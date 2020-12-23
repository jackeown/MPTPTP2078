%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:02 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  162 (16641 expanded)
%              Number of clauses        :   93 (4101 expanded)
%              Number of leaves         :   24 (4903 expanded)
%              Depth                    :   36
%              Number of atoms          :  326 (17150 expanded)
%              Number of equality atoms :  254 (17056 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f23,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f23])).

fof(f29,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f24])).

fof(f37,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f37])).

fof(f69,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f52,f47])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f71])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f72])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f73])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f74])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f61,f75])).

fof(f92,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f69,f70,f76])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f77,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f43,f47])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f30])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f14])).

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
    inference(nnf_transformation,[],[f28])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f54,f74])).

fof(f97,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f89])).

fof(f98,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f97])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f74])).

fof(f99,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f90])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1007,negated_conjecture,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_21,c_10,c_2])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1208,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1007,c_0])).

cnf(c_1955,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1208,c_10])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1573,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_2])).

cnf(c_1965,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1955,c_1573])).

cnf(c_2120,plain,
    ( k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11,c_1965])).

cnf(c_2125,plain,
    ( k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_2120,c_8])).

cnf(c_2619,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(superposition,[status(thm)],[c_2125,c_0])).

cnf(c_2622,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_2619,c_2125])).

cnf(c_2128,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_2125,c_1965])).

cnf(c_2296,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2128,c_10])).

cnf(c_2494,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11,c_2296])).

cnf(c_2520,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = sK3 ),
    inference(demodulation,[status(thm)],[c_2494,c_8])).

cnf(c_2978,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),X0) = sK3 ),
    inference(superposition,[status(thm)],[c_2128,c_2520])).

cnf(c_3077,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_2978,c_10])).

cnf(c_2490,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_2296])).

cnf(c_3382,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(sK3,X0))) = sK3 ),
    inference(superposition,[status(thm)],[c_2490,c_2978])).

cnf(c_5110,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(sK3,k5_xboole_0(sK3,X1)))) = sK3 ),
    inference(superposition,[status(thm)],[c_3077,c_3382])).

cnf(c_5175,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),X1)) = sK3 ),
    inference(demodulation,[status(thm)],[c_5110,c_2128])).

cnf(c_5263,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X1)),sK3) ),
    inference(superposition,[status(thm)],[c_5175,c_3077])).

cnf(c_5291,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(X1,sK3) ),
    inference(demodulation,[status(thm)],[c_5263,c_2128])).

cnf(c_6720,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X1,sK3) ),
    inference(superposition,[status(thm)],[c_5291,c_2490])).

cnf(c_8153,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,sK3) ),
    inference(superposition,[status(thm)],[c_2128,c_6720])).

cnf(c_6713,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(sK3,k5_xboole_0(X1,sK3)) ),
    inference(superposition,[status(thm)],[c_5291,c_2128])).

cnf(c_2290,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,sK3)) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_2128])).

cnf(c_6724,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(demodulation,[status(thm)],[c_6713,c_2290])).

cnf(c_6799,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_6724])).

cnf(c_8474,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X1,X0)) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_8153,c_6799])).

cnf(c_10753,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),sK3),k5_xboole_0(sK3,X1)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_3077,c_8474])).

cnf(c_6679,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,X1))) = k5_xboole_0(k5_xboole_0(X1,X0),sK3) ),
    inference(superposition,[status(thm)],[c_3077,c_5291])).

cnf(c_6765,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sK3) = k5_xboole_0(X1,k5_xboole_0(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_6679,c_2296])).

cnf(c_10852,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(sK3,X0)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_10753,c_2128,c_6765])).

cnf(c_11361,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(sK3,X0)) = k5_xboole_0(k5_xboole_0(sK3,sK3),X1) ),
    inference(superposition,[status(thm)],[c_6720,c_10852])).

cnf(c_2310,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,sK3))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_10,c_2290])).

cnf(c_1221,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_2])).

cnf(c_9140,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(sK3,X2)) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2310,c_1221])).

cnf(c_10787,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,sK3),X2)) = k5_xboole_0(X2,k5_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_8474,c_1221])).

cnf(c_6838,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_6724,c_10])).

cnf(c_9156,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_6838,c_1221])).

cnf(c_9236,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_1221,c_2296])).

cnf(c_2756,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_2310,c_10])).

cnf(c_2761,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_2756,c_10])).

cnf(c_9284,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_9236,c_2761])).

cnf(c_8449,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),X1) = k5_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_6724,c_8153])).

cnf(c_10146,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,sK3),X2) ),
    inference(superposition,[status(thm)],[c_8449,c_10])).

cnf(c_1220,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_10,c_2])).

cnf(c_6717,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,sK3),X1),X0) = k5_xboole_0(X1,sK3) ),
    inference(superposition,[status(thm)],[c_5291,c_2310])).

cnf(c_8823,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,sK3),X2)),X1) = k5_xboole_0(k5_xboole_0(X0,X2),sK3) ),
    inference(superposition,[status(thm)],[c_1220,c_6717])).

cnf(c_8828,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))) = k5_xboole_0(k5_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_1220,c_2490])).

cnf(c_3358,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10,c_2490])).

cnf(c_8850,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_8828,c_3358])).

cnf(c_8874,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,k5_xboole_0(sK3,X2)) ),
    inference(demodulation,[status(thm)],[c_8823,c_8850])).

cnf(c_10196,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,X1)) = k5_xboole_0(k5_xboole_0(X0,sK3),X1) ),
    inference(light_normalisation,[status(thm)],[c_10146,c_8874])).

cnf(c_10821,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),X1) = k5_xboole_0(X0,k5_xboole_0(sK3,X1)) ),
    inference(demodulation,[status(thm)],[c_10787,c_9156,c_9284,c_10196])).

cnf(c_11463,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(sK3,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_11361,c_2128,c_9140,c_10821])).

cnf(c_19145,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_2622,c_11463])).

cnf(c_3071,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = sK3 ),
    inference(superposition,[status(thm)],[c_2296,c_2978])).

cnf(c_3847,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_3071,c_2310])).

cnf(c_3849,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(sK3,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3847,c_11])).

cnf(c_19152,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_19145,c_3849])).

cnf(c_1011,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2177,plain,
    ( X0 != X1
    | k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)) != X1
    | k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)) = X0 ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_3633,plain,
    ( X0 != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = X0
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) ),
    inference(instantiation,[status(thm)],[c_2177])).

cnf(c_4715,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)
    | k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0)) != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) ),
    inference(instantiation,[status(thm)],[c_3633])).

cnf(c_4716,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) ),
    inference(instantiation,[status(thm)],[c_4715])).

cnf(c_1463,plain,
    ( X0 != X1
    | X0 = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != X1 ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_1751,plain,
    ( X0 = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | X0 != k1_xboole_0
    | k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1463])).

cnf(c_4510,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != k1_xboole_0
    | k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1751])).

cnf(c_4511,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0
    | k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4510])).

cnf(c_2378,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0
    | k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1751])).

cnf(c_2380,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0
    | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2378])).

cnf(c_1015,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1237,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0)))
    | X2 != X0
    | k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0)) != X1 ),
    inference(instantiation,[status(thm)],[c_1015])).

cnf(c_1258,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
    | r2_hidden(X3,k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)))
    | X3 != X0
    | k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_1260,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1258])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_184,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_9])).

cnf(c_185,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ),
    inference(unflattening,[status(thm)],[c_184])).

cnf(c_187,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_48,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_18,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_27,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_24,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19152,c_4716,c_4511,c_2380,c_1260,c_1007,c_187,c_48,c_27,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:04:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.65/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/1.47  
% 7.65/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.65/1.47  
% 7.65/1.47  ------  iProver source info
% 7.65/1.47  
% 7.65/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.65/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.65/1.47  git: non_committed_changes: false
% 7.65/1.47  git: last_make_outside_of_git: false
% 7.65/1.47  
% 7.65/1.47  ------ 
% 7.65/1.47  
% 7.65/1.47  ------ Input Options
% 7.65/1.47  
% 7.65/1.47  --out_options                           all
% 7.65/1.47  --tptp_safe_out                         true
% 7.65/1.47  --problem_path                          ""
% 7.65/1.47  --include_path                          ""
% 7.65/1.47  --clausifier                            res/vclausify_rel
% 7.65/1.47  --clausifier_options                    ""
% 7.65/1.47  --stdin                                 false
% 7.65/1.47  --stats_out                             all
% 7.65/1.47  
% 7.65/1.47  ------ General Options
% 7.65/1.47  
% 7.65/1.47  --fof                                   false
% 7.65/1.47  --time_out_real                         305.
% 7.65/1.47  --time_out_virtual                      -1.
% 7.65/1.47  --symbol_type_check                     false
% 7.65/1.47  --clausify_out                          false
% 7.65/1.47  --sig_cnt_out                           false
% 7.65/1.47  --trig_cnt_out                          false
% 7.65/1.47  --trig_cnt_out_tolerance                1.
% 7.65/1.47  --trig_cnt_out_sk_spl                   false
% 7.65/1.47  --abstr_cl_out                          false
% 7.65/1.47  
% 7.65/1.47  ------ Global Options
% 7.65/1.47  
% 7.65/1.47  --schedule                              default
% 7.65/1.47  --add_important_lit                     false
% 7.65/1.47  --prop_solver_per_cl                    1000
% 7.65/1.47  --min_unsat_core                        false
% 7.65/1.47  --soft_assumptions                      false
% 7.65/1.47  --soft_lemma_size                       3
% 7.65/1.47  --prop_impl_unit_size                   0
% 7.65/1.47  --prop_impl_unit                        []
% 7.65/1.47  --share_sel_clauses                     true
% 7.65/1.47  --reset_solvers                         false
% 7.65/1.47  --bc_imp_inh                            [conj_cone]
% 7.65/1.47  --conj_cone_tolerance                   3.
% 7.65/1.47  --extra_neg_conj                        none
% 7.65/1.47  --large_theory_mode                     true
% 7.65/1.47  --prolific_symb_bound                   200
% 7.65/1.47  --lt_threshold                          2000
% 7.65/1.47  --clause_weak_htbl                      true
% 7.65/1.47  --gc_record_bc_elim                     false
% 7.65/1.47  
% 7.65/1.47  ------ Preprocessing Options
% 7.65/1.47  
% 7.65/1.47  --preprocessing_flag                    true
% 7.65/1.47  --time_out_prep_mult                    0.1
% 7.65/1.47  --splitting_mode                        input
% 7.65/1.47  --splitting_grd                         true
% 7.65/1.47  --splitting_cvd                         false
% 7.65/1.47  --splitting_cvd_svl                     false
% 7.65/1.47  --splitting_nvd                         32
% 7.65/1.47  --sub_typing                            true
% 7.65/1.47  --prep_gs_sim                           true
% 7.65/1.47  --prep_unflatten                        true
% 7.65/1.47  --prep_res_sim                          true
% 7.65/1.47  --prep_upred                            true
% 7.65/1.47  --prep_sem_filter                       exhaustive
% 7.65/1.47  --prep_sem_filter_out                   false
% 7.65/1.47  --pred_elim                             true
% 7.65/1.47  --res_sim_input                         true
% 7.65/1.47  --eq_ax_congr_red                       true
% 7.65/1.47  --pure_diseq_elim                       true
% 7.65/1.47  --brand_transform                       false
% 7.65/1.47  --non_eq_to_eq                          false
% 7.65/1.47  --prep_def_merge                        true
% 7.65/1.47  --prep_def_merge_prop_impl              false
% 7.65/1.47  --prep_def_merge_mbd                    true
% 7.65/1.47  --prep_def_merge_tr_red                 false
% 7.65/1.47  --prep_def_merge_tr_cl                  false
% 7.65/1.47  --smt_preprocessing                     true
% 7.65/1.47  --smt_ac_axioms                         fast
% 7.65/1.47  --preprocessed_out                      false
% 7.65/1.47  --preprocessed_stats                    false
% 7.65/1.47  
% 7.65/1.47  ------ Abstraction refinement Options
% 7.65/1.47  
% 7.65/1.47  --abstr_ref                             []
% 7.65/1.47  --abstr_ref_prep                        false
% 7.65/1.47  --abstr_ref_until_sat                   false
% 7.65/1.47  --abstr_ref_sig_restrict                funpre
% 7.65/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.47  --abstr_ref_under                       []
% 7.65/1.47  
% 7.65/1.47  ------ SAT Options
% 7.65/1.47  
% 7.65/1.47  --sat_mode                              false
% 7.65/1.47  --sat_fm_restart_options                ""
% 7.65/1.47  --sat_gr_def                            false
% 7.65/1.47  --sat_epr_types                         true
% 7.65/1.47  --sat_non_cyclic_types                  false
% 7.65/1.47  --sat_finite_models                     false
% 7.65/1.47  --sat_fm_lemmas                         false
% 7.65/1.47  --sat_fm_prep                           false
% 7.65/1.47  --sat_fm_uc_incr                        true
% 7.65/1.47  --sat_out_model                         small
% 7.65/1.47  --sat_out_clauses                       false
% 7.65/1.47  
% 7.65/1.47  ------ QBF Options
% 7.65/1.47  
% 7.65/1.47  --qbf_mode                              false
% 7.65/1.47  --qbf_elim_univ                         false
% 7.65/1.47  --qbf_dom_inst                          none
% 7.65/1.47  --qbf_dom_pre_inst                      false
% 7.65/1.47  --qbf_sk_in                             false
% 7.65/1.47  --qbf_pred_elim                         true
% 7.65/1.47  --qbf_split                             512
% 7.65/1.47  
% 7.65/1.47  ------ BMC1 Options
% 7.65/1.47  
% 7.65/1.47  --bmc1_incremental                      false
% 7.65/1.47  --bmc1_axioms                           reachable_all
% 7.65/1.47  --bmc1_min_bound                        0
% 7.65/1.47  --bmc1_max_bound                        -1
% 7.65/1.47  --bmc1_max_bound_default                -1
% 7.65/1.47  --bmc1_symbol_reachability              true
% 7.65/1.47  --bmc1_property_lemmas                  false
% 7.65/1.47  --bmc1_k_induction                      false
% 7.65/1.47  --bmc1_non_equiv_states                 false
% 7.65/1.47  --bmc1_deadlock                         false
% 7.65/1.47  --bmc1_ucm                              false
% 7.65/1.47  --bmc1_add_unsat_core                   none
% 7.65/1.47  --bmc1_unsat_core_children              false
% 7.65/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.47  --bmc1_out_stat                         full
% 7.65/1.47  --bmc1_ground_init                      false
% 7.65/1.47  --bmc1_pre_inst_next_state              false
% 7.65/1.47  --bmc1_pre_inst_state                   false
% 7.65/1.47  --bmc1_pre_inst_reach_state             false
% 7.65/1.47  --bmc1_out_unsat_core                   false
% 7.65/1.47  --bmc1_aig_witness_out                  false
% 7.65/1.47  --bmc1_verbose                          false
% 7.65/1.47  --bmc1_dump_clauses_tptp                false
% 7.65/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.47  --bmc1_dump_file                        -
% 7.65/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.47  --bmc1_ucm_extend_mode                  1
% 7.65/1.47  --bmc1_ucm_init_mode                    2
% 7.65/1.47  --bmc1_ucm_cone_mode                    none
% 7.65/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.47  --bmc1_ucm_relax_model                  4
% 7.65/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.47  --bmc1_ucm_layered_model                none
% 7.65/1.47  --bmc1_ucm_max_lemma_size               10
% 7.65/1.47  
% 7.65/1.47  ------ AIG Options
% 7.65/1.47  
% 7.65/1.47  --aig_mode                              false
% 7.65/1.47  
% 7.65/1.47  ------ Instantiation Options
% 7.65/1.47  
% 7.65/1.47  --instantiation_flag                    true
% 7.65/1.47  --inst_sos_flag                         true
% 7.65/1.47  --inst_sos_phase                        true
% 7.65/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.47  --inst_lit_sel_side                     num_symb
% 7.65/1.47  --inst_solver_per_active                1400
% 7.65/1.47  --inst_solver_calls_frac                1.
% 7.65/1.47  --inst_passive_queue_type               priority_queues
% 7.65/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.47  --inst_passive_queues_freq              [25;2]
% 7.65/1.47  --inst_dismatching                      true
% 7.65/1.47  --inst_eager_unprocessed_to_passive     true
% 7.65/1.47  --inst_prop_sim_given                   true
% 7.65/1.47  --inst_prop_sim_new                     false
% 7.65/1.47  --inst_subs_new                         false
% 7.65/1.47  --inst_eq_res_simp                      false
% 7.65/1.47  --inst_subs_given                       false
% 7.65/1.47  --inst_orphan_elimination               true
% 7.65/1.47  --inst_learning_loop_flag               true
% 7.65/1.47  --inst_learning_start                   3000
% 7.65/1.47  --inst_learning_factor                  2
% 7.65/1.47  --inst_start_prop_sim_after_learn       3
% 7.65/1.47  --inst_sel_renew                        solver
% 7.65/1.47  --inst_lit_activity_flag                true
% 7.65/1.47  --inst_restr_to_given                   false
% 7.65/1.47  --inst_activity_threshold               500
% 7.65/1.47  --inst_out_proof                        true
% 7.65/1.47  
% 7.65/1.47  ------ Resolution Options
% 7.65/1.47  
% 7.65/1.47  --resolution_flag                       true
% 7.65/1.47  --res_lit_sel                           adaptive
% 7.65/1.47  --res_lit_sel_side                      none
% 7.65/1.47  --res_ordering                          kbo
% 7.65/1.47  --res_to_prop_solver                    active
% 7.65/1.47  --res_prop_simpl_new                    false
% 7.65/1.47  --res_prop_simpl_given                  true
% 7.65/1.47  --res_passive_queue_type                priority_queues
% 7.65/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.47  --res_passive_queues_freq               [15;5]
% 7.65/1.47  --res_forward_subs                      full
% 7.65/1.47  --res_backward_subs                     full
% 7.65/1.47  --res_forward_subs_resolution           true
% 7.65/1.47  --res_backward_subs_resolution          true
% 7.65/1.47  --res_orphan_elimination                true
% 7.65/1.47  --res_time_limit                        2.
% 7.65/1.47  --res_out_proof                         true
% 7.65/1.47  
% 7.65/1.47  ------ Superposition Options
% 7.65/1.47  
% 7.65/1.47  --superposition_flag                    true
% 7.65/1.47  --sup_passive_queue_type                priority_queues
% 7.65/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.47  --demod_completeness_check              fast
% 7.65/1.47  --demod_use_ground                      true
% 7.65/1.47  --sup_to_prop_solver                    passive
% 7.65/1.47  --sup_prop_simpl_new                    true
% 7.65/1.47  --sup_prop_simpl_given                  true
% 7.65/1.47  --sup_fun_splitting                     true
% 7.65/1.47  --sup_smt_interval                      50000
% 7.65/1.47  
% 7.65/1.47  ------ Superposition Simplification Setup
% 7.65/1.47  
% 7.65/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.65/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.65/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.65/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.65/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.65/1.47  --sup_immed_triv                        [TrivRules]
% 7.65/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.47  --sup_immed_bw_main                     []
% 7.65/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.65/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.48  --sup_input_bw                          []
% 7.65/1.48  
% 7.65/1.48  ------ Combination Options
% 7.65/1.48  
% 7.65/1.48  --comb_res_mult                         3
% 7.65/1.48  --comb_sup_mult                         2
% 7.65/1.48  --comb_inst_mult                        10
% 7.65/1.48  
% 7.65/1.48  ------ Debug Options
% 7.65/1.48  
% 7.65/1.48  --dbg_backtrace                         false
% 7.65/1.48  --dbg_dump_prop_clauses                 false
% 7.65/1.48  --dbg_dump_prop_clauses_file            -
% 7.65/1.48  --dbg_out_stat                          false
% 7.65/1.48  ------ Parsing...
% 7.65/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.65/1.48  
% 7.65/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.65/1.48  
% 7.65/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.65/1.48  
% 7.65/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.48  ------ Proving...
% 7.65/1.48  ------ Problem Properties 
% 7.65/1.48  
% 7.65/1.48  
% 7.65/1.48  clauses                                 21
% 7.65/1.48  conjectures                             1
% 7.65/1.48  EPR                                     1
% 7.65/1.48  Horn                                    18
% 7.65/1.48  unary                                   14
% 7.65/1.48  binary                                  2
% 7.65/1.48  lits                                    36
% 7.65/1.48  lits eq                                 23
% 7.65/1.48  fd_pure                                 0
% 7.65/1.48  fd_pseudo                               0
% 7.65/1.48  fd_cond                                 0
% 7.65/1.48  fd_pseudo_cond                          4
% 7.65/1.48  AC symbols                              1
% 7.65/1.48  
% 7.65/1.48  ------ Schedule dynamic 5 is on 
% 7.65/1.48  
% 7.65/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.65/1.48  
% 7.65/1.48  
% 7.65/1.48  ------ 
% 7.65/1.48  Current options:
% 7.65/1.48  ------ 
% 7.65/1.48  
% 7.65/1.48  ------ Input Options
% 7.65/1.48  
% 7.65/1.48  --out_options                           all
% 7.65/1.48  --tptp_safe_out                         true
% 7.65/1.48  --problem_path                          ""
% 7.65/1.48  --include_path                          ""
% 7.65/1.48  --clausifier                            res/vclausify_rel
% 7.65/1.48  --clausifier_options                    ""
% 7.65/1.48  --stdin                                 false
% 7.65/1.48  --stats_out                             all
% 7.65/1.48  
% 7.65/1.48  ------ General Options
% 7.65/1.48  
% 7.65/1.48  --fof                                   false
% 7.65/1.48  --time_out_real                         305.
% 7.65/1.48  --time_out_virtual                      -1.
% 7.65/1.48  --symbol_type_check                     false
% 7.65/1.48  --clausify_out                          false
% 7.65/1.48  --sig_cnt_out                           false
% 7.65/1.48  --trig_cnt_out                          false
% 7.65/1.48  --trig_cnt_out_tolerance                1.
% 7.65/1.48  --trig_cnt_out_sk_spl                   false
% 7.65/1.48  --abstr_cl_out                          false
% 7.65/1.48  
% 7.65/1.48  ------ Global Options
% 7.65/1.48  
% 7.65/1.48  --schedule                              default
% 7.65/1.48  --add_important_lit                     false
% 7.65/1.48  --prop_solver_per_cl                    1000
% 7.65/1.48  --min_unsat_core                        false
% 7.65/1.48  --soft_assumptions                      false
% 7.65/1.48  --soft_lemma_size                       3
% 7.65/1.48  --prop_impl_unit_size                   0
% 7.65/1.48  --prop_impl_unit                        []
% 7.65/1.48  --share_sel_clauses                     true
% 7.65/1.48  --reset_solvers                         false
% 7.65/1.48  --bc_imp_inh                            [conj_cone]
% 7.65/1.48  --conj_cone_tolerance                   3.
% 7.65/1.48  --extra_neg_conj                        none
% 7.65/1.48  --large_theory_mode                     true
% 7.65/1.48  --prolific_symb_bound                   200
% 7.65/1.48  --lt_threshold                          2000
% 7.65/1.48  --clause_weak_htbl                      true
% 7.65/1.48  --gc_record_bc_elim                     false
% 7.65/1.48  
% 7.65/1.48  ------ Preprocessing Options
% 7.65/1.48  
% 7.65/1.48  --preprocessing_flag                    true
% 7.65/1.48  --time_out_prep_mult                    0.1
% 7.65/1.48  --splitting_mode                        input
% 7.65/1.48  --splitting_grd                         true
% 7.65/1.48  --splitting_cvd                         false
% 7.65/1.48  --splitting_cvd_svl                     false
% 7.65/1.48  --splitting_nvd                         32
% 7.65/1.48  --sub_typing                            true
% 7.65/1.48  --prep_gs_sim                           true
% 7.65/1.48  --prep_unflatten                        true
% 7.65/1.48  --prep_res_sim                          true
% 7.65/1.48  --prep_upred                            true
% 7.65/1.48  --prep_sem_filter                       exhaustive
% 7.65/1.48  --prep_sem_filter_out                   false
% 7.65/1.48  --pred_elim                             true
% 7.65/1.48  --res_sim_input                         true
% 7.65/1.48  --eq_ax_congr_red                       true
% 7.65/1.48  --pure_diseq_elim                       true
% 7.65/1.48  --brand_transform                       false
% 7.65/1.48  --non_eq_to_eq                          false
% 7.65/1.48  --prep_def_merge                        true
% 7.65/1.48  --prep_def_merge_prop_impl              false
% 7.65/1.48  --prep_def_merge_mbd                    true
% 7.65/1.48  --prep_def_merge_tr_red                 false
% 7.65/1.48  --prep_def_merge_tr_cl                  false
% 7.65/1.48  --smt_preprocessing                     true
% 7.65/1.48  --smt_ac_axioms                         fast
% 7.65/1.48  --preprocessed_out                      false
% 7.65/1.48  --preprocessed_stats                    false
% 7.65/1.48  
% 7.65/1.48  ------ Abstraction refinement Options
% 7.65/1.48  
% 7.65/1.48  --abstr_ref                             []
% 7.65/1.48  --abstr_ref_prep                        false
% 7.65/1.48  --abstr_ref_until_sat                   false
% 7.65/1.48  --abstr_ref_sig_restrict                funpre
% 7.65/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.48  --abstr_ref_under                       []
% 7.65/1.48  
% 7.65/1.48  ------ SAT Options
% 7.65/1.48  
% 7.65/1.48  --sat_mode                              false
% 7.65/1.48  --sat_fm_restart_options                ""
% 7.65/1.48  --sat_gr_def                            false
% 7.65/1.48  --sat_epr_types                         true
% 7.65/1.48  --sat_non_cyclic_types                  false
% 7.65/1.48  --sat_finite_models                     false
% 7.65/1.48  --sat_fm_lemmas                         false
% 7.65/1.48  --sat_fm_prep                           false
% 7.65/1.48  --sat_fm_uc_incr                        true
% 7.65/1.48  --sat_out_model                         small
% 7.65/1.48  --sat_out_clauses                       false
% 7.65/1.48  
% 7.65/1.48  ------ QBF Options
% 7.65/1.48  
% 7.65/1.48  --qbf_mode                              false
% 7.65/1.48  --qbf_elim_univ                         false
% 7.65/1.48  --qbf_dom_inst                          none
% 7.65/1.48  --qbf_dom_pre_inst                      false
% 7.65/1.48  --qbf_sk_in                             false
% 7.65/1.48  --qbf_pred_elim                         true
% 7.65/1.48  --qbf_split                             512
% 7.65/1.48  
% 7.65/1.48  ------ BMC1 Options
% 7.65/1.48  
% 7.65/1.48  --bmc1_incremental                      false
% 7.65/1.48  --bmc1_axioms                           reachable_all
% 7.65/1.48  --bmc1_min_bound                        0
% 7.65/1.48  --bmc1_max_bound                        -1
% 7.65/1.48  --bmc1_max_bound_default                -1
% 7.65/1.48  --bmc1_symbol_reachability              true
% 7.65/1.48  --bmc1_property_lemmas                  false
% 7.65/1.48  --bmc1_k_induction                      false
% 7.65/1.48  --bmc1_non_equiv_states                 false
% 7.65/1.48  --bmc1_deadlock                         false
% 7.65/1.48  --bmc1_ucm                              false
% 7.65/1.48  --bmc1_add_unsat_core                   none
% 7.65/1.48  --bmc1_unsat_core_children              false
% 7.65/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.48  --bmc1_out_stat                         full
% 7.65/1.48  --bmc1_ground_init                      false
% 7.65/1.48  --bmc1_pre_inst_next_state              false
% 7.65/1.48  --bmc1_pre_inst_state                   false
% 7.65/1.48  --bmc1_pre_inst_reach_state             false
% 7.65/1.48  --bmc1_out_unsat_core                   false
% 7.65/1.48  --bmc1_aig_witness_out                  false
% 7.65/1.48  --bmc1_verbose                          false
% 7.65/1.48  --bmc1_dump_clauses_tptp                false
% 7.65/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.48  --bmc1_dump_file                        -
% 7.65/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.48  --bmc1_ucm_extend_mode                  1
% 7.65/1.48  --bmc1_ucm_init_mode                    2
% 7.65/1.48  --bmc1_ucm_cone_mode                    none
% 7.65/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.48  --bmc1_ucm_relax_model                  4
% 7.65/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.48  --bmc1_ucm_layered_model                none
% 7.65/1.48  --bmc1_ucm_max_lemma_size               10
% 7.65/1.48  
% 7.65/1.48  ------ AIG Options
% 7.65/1.48  
% 7.65/1.48  --aig_mode                              false
% 7.65/1.48  
% 7.65/1.48  ------ Instantiation Options
% 7.65/1.48  
% 7.65/1.48  --instantiation_flag                    true
% 7.65/1.48  --inst_sos_flag                         true
% 7.65/1.48  --inst_sos_phase                        true
% 7.65/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.48  --inst_lit_sel_side                     none
% 7.65/1.48  --inst_solver_per_active                1400
% 7.65/1.48  --inst_solver_calls_frac                1.
% 7.65/1.48  --inst_passive_queue_type               priority_queues
% 7.65/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.48  --inst_passive_queues_freq              [25;2]
% 7.65/1.48  --inst_dismatching                      true
% 7.65/1.48  --inst_eager_unprocessed_to_passive     true
% 7.65/1.48  --inst_prop_sim_given                   true
% 7.65/1.48  --inst_prop_sim_new                     false
% 7.65/1.48  --inst_subs_new                         false
% 7.65/1.48  --inst_eq_res_simp                      false
% 7.65/1.48  --inst_subs_given                       false
% 7.65/1.48  --inst_orphan_elimination               true
% 7.65/1.48  --inst_learning_loop_flag               true
% 7.65/1.48  --inst_learning_start                   3000
% 7.65/1.48  --inst_learning_factor                  2
% 7.65/1.48  --inst_start_prop_sim_after_learn       3
% 7.65/1.48  --inst_sel_renew                        solver
% 7.65/1.48  --inst_lit_activity_flag                true
% 7.65/1.48  --inst_restr_to_given                   false
% 7.65/1.48  --inst_activity_threshold               500
% 7.65/1.48  --inst_out_proof                        true
% 7.65/1.48  
% 7.65/1.48  ------ Resolution Options
% 7.65/1.48  
% 7.65/1.48  --resolution_flag                       false
% 7.65/1.48  --res_lit_sel                           adaptive
% 7.65/1.48  --res_lit_sel_side                      none
% 7.65/1.48  --res_ordering                          kbo
% 7.65/1.48  --res_to_prop_solver                    active
% 7.65/1.48  --res_prop_simpl_new                    false
% 7.65/1.48  --res_prop_simpl_given                  true
% 7.65/1.48  --res_passive_queue_type                priority_queues
% 7.65/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.48  --res_passive_queues_freq               [15;5]
% 7.65/1.48  --res_forward_subs                      full
% 7.65/1.48  --res_backward_subs                     full
% 7.65/1.48  --res_forward_subs_resolution           true
% 7.65/1.48  --res_backward_subs_resolution          true
% 7.65/1.48  --res_orphan_elimination                true
% 7.65/1.48  --res_time_limit                        2.
% 7.65/1.48  --res_out_proof                         true
% 7.65/1.48  
% 7.65/1.48  ------ Superposition Options
% 7.65/1.48  
% 7.65/1.48  --superposition_flag                    true
% 7.65/1.48  --sup_passive_queue_type                priority_queues
% 7.65/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.48  --demod_completeness_check              fast
% 7.65/1.48  --demod_use_ground                      true
% 7.65/1.48  --sup_to_prop_solver                    passive
% 7.65/1.48  --sup_prop_simpl_new                    true
% 7.65/1.48  --sup_prop_simpl_given                  true
% 7.65/1.48  --sup_fun_splitting                     true
% 7.65/1.48  --sup_smt_interval                      50000
% 7.65/1.48  
% 7.65/1.48  ------ Superposition Simplification Setup
% 7.65/1.48  
% 7.65/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.65/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.65/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.65/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.65/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.65/1.48  --sup_immed_triv                        [TrivRules]
% 7.65/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.48  --sup_immed_bw_main                     []
% 7.65/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.65/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.48  --sup_input_bw                          []
% 7.65/1.48  
% 7.65/1.48  ------ Combination Options
% 7.65/1.48  
% 7.65/1.48  --comb_res_mult                         3
% 7.65/1.48  --comb_sup_mult                         2
% 7.65/1.48  --comb_inst_mult                        10
% 7.65/1.48  
% 7.65/1.48  ------ Debug Options
% 7.65/1.48  
% 7.65/1.48  --dbg_backtrace                         false
% 7.65/1.48  --dbg_dump_prop_clauses                 false
% 7.65/1.48  --dbg_dump_prop_clauses_file            -
% 7.65/1.48  --dbg_out_stat                          false
% 7.65/1.48  
% 7.65/1.48  
% 7.65/1.48  
% 7.65/1.48  
% 7.65/1.48  ------ Proving...
% 7.65/1.48  
% 7.65/1.48  
% 7.65/1.48  % SZS status Theorem for theBenchmark.p
% 7.65/1.48  
% 7.65/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.65/1.48  
% 7.65/1.48  fof(f12,axiom,(
% 7.65/1.48    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f51,plain,(
% 7.65/1.48    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.65/1.48    inference(cnf_transformation,[],[f12])).
% 7.65/1.48  
% 7.65/1.48  fof(f23,conjecture,(
% 7.65/1.48    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f24,negated_conjecture,(
% 7.65/1.48    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 7.65/1.48    inference(negated_conjecture,[],[f23])).
% 7.65/1.48  
% 7.65/1.48  fof(f29,plain,(
% 7.65/1.48    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 7.65/1.48    inference(ennf_transformation,[],[f24])).
% 7.65/1.48  
% 7.65/1.48  fof(f37,plain,(
% 7.65/1.48    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 7.65/1.48    introduced(choice_axiom,[])).
% 7.65/1.48  
% 7.65/1.48  fof(f38,plain,(
% 7.65/1.48    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 7.65/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f37])).
% 7.65/1.48  
% 7.65/1.48  fof(f69,plain,(
% 7.65/1.48    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 7.65/1.48    inference(cnf_transformation,[],[f38])).
% 7.65/1.48  
% 7.65/1.48  fof(f13,axiom,(
% 7.65/1.48    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f52,plain,(
% 7.65/1.48    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f13])).
% 7.65/1.48  
% 7.65/1.48  fof(f8,axiom,(
% 7.65/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f47,plain,(
% 7.65/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.65/1.48    inference(cnf_transformation,[],[f8])).
% 7.65/1.48  
% 7.65/1.48  fof(f70,plain,(
% 7.65/1.48    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1)) )),
% 7.65/1.48    inference(definition_unfolding,[],[f52,f47])).
% 7.65/1.48  
% 7.65/1.48  fof(f15,axiom,(
% 7.65/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f61,plain,(
% 7.65/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f15])).
% 7.65/1.48  
% 7.65/1.48  fof(f16,axiom,(
% 7.65/1.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f62,plain,(
% 7.65/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f16])).
% 7.65/1.48  
% 7.65/1.48  fof(f17,axiom,(
% 7.65/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f63,plain,(
% 7.65/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f17])).
% 7.65/1.48  
% 7.65/1.48  fof(f18,axiom,(
% 7.65/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f64,plain,(
% 7.65/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f18])).
% 7.65/1.48  
% 7.65/1.48  fof(f19,axiom,(
% 7.65/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f65,plain,(
% 7.65/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f19])).
% 7.65/1.48  
% 7.65/1.48  fof(f20,axiom,(
% 7.65/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f66,plain,(
% 7.65/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f20])).
% 7.65/1.48  
% 7.65/1.48  fof(f21,axiom,(
% 7.65/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f67,plain,(
% 7.65/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f21])).
% 7.65/1.48  
% 7.65/1.48  fof(f71,plain,(
% 7.65/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.65/1.48    inference(definition_unfolding,[],[f66,f67])).
% 7.65/1.48  
% 7.65/1.48  fof(f72,plain,(
% 7.65/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.65/1.48    inference(definition_unfolding,[],[f65,f71])).
% 7.65/1.48  
% 7.65/1.48  fof(f73,plain,(
% 7.65/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.65/1.48    inference(definition_unfolding,[],[f64,f72])).
% 7.65/1.48  
% 7.65/1.48  fof(f74,plain,(
% 7.65/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.65/1.48    inference(definition_unfolding,[],[f63,f73])).
% 7.65/1.48  
% 7.65/1.48  fof(f75,plain,(
% 7.65/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.65/1.48    inference(definition_unfolding,[],[f62,f74])).
% 7.65/1.48  
% 7.65/1.48  fof(f76,plain,(
% 7.65/1.48    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.65/1.48    inference(definition_unfolding,[],[f61,f75])).
% 7.65/1.48  
% 7.65/1.48  fof(f92,plain,(
% 7.65/1.48    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0),
% 7.65/1.48    inference(definition_unfolding,[],[f69,f70,f76])).
% 7.65/1.48  
% 7.65/1.48  fof(f11,axiom,(
% 7.65/1.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f50,plain,(
% 7.65/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f11])).
% 7.65/1.48  
% 7.65/1.48  fof(f2,axiom,(
% 7.65/1.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f40,plain,(
% 7.65/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f2])).
% 7.65/1.48  
% 7.65/1.48  fof(f4,axiom,(
% 7.65/1.48    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f43,plain,(
% 7.65/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f4])).
% 7.65/1.48  
% 7.65/1.48  fof(f77,plain,(
% 7.65/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1)) )),
% 7.65/1.48    inference(definition_unfolding,[],[f43,f47])).
% 7.65/1.48  
% 7.65/1.48  fof(f9,axiom,(
% 7.65/1.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f48,plain,(
% 7.65/1.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.65/1.48    inference(cnf_transformation,[],[f9])).
% 7.65/1.48  
% 7.65/1.48  fof(f3,axiom,(
% 7.65/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f25,plain,(
% 7.65/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.65/1.48    inference(rectify,[],[f3])).
% 7.65/1.48  
% 7.65/1.48  fof(f26,plain,(
% 7.65/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.65/1.48    inference(ennf_transformation,[],[f25])).
% 7.65/1.48  
% 7.65/1.48  fof(f30,plain,(
% 7.65/1.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.65/1.48    introduced(choice_axiom,[])).
% 7.65/1.48  
% 7.65/1.48  fof(f31,plain,(
% 7.65/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.65/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f30])).
% 7.65/1.48  
% 7.65/1.48  fof(f42,plain,(
% 7.65/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.65/1.48    inference(cnf_transformation,[],[f31])).
% 7.65/1.48  
% 7.65/1.48  fof(f79,plain,(
% 7.65/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.65/1.48    inference(definition_unfolding,[],[f42,f47])).
% 7.65/1.48  
% 7.65/1.48  fof(f10,axiom,(
% 7.65/1.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f49,plain,(
% 7.65/1.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f10])).
% 7.65/1.48  
% 7.65/1.48  fof(f6,axiom,(
% 7.65/1.48    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f45,plain,(
% 7.65/1.48    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.65/1.48    inference(cnf_transformation,[],[f6])).
% 7.65/1.48  
% 7.65/1.48  fof(f82,plain,(
% 7.65/1.48    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 7.65/1.48    inference(definition_unfolding,[],[f45,f47])).
% 7.65/1.48  
% 7.65/1.48  fof(f14,axiom,(
% 7.65/1.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.65/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f28,plain,(
% 7.65/1.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.65/1.48    inference(ennf_transformation,[],[f14])).
% 7.65/1.48  
% 7.65/1.48  fof(f32,plain,(
% 7.65/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.65/1.48    inference(nnf_transformation,[],[f28])).
% 7.65/1.48  
% 7.65/1.48  fof(f33,plain,(
% 7.65/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.65/1.48    inference(flattening,[],[f32])).
% 7.65/1.48  
% 7.65/1.48  fof(f34,plain,(
% 7.65/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.65/1.48    inference(rectify,[],[f33])).
% 7.65/1.48  
% 7.65/1.48  fof(f35,plain,(
% 7.65/1.48    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 7.65/1.48    introduced(choice_axiom,[])).
% 7.65/1.48  
% 7.65/1.48  fof(f36,plain,(
% 7.65/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.65/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 7.65/1.48  
% 7.65/1.48  fof(f54,plain,(
% 7.65/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.65/1.48    inference(cnf_transformation,[],[f36])).
% 7.65/1.48  
% 7.65/1.48  fof(f89,plain,(
% 7.65/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.65/1.48    inference(definition_unfolding,[],[f54,f74])).
% 7.65/1.48  
% 7.65/1.48  fof(f97,plain,(
% 7.65/1.48    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 7.65/1.48    inference(equality_resolution,[],[f89])).
% 7.65/1.48  
% 7.65/1.48  fof(f98,plain,(
% 7.65/1.48    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 7.65/1.48    inference(equality_resolution,[],[f97])).
% 7.65/1.48  
% 7.65/1.48  fof(f53,plain,(
% 7.65/1.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 7.65/1.48    inference(cnf_transformation,[],[f36])).
% 7.65/1.48  
% 7.65/1.48  fof(f90,plain,(
% 7.65/1.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.65/1.48    inference(definition_unfolding,[],[f53,f74])).
% 7.65/1.48  
% 7.65/1.48  fof(f99,plain,(
% 7.65/1.48    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 7.65/1.48    inference(equality_resolution,[],[f90])).
% 7.65/1.48  
% 7.65/1.48  cnf(c_11,plain,
% 7.65/1.48      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.65/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_21,negated_conjecture,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
% 7.65/1.48      inference(cnf_transformation,[],[f92]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_10,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.65/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2,plain,
% 7.65/1.48      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.65/1.48      inference(cnf_transformation,[],[f40]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1007,negated_conjecture,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) = k1_xboole_0 ),
% 7.65/1.48      inference(theory_normalisation,[status(thm)],[c_21,c_10,c_2]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_0,plain,
% 7.65/1.48      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.65/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1208,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
% 7.65/1.48      inference(demodulation,[status(thm)],[c_1007,c_0]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1955,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_1208,c_10]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_8,plain,
% 7.65/1.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.65/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1573,plain,
% 7.65/1.48      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_8,c_2]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1965,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),X0)) = X0 ),
% 7.65/1.48      inference(light_normalisation,[status(thm)],[c_1955,c_1573]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2120,plain,
% 7.65/1.48      ( k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k5_xboole_0(sK3,k1_xboole_0) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_11,c_1965]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2125,plain,
% 7.65/1.48      ( k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK3 ),
% 7.65/1.48      inference(demodulation,[status(thm)],[c_2120,c_8]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2619,plain,
% 7.65/1.48      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_2125,c_0]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2622,plain,
% 7.65/1.48      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK3 ),
% 7.65/1.48      inference(demodulation,[status(thm)],[c_2619,c_2125]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2128,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
% 7.65/1.48      inference(demodulation,[status(thm)],[c_2125,c_1965]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2296,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X0,X1) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_2128,c_10]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2494,plain,
% 7.65/1.48      ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k1_xboole_0) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_11,c_2296]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2520,plain,
% 7.65/1.48      ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = sK3 ),
% 7.65/1.48      inference(demodulation,[status(thm)],[c_2494,c_8]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2978,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(sK3,X0),X0) = sK3 ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_2128,c_2520]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_3077,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(sK3,X1) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_2978,c_10]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2490,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X1,X0) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_2,c_2296]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_3382,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(sK3,X0))) = sK3 ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_2490,c_2978]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_5110,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(sK3,k5_xboole_0(sK3,X1)))) = sK3 ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_3077,c_3382]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_5175,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),X1)) = sK3 ),
% 7.65/1.48      inference(demodulation,[status(thm)],[c_5110,c_2128]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_5263,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X1)),sK3) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_5175,c_3077]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_5291,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(X1,sK3) ),
% 7.65/1.48      inference(demodulation,[status(thm)],[c_5263,c_2128]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_6720,plain,
% 7.65/1.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X1,sK3) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_5291,c_2490]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_8153,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,sK3) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_2128,c_6720]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_6713,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(sK3,k5_xboole_0(X1,sK3)) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_5291,c_2128]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2290,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(X0,sK3)) = X0 ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_2,c_2128]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_6724,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 7.65/1.48      inference(demodulation,[status(thm)],[c_6713,c_2290]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_6799,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_2,c_6724]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_8474,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X1,X0)) = k5_xboole_0(sK3,X1) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_8153,c_6799]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_10753,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),sK3),k5_xboole_0(sK3,X1)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_3077,c_8474]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_6679,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,X1))) = k5_xboole_0(k5_xboole_0(X1,X0),sK3) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_3077,c_5291]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_6765,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),sK3) = k5_xboole_0(X1,k5_xboole_0(sK3,X0)) ),
% 7.65/1.48      inference(demodulation,[status(thm)],[c_6679,c_2296]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_10852,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(sK3,X0)) = X1 ),
% 7.65/1.48      inference(light_normalisation,
% 7.65/1.48                [status(thm)],
% 7.65/1.48                [c_10753,c_2128,c_6765]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_11361,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(sK3,X0)) = k5_xboole_0(k5_xboole_0(sK3,sK3),X1) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_6720,c_10852]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2310,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,sK3))) = k5_xboole_0(X0,X1) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_10,c_2290]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1221,plain,
% 7.65/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_10,c_2]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_9140,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(sK3,X2)) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_2310,c_1221]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_10787,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,sK3),X2)) = k5_xboole_0(X2,k5_xboole_0(sK3,X0)) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_8474,c_1221]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_6838,plain,
% 7.65/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_6724,c_10]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_9156,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X2,X0) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_6838,c_1221]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_9236,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_1221,c_2296]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2756,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_2310,c_10]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2761,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.65/1.48      inference(light_normalisation,[status(thm)],[c_2756,c_10]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_9284,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.65/1.48      inference(light_normalisation,[status(thm)],[c_9236,c_2761]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_8449,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),X1) = k5_xboole_0(X0,sK3) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_6724,c_8153]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_10146,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,sK3),X2) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_8449,c_10]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1220,plain,
% 7.65/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_10,c_2]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_6717,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,sK3),X1),X0) = k5_xboole_0(X1,sK3) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_5291,c_2310]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_8823,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,sK3),X2)),X1) = k5_xboole_0(k5_xboole_0(X0,X2),sK3) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_1220,c_6717]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_8828,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))) = k5_xboole_0(k5_xboole_0(X1,X2),X0) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_1220,c_2490]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_3358,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_10,c_2490]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_8850,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 7.65/1.48      inference(light_normalisation,[status(thm)],[c_8828,c_3358]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_8874,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,k5_xboole_0(sK3,X2)) ),
% 7.65/1.48      inference(demodulation,[status(thm)],[c_8823,c_8850]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_10196,plain,
% 7.65/1.48      ( k5_xboole_0(X0,k5_xboole_0(sK3,X1)) = k5_xboole_0(k5_xboole_0(X0,sK3),X1) ),
% 7.65/1.48      inference(light_normalisation,[status(thm)],[c_10146,c_8874]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_10821,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(sK3,X0),X1) = k5_xboole_0(X0,k5_xboole_0(sK3,X1)) ),
% 7.65/1.48      inference(demodulation,
% 7.65/1.48                [status(thm)],
% 7.65/1.48                [c_10787,c_9156,c_9284,c_10196]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_11463,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(sK3,X0)) = X1 ),
% 7.65/1.48      inference(demodulation,
% 7.65/1.48                [status(thm)],
% 7.65/1.48                [c_11361,c_2128,c_9140,c_10821]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_19145,plain,
% 7.65/1.48      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(sK3,X0)) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_2622,c_11463]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_3071,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = sK3 ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_2296,c_2978]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_3847,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,sK3) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_3071,c_2310]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_3849,plain,
% 7.65/1.48      ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(sK3,X0)) = k1_xboole_0 ),
% 7.65/1.48      inference(demodulation,[status(thm)],[c_3847,c_11]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_19152,plain,
% 7.65/1.48      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 7.65/1.48      inference(light_normalisation,[status(thm)],[c_19145,c_3849]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1011,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2177,plain,
% 7.65/1.48      ( X0 != X1
% 7.65/1.48      | k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)) != X1
% 7.65/1.48      | k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)) = X0 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1011]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_3633,plain,
% 7.65/1.48      ( X0 != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.65/1.48      | k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = X0
% 7.65/1.48      | k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_2177]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_4715,plain,
% 7.65/1.48      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.65/1.48      | k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)
% 7.65/1.48      | k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0)) != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_3633]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_4716,plain,
% 7.65/1.48      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.65/1.48      | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 7.65/1.48      | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_4715]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1463,plain,
% 7.65/1.48      ( X0 != X1
% 7.65/1.48      | X0 = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.65/1.48      | k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != X1 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1011]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1751,plain,
% 7.65/1.48      ( X0 = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.65/1.48      | X0 != k1_xboole_0
% 7.65/1.48      | k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1463]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_4510,plain,
% 7.65/1.48      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.65/1.48      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != k1_xboole_0
% 7.65/1.48      | k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1751]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_4511,plain,
% 7.65/1.48      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.65/1.48      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0
% 7.65/1.48      | k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_4510]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2378,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0
% 7.65/1.48      | k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.65/1.48      | k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) != k1_xboole_0 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1751]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2380,plain,
% 7.65/1.48      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0
% 7.65/1.48      | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.65/1.48      | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k1_xboole_0 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_2378]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1015,plain,
% 7.65/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.65/1.48      theory(equality) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1237,plain,
% 7.65/1.48      ( ~ r2_hidden(X0,X1)
% 7.65/1.48      | r2_hidden(X2,k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0)))
% 7.65/1.48      | X2 != X0
% 7.65/1.48      | k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0)) != X1 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1015]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1258,plain,
% 7.65/1.48      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
% 7.65/1.48      | r2_hidden(X3,k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)))
% 7.65/1.48      | X3 != X0
% 7.65/1.48      | k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1237]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1260,plain,
% 7.65/1.48      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 7.65/1.48      | r2_hidden(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)))
% 7.65/1.48      | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 7.65/1.48      | sK2 != sK2 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1258]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_3,plain,
% 7.65/1.48      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 7.65/1.48      | ~ r1_xboole_0(X1,X2) ),
% 7.65/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_9,plain,
% 7.65/1.48      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.65/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_184,plain,
% 7.65/1.48      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 7.65/1.48      | X3 != X1
% 7.65/1.48      | k1_xboole_0 != X2 ),
% 7.65/1.48      inference(resolution_lifted,[status(thm)],[c_3,c_9]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_185,plain,
% 7.65/1.48      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ),
% 7.65/1.48      inference(unflattening,[status(thm)],[c_184]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_187,plain,
% 7.65/1.48      ( ~ r2_hidden(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0))) ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_185]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_6,plain,
% 7.65/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.65/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_48,plain,
% 7.65/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_18,plain,
% 7.65/1.48      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 7.65/1.48      inference(cnf_transformation,[],[f98]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_27,plain,
% 7.65/1.48      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_18]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_19,plain,
% 7.65/1.48      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 7.65/1.48      | X0 = X1
% 7.65/1.48      | X0 = X2
% 7.65/1.48      | X0 = X3 ),
% 7.65/1.48      inference(cnf_transformation,[],[f99]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_24,plain,
% 7.65/1.48      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 7.65/1.48      | sK2 = sK2 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_19]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(contradiction,plain,
% 7.65/1.48      ( $false ),
% 7.65/1.48      inference(minisat,
% 7.65/1.48                [status(thm)],
% 7.65/1.48                [c_19152,c_4716,c_4511,c_2380,c_1260,c_1007,c_187,c_48,
% 7.65/1.48                 c_27,c_24]) ).
% 7.65/1.48  
% 7.65/1.48  
% 7.65/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.65/1.48  
% 7.65/1.48  ------                               Statistics
% 7.65/1.48  
% 7.65/1.48  ------ General
% 7.65/1.48  
% 7.65/1.48  abstr_ref_over_cycles:                  0
% 7.65/1.48  abstr_ref_under_cycles:                 0
% 7.65/1.48  gc_basic_clause_elim:                   0
% 7.65/1.48  forced_gc_time:                         0
% 7.65/1.48  parsing_time:                           0.01
% 7.65/1.48  unif_index_cands_time:                  0.
% 7.65/1.48  unif_index_add_time:                    0.
% 7.65/1.48  orderings_time:                         0.
% 7.65/1.48  out_proof_time:                         0.011
% 7.65/1.48  total_time:                             0.619
% 7.65/1.48  num_of_symbols:                         43
% 7.65/1.48  num_of_terms:                           22205
% 7.65/1.48  
% 7.65/1.48  ------ Preprocessing
% 7.65/1.48  
% 7.65/1.48  num_of_splits:                          0
% 7.65/1.48  num_of_split_atoms:                     0
% 7.65/1.48  num_of_reused_defs:                     0
% 7.65/1.48  num_eq_ax_congr_red:                    22
% 7.65/1.48  num_of_sem_filtered_clauses:            1
% 7.65/1.48  num_of_subtypes:                        0
% 7.65/1.48  monotx_restored_types:                  0
% 7.65/1.48  sat_num_of_epr_types:                   0
% 7.65/1.48  sat_num_of_non_cyclic_types:            0
% 7.65/1.48  sat_guarded_non_collapsed_types:        0
% 7.65/1.48  num_pure_diseq_elim:                    0
% 7.65/1.48  simp_replaced_by:                       0
% 7.65/1.48  res_preprocessed:                       102
% 7.65/1.48  prep_upred:                             0
% 7.65/1.48  prep_unflattend:                        58
% 7.65/1.48  smt_new_axioms:                         0
% 7.65/1.48  pred_elim_cands:                        2
% 7.65/1.48  pred_elim:                              1
% 7.65/1.48  pred_elim_cl:                           1
% 7.65/1.48  pred_elim_cycles:                       5
% 7.65/1.48  merged_defs:                            0
% 7.65/1.48  merged_defs_ncl:                        0
% 7.65/1.48  bin_hyper_res:                          0
% 7.65/1.48  prep_cycles:                            4
% 7.65/1.48  pred_elim_time:                         0.012
% 7.65/1.48  splitting_time:                         0.
% 7.65/1.48  sem_filter_time:                        0.
% 7.65/1.48  monotx_time:                            0.
% 7.65/1.48  subtype_inf_time:                       0.
% 7.65/1.48  
% 7.65/1.48  ------ Problem properties
% 7.65/1.48  
% 7.65/1.48  clauses:                                21
% 7.65/1.48  conjectures:                            1
% 7.65/1.48  epr:                                    1
% 7.65/1.48  horn:                                   18
% 7.65/1.48  ground:                                 1
% 7.65/1.48  unary:                                  14
% 7.65/1.48  binary:                                 2
% 7.65/1.48  lits:                                   36
% 7.65/1.48  lits_eq:                                23
% 7.65/1.48  fd_pure:                                0
% 7.65/1.48  fd_pseudo:                              0
% 7.65/1.48  fd_cond:                                0
% 7.65/1.48  fd_pseudo_cond:                         4
% 7.65/1.48  ac_symbols:                             1
% 7.65/1.48  
% 7.65/1.48  ------ Propositional Solver
% 7.65/1.48  
% 7.65/1.48  prop_solver_calls:                      30
% 7.65/1.48  prop_fast_solver_calls:                 696
% 7.65/1.48  smt_solver_calls:                       0
% 7.65/1.48  smt_fast_solver_calls:                  0
% 7.65/1.48  prop_num_of_clauses:                    4063
% 7.65/1.48  prop_preprocess_simplified:             8711
% 7.65/1.48  prop_fo_subsumed:                       1
% 7.65/1.48  prop_solver_time:                       0.
% 7.65/1.48  smt_solver_time:                        0.
% 7.65/1.48  smt_fast_solver_time:                   0.
% 7.65/1.48  prop_fast_solver_time:                  0.
% 7.65/1.48  prop_unsat_core_time:                   0.
% 7.65/1.48  
% 7.65/1.48  ------ QBF
% 7.65/1.48  
% 7.65/1.48  qbf_q_res:                              0
% 7.65/1.48  qbf_num_tautologies:                    0
% 7.65/1.48  qbf_prep_cycles:                        0
% 7.65/1.48  
% 7.65/1.48  ------ BMC1
% 7.65/1.48  
% 7.65/1.48  bmc1_current_bound:                     -1
% 7.65/1.48  bmc1_last_solved_bound:                 -1
% 7.65/1.48  bmc1_unsat_core_size:                   -1
% 7.65/1.48  bmc1_unsat_core_parents_size:           -1
% 7.65/1.48  bmc1_merge_next_fun:                    0
% 7.65/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.65/1.48  
% 7.65/1.48  ------ Instantiation
% 7.65/1.48  
% 7.65/1.48  inst_num_of_clauses:                    1164
% 7.65/1.48  inst_num_in_passive:                    356
% 7.65/1.48  inst_num_in_active:                     433
% 7.65/1.48  inst_num_in_unprocessed:                376
% 7.65/1.48  inst_num_of_loops:                      510
% 7.65/1.48  inst_num_of_learning_restarts:          0
% 7.65/1.48  inst_num_moves_active_passive:          73
% 7.65/1.48  inst_lit_activity:                      0
% 7.65/1.48  inst_lit_activity_moves:                0
% 7.65/1.48  inst_num_tautologies:                   0
% 7.65/1.48  inst_num_prop_implied:                  0
% 7.65/1.48  inst_num_existing_simplified:           0
% 7.65/1.48  inst_num_eq_res_simplified:             0
% 7.65/1.48  inst_num_child_elim:                    0
% 7.65/1.48  inst_num_of_dismatching_blockings:      1449
% 7.65/1.48  inst_num_of_non_proper_insts:           1638
% 7.65/1.48  inst_num_of_duplicates:                 0
% 7.65/1.48  inst_inst_num_from_inst_to_res:         0
% 7.65/1.48  inst_dismatching_checking_time:         0.
% 7.65/1.48  
% 7.65/1.48  ------ Resolution
% 7.65/1.48  
% 7.65/1.48  res_num_of_clauses:                     0
% 7.65/1.48  res_num_in_passive:                     0
% 7.65/1.48  res_num_in_active:                      0
% 7.65/1.48  res_num_of_loops:                       106
% 7.65/1.48  res_forward_subset_subsumed:            319
% 7.65/1.48  res_backward_subset_subsumed:           6
% 7.65/1.48  res_forward_subsumed:                   0
% 7.65/1.48  res_backward_subsumed:                  0
% 7.65/1.48  res_forward_subsumption_resolution:     2
% 7.65/1.48  res_backward_subsumption_resolution:    0
% 7.65/1.48  res_clause_to_clause_subsumption:       9458
% 7.65/1.48  res_orphan_elimination:                 0
% 7.65/1.48  res_tautology_del:                      229
% 7.65/1.48  res_num_eq_res_simplified:              0
% 7.65/1.48  res_num_sel_changes:                    0
% 7.65/1.48  res_moves_from_active_to_pass:          0
% 7.65/1.48  
% 7.65/1.48  ------ Superposition
% 7.65/1.48  
% 7.65/1.48  sup_time_total:                         0.
% 7.65/1.48  sup_time_generating:                    0.
% 7.65/1.48  sup_time_sim_full:                      0.
% 7.65/1.48  sup_time_sim_immed:                     0.
% 7.65/1.48  
% 7.65/1.48  sup_num_of_clauses:                     733
% 7.65/1.48  sup_num_in_active:                      83
% 7.65/1.48  sup_num_in_passive:                     650
% 7.65/1.48  sup_num_of_loops:                       100
% 7.65/1.48  sup_fw_superposition:                   3596
% 7.65/1.48  sup_bw_superposition:                   2801
% 7.65/1.48  sup_immediate_simplified:               2581
% 7.65/1.48  sup_given_eliminated:                   4
% 7.65/1.48  comparisons_done:                       0
% 7.65/1.48  comparisons_avoided:                    6
% 7.65/1.48  
% 7.65/1.48  ------ Simplifications
% 7.65/1.48  
% 7.65/1.48  
% 7.65/1.48  sim_fw_subset_subsumed:                 0
% 7.65/1.48  sim_bw_subset_subsumed:                 0
% 7.65/1.48  sim_fw_subsumed:                        183
% 7.65/1.48  sim_bw_subsumed:                        7
% 7.65/1.48  sim_fw_subsumption_res:                 0
% 7.65/1.48  sim_bw_subsumption_res:                 0
% 7.65/1.48  sim_tautology_del:                      0
% 7.65/1.48  sim_eq_tautology_del:                   872
% 7.65/1.48  sim_eq_res_simp:                        0
% 7.65/1.48  sim_fw_demodulated:                     1680
% 7.65/1.48  sim_bw_demodulated:                     32
% 7.65/1.48  sim_light_normalised:                   995
% 7.65/1.48  sim_joinable_taut:                      218
% 7.65/1.48  sim_joinable_simp:                      0
% 7.65/1.48  sim_ac_normalised:                      0
% 7.65/1.48  sim_smt_subsumption:                    0
% 7.65/1.48  
%------------------------------------------------------------------------------
