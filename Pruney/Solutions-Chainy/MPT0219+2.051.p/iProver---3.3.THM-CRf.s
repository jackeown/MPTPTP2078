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
% DateTime   : Thu Dec  3 11:29:17 EST 2020

% Result     : Theorem 35.25s
% Output     : CNFRefutation 35.25s
% Verified   : 
% Statistics : Number of formulae       :  278 (294894 expanded)
%              Number of clauses        :  194 (105459 expanded)
%              Number of leaves         :   26 (78957 expanded)
%              Depth                    :   47
%              Number of atoms          :  516 (360833 expanded)
%              Number of equality atoms :  383 (286217 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :   14 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

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
    inference(nnf_transformation,[],[f25])).

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

fof(f62,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f76,f77])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f75,f81])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f74,f82])).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f73,f83])).

fof(f93,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f62,f84])).

fof(f105,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f93])).

fof(f106,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f105])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f26,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK3 != sK4
      & k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( sK3 != sK4
    & k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f41])).

fof(f78,plain,(
    k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f80,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f58,f51])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f72,f84])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f71,f85])).

fof(f101,plain,(
    k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f78,f80,f86,f86,f86])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f87,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) ),
    inference(definition_unfolding,[],[f54,f51,f51,f80])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f88,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f55,f80,f51])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f104,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

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
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f67,f86])).

fof(f114,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f100])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f68,f86])).

fof(f112,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f99])).

fof(f113,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f112])).

fof(f79,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_18,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_622,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_27,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_999,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_0,c_27])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_226,plain,
    ( X0 != X1
    | k3_xboole_0(X2,X1) = X2
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_227,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_226])).

cnf(c_1000,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_227,c_0])).

cnf(c_13,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1392,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0)))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0)))),k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_13,c_10])).

cnf(c_34554,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))),k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))),k5_xboole_0(X0,X1))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1000,c_1392])).

cnf(c_11,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1366,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_1000,c_11])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1368,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1366,c_12,c_1000])).

cnf(c_7,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1347,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))))) = X0 ),
    inference(superposition,[status(thm)],[c_13,c_11])).

cnf(c_5422,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)))),X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_1347,c_13])).

cnf(c_19336,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))),X2))) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_13,c_5422])).

cnf(c_25594,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,X0),X0)),X1))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_19336])).

cnf(c_1397,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)),X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1000,c_10])).

cnf(c_1404,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1397,c_7,c_12,c_227,c_1368])).

cnf(c_1405,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1404,c_1368])).

cnf(c_25617,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_25594,c_12,c_227,c_1405])).

cnf(c_26074,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_25617,c_13])).

cnf(c_26164,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_26074,c_13])).

cnf(c_26427,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X2),X3)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))),X3)) ),
    inference(superposition,[status(thm)],[c_26164,c_26164])).

cnf(c_26433,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X2),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_26164,c_13])).

cnf(c_26555,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
    inference(demodulation,[status(thm)],[c_26427,c_26164,c_26433])).

cnf(c_34902,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)),k5_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_34554,c_227,c_1368,c_26555])).

cnf(c_34903,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_34902,c_7,c_12])).

cnf(c_35692,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X1)),X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_34903,c_13])).

cnf(c_35784,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = X2 ),
    inference(demodulation,[status(thm)],[c_35692,c_1368,c_26555])).

cnf(c_35785,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
    inference(light_normalisation,[status(thm)],[c_35784,c_13])).

cnf(c_39629,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_999,c_35785])).

cnf(c_1282,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) ),
    inference(superposition,[status(thm)],[c_999,c_13])).

cnf(c_1465,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),X1) ),
    inference(superposition,[status(thm)],[c_1282,c_13])).

cnf(c_1607,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),X0)) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0))) ),
    inference(superposition,[status(thm)],[c_10,c_1465])).

cnf(c_1609,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),X1) ),
    inference(superposition,[status(thm)],[c_13,c_1465])).

cnf(c_1617,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),X1) ),
    inference(demodulation,[status(thm)],[c_1609,c_1282])).

cnf(c_1827,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),X0)) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)) ),
    inference(demodulation,[status(thm)],[c_1607,c_1282,c_1617])).

cnf(c_25973,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2)))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_13,c_25617])).

cnf(c_26268,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_25973,c_13])).

cnf(c_35681,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_34903,c_26268])).

cnf(c_35807,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0)))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_35681,c_34903])).

cnf(c_35808,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_35807,c_12])).

cnf(c_40628,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)))) = k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),X0) ),
    inference(superposition,[status(thm)],[c_1827,c_35808])).

cnf(c_1805,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1),X0)))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1),X0)))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1))) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1))) ),
    inference(superposition,[status(thm)],[c_1617,c_10])).

cnf(c_2818,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k1_xboole_0))),k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k1_xboole_0))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))) ),
    inference(superposition,[status(thm)],[c_1000,c_1805])).

cnf(c_2859,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))) ),
    inference(light_normalisation,[status(thm)],[c_2818,c_12])).

cnf(c_2860,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2859,c_7,c_227,c_1368,c_1617])).

cnf(c_3801,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1282,c_2860])).

cnf(c_4545,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1282,c_3801])).

cnf(c_4841,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3801,c_4545])).

cnf(c_1619,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),X1)) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1617,c_1465])).

cnf(c_4869,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4841,c_12,c_1282,c_1619])).

cnf(c_26075,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),X2)))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_25617,c_13])).

cnf(c_26163,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_26075,c_13])).

cnf(c_28898,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_4869,c_26163])).

cnf(c_1462,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) ),
    inference(superposition,[status(thm)],[c_13,c_1282])).

cnf(c_1605,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)),X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),X1) ),
    inference(superposition,[status(thm)],[c_1462,c_13])).

cnf(c_2057,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)),X1)) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1605,c_1605,c_1617])).

cnf(c_29427,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1))))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1)) ),
    inference(superposition,[status(thm)],[c_2057,c_26268])).

cnf(c_29031,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2)))),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_26163,c_13])).

cnf(c_29202,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2)))),X3)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
    inference(light_normalisation,[status(thm)],[c_29031,c_26555])).

cnf(c_29203,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))),X3))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
    inference(demodulation,[status(thm)],[c_29202,c_26555])).

cnf(c_29204,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
    inference(demodulation,[status(thm)],[c_29203,c_26555])).

cnf(c_26434,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),X2)),X3))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_26164,c_13])).

cnf(c_26857,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))),X3))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
    inference(light_normalisation,[status(thm)],[c_26434,c_13])).

cnf(c_26858,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
    inference(demodulation,[status(thm)],[c_26857,c_26555])).

cnf(c_26859,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3))))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
    inference(light_normalisation,[status(thm)],[c_26858,c_26555])).

cnf(c_29205,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
    inference(light_normalisation,[status(thm)],[c_29204,c_26555,c_26859])).

cnf(c_30194,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1))))))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X1))) ),
    inference(demodulation,[status(thm)],[c_29427,c_26555,c_29205])).

cnf(c_30195,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1))))))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X1))) ),
    inference(demodulation,[status(thm)],[c_30194,c_29205])).

cnf(c_30196,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1))))))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X1))) ),
    inference(demodulation,[status(thm)],[c_30195,c_29205])).

cnf(c_30197,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1)))))))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X1))) ),
    inference(demodulation,[status(thm)],[c_30196,c_26555])).

cnf(c_30198,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1))))))))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X1))) ),
    inference(demodulation,[status(thm)],[c_30197,c_1617])).

cnf(c_2061,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0),X1))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_13,c_2057])).

cnf(c_29209,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,X2))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_29205,c_26163])).

cnf(c_29311,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_29209,c_29205])).

cnf(c_29312,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_29311,c_13])).

cnf(c_30199,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1)))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X1))) ),
    inference(demodulation,[status(thm)],[c_30198,c_2061,c_29312])).

cnf(c_29431,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k1_xboole_0)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)) ),
    inference(superposition,[status(thm)],[c_3801,c_26268])).

cnf(c_30180,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X0)) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),X0)) ),
    inference(demodulation,[status(thm)],[c_29431,c_12,c_29205])).

cnf(c_30181,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),X0)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)) ),
    inference(light_normalisation,[status(thm)],[c_30180,c_999])).

cnf(c_30182,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X0))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)) ),
    inference(demodulation,[status(thm)],[c_30181,c_26555,c_29205])).

cnf(c_30202,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)) ),
    inference(demodulation,[status(thm)],[c_30199,c_30182])).

cnf(c_31225,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_28898,c_30202])).

cnf(c_31226,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0))) ),
    inference(light_normalisation,[status(thm)],[c_31225,c_999])).

cnf(c_3818,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2860,c_1282])).

cnf(c_3831,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3818,c_999])).

cnf(c_26094,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)) ),
    inference(superposition,[status(thm)],[c_25617,c_1282])).

cnf(c_26145,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) ),
    inference(light_normalisation,[status(thm)],[c_26094,c_1282])).

cnf(c_27474,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) ),
    inference(superposition,[status(thm)],[c_13,c_26145])).

cnf(c_31227,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_31226,c_12,c_1282,c_2061,c_3831,c_27474,c_29205])).

cnf(c_2844,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))) ),
    inference(superposition,[status(thm)],[c_1805,c_1619])).

cnf(c_2178,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),X1),X2)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_1619,c_13])).

cnf(c_1614,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),X1),X2)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_1465,c_13])).

cnf(c_1819,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),X1),X2)) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(X0,X1),X2)) ),
    inference(demodulation,[status(thm)],[c_1614,c_1617])).

cnf(c_1820,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),X1),X2)) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_1819,c_13])).

cnf(c_2181,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,X1)),X2) ),
    inference(light_normalisation,[status(thm)],[c_2178,c_1820])).

cnf(c_2845,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))) ),
    inference(demodulation,[status(thm)],[c_2844,c_1282,c_2181])).

cnf(c_33382,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))),k5_xboole_0(k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))),k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))))),k1_xboole_0))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))))))) ),
    inference(superposition,[status(thm)],[c_31227,c_2845])).

cnf(c_33395,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))),k5_xboole_0(k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))),k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))))),k1_xboole_0))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_33382,c_31227])).

cnf(c_4226,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_3831,c_1617])).

cnf(c_4233,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4226,c_1368])).

cnf(c_33396,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))),k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))))),k1_xboole_0))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_33395,c_12,c_1000,c_2057,c_4233])).

cnf(c_33397,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),k1_xboole_0)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_33396,c_227,c_1000,c_1368,c_26555])).

cnf(c_33398,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k1_xboole_0))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_33397,c_1617])).

cnf(c_33399,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(light_normalisation,[status(thm)],[c_33398,c_12])).

cnf(c_1386,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_10])).

cnf(c_9069,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_1386])).

cnf(c_13051,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(superposition,[status(thm)],[c_999,c_9069])).

cnf(c_13801,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13051,c_2860])).

cnf(c_34516,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0))),k5_xboole_0(X0,X1))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1368,c_1392])).

cnf(c_34935,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_34516,c_7,c_12,c_227,c_1000,c_1368,c_26555,c_29205])).

cnf(c_35982,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k5_xboole_0(k1_xboole_0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13801,c_34935])).

cnf(c_13071,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X0,X1)),k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_9069,c_13])).

cnf(c_16702,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(superposition,[status(thm)],[c_999,c_13071])).

cnf(c_17208,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(superposition,[status(thm)],[c_13,c_16702])).

cnf(c_17244,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(superposition,[status(thm)],[c_0,c_17208])).

cnf(c_17278,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(demodulation,[status(thm)],[c_17244,c_12,c_1405,c_1462])).

cnf(c_36199,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k1_xboole_0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_35982,c_17278])).

cnf(c_36200,plain,
    ( k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_36199,c_1368,c_26555])).

cnf(c_36201,plain,
    ( k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_36200,c_1617])).

cnf(c_6393,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))))),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4869,c_4545])).

cnf(c_6412,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6393,c_12,c_1282,c_1619])).

cnf(c_13795,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13051,c_6412])).

cnf(c_17600,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13795,c_13795,c_17278])).

cnf(c_17629,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17600,c_1282])).

cnf(c_17880,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17629,c_1282])).

cnf(c_35991,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k1_xboole_0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17880,c_34935])).

cnf(c_29443,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k1_xboole_0)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(superposition,[status(thm)],[c_17880,c_26268])).

cnf(c_30102,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(demodulation,[status(thm)],[c_29443,c_12,c_29205])).

cnf(c_26046,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_13051,c_25617])).

cnf(c_26194,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(demodulation,[status(thm)],[c_26046,c_25617])).

cnf(c_26195,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_26194,c_13051,c_17278])).

cnf(c_30103,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(light_normalisation,[status(thm)],[c_30102,c_999,c_26195])).

cnf(c_30104,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(demodulation,[status(thm)],[c_30103,c_26555,c_29205])).

cnf(c_30200,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(demodulation,[status(thm)],[c_30199,c_30104])).

cnf(c_36161,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),k5_xboole_0(k1_xboole_0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_35991,c_30200])).

cnf(c_36162,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_36161,c_1368,c_26555])).

cnf(c_36163,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_36162,c_26555])).

cnf(c_36164,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_36163,c_26555])).

cnf(c_36165,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_36164,c_1617])).

cnf(c_36202,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_36201,c_36165])).

cnf(c_36203,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_36202,c_12])).

cnf(c_44441,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_40628,c_7,c_12,c_227,c_1000,c_1368,c_33399,c_36203])).

cnf(c_39794,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
    inference(superposition,[status(thm)],[c_35785,c_35785])).

cnf(c_39964,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = sP0_iProver_split(X1,X2) ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_39794])).

cnf(c_40686,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),X1),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),k1_xboole_0)) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_34903,c_35808])).

cnf(c_40824,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X0),X1),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),k1_xboole_0)))) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_40686,c_26555,c_29205])).

cnf(c_36018,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X0),X1),X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_34935,c_13])).

cnf(c_36113,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X0),X1),X2)) = X2 ),
    inference(demodulation,[status(thm)],[c_36018,c_1368])).

cnf(c_40825,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(k5_xboole_0(X1,X0),k1_xboole_0)))) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_40824,c_29205,c_36113])).

cnf(c_40826,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),k5_xboole_0(k5_xboole_0(X1,X0),k1_xboole_0)))) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_40825,c_29205])).

cnf(c_40827,plain,
    ( sP0_iProver_split(X0,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0))) = k5_xboole_0(X1,k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_40826,c_26555,c_39964])).

cnf(c_40828,plain,
    ( sP0_iProver_split(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X1)),k1_xboole_0))) = k5_xboole_0(X1,k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_40827,c_29205])).

cnf(c_40829,plain,
    ( sP0_iProver_split(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)))) = k5_xboole_0(X1,k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_40828,c_26555])).

cnf(c_40830,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = sP0_iProver_split(X1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_40829,c_12,c_34903])).

cnf(c_44442,plain,
    ( sP0_iProver_split(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_44441,c_12,c_39964,c_40830])).

cnf(c_36052,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k1_xboole_0)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_34935,c_26268])).

cnf(c_36055,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,X1),X1) ),
    inference(demodulation,[status(thm)],[c_36052,c_12,c_1368,c_1405,c_29205])).

cnf(c_36056,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X0,X1),X0))) = k5_xboole_0(k5_xboole_0(X0,X1),X1) ),
    inference(demodulation,[status(thm)],[c_36055,c_26555,c_29205])).

cnf(c_36057,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X0))) = k5_xboole_0(k5_xboole_0(X0,X1),X1) ),
    inference(light_normalisation,[status(thm)],[c_36056,c_1405])).

cnf(c_36058,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,X1),X1) ),
    inference(demodulation,[status(thm)],[c_36057,c_1368,c_29205])).

cnf(c_36059,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X0))) = k5_xboole_0(k5_xboole_0(X0,X1),X1) ),
    inference(demodulation,[status(thm)],[c_36058,c_26555])).

cnf(c_36060,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(demodulation,[status(thm)],[c_36059,c_12,c_34935])).

cnf(c_40695,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),k5_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_36060,c_35808])).

cnf(c_44122,plain,
    ( k5_xboole_0(sP0_iProver_split(X0,k1_xboole_0),k5_xboole_0(X1,X0)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_40695,c_40830])).

cnf(c_40730,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),k5_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),X0)) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_35808,c_35808])).

cnf(c_44054,plain,
    ( k5_xboole_0(k5_xboole_0(sP0_iProver_split(X0,k1_xboole_0),k5_xboole_0(X1,X0)),k5_xboole_0(sP0_iProver_split(X0,k1_xboole_0),X1)) = sP0_iProver_split(X0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_40730,c_40830])).

cnf(c_44123,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split(X1,k1_xboole_0),X0)) = sP0_iProver_split(X1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_44122,c_44054])).

cnf(c_44448,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_44442,c_44123])).

cnf(c_45916,plain,
    ( k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_39629,c_44448])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_627,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_47977,plain,
    ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_45916,c_627])).

cnf(c_56319,plain,
    ( r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_622,c_47977])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_678,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_679,plain,
    ( sK4 = X0
    | r2_hidden(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_681,plain,
    ( sK4 = sK3
    | r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_353,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_657,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_658,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_24,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_32,plain,
    ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_29,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_56319,c_681,c_658,c_32,c_29,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:43:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 35.25/4.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.25/4.99  
% 35.25/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.25/4.99  
% 35.25/4.99  ------  iProver source info
% 35.25/4.99  
% 35.25/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.25/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.25/4.99  git: non_committed_changes: false
% 35.25/4.99  git: last_make_outside_of_git: false
% 35.25/4.99  
% 35.25/4.99  ------ 
% 35.25/4.99  
% 35.25/4.99  ------ Input Options
% 35.25/4.99  
% 35.25/4.99  --out_options                           all
% 35.25/4.99  --tptp_safe_out                         true
% 35.25/4.99  --problem_path                          ""
% 35.25/4.99  --include_path                          ""
% 35.25/4.99  --clausifier                            res/vclausify_rel
% 35.25/4.99  --clausifier_options                    ""
% 35.25/4.99  --stdin                                 false
% 35.25/4.99  --stats_out                             all
% 35.25/4.99  
% 35.25/4.99  ------ General Options
% 35.25/4.99  
% 35.25/4.99  --fof                                   false
% 35.25/4.99  --time_out_real                         305.
% 35.25/4.99  --time_out_virtual                      -1.
% 35.25/4.99  --symbol_type_check                     false
% 35.25/4.99  --clausify_out                          false
% 35.25/4.99  --sig_cnt_out                           false
% 35.25/4.99  --trig_cnt_out                          false
% 35.25/4.99  --trig_cnt_out_tolerance                1.
% 35.25/4.99  --trig_cnt_out_sk_spl                   false
% 35.25/4.99  --abstr_cl_out                          false
% 35.25/4.99  
% 35.25/4.99  ------ Global Options
% 35.25/4.99  
% 35.25/4.99  --schedule                              default
% 35.25/4.99  --add_important_lit                     false
% 35.25/4.99  --prop_solver_per_cl                    1000
% 35.25/4.99  --min_unsat_core                        false
% 35.25/4.99  --soft_assumptions                      false
% 35.25/4.99  --soft_lemma_size                       3
% 35.25/4.99  --prop_impl_unit_size                   0
% 35.25/4.99  --prop_impl_unit                        []
% 35.25/4.99  --share_sel_clauses                     true
% 35.25/4.99  --reset_solvers                         false
% 35.25/4.99  --bc_imp_inh                            [conj_cone]
% 35.25/4.99  --conj_cone_tolerance                   3.
% 35.25/4.99  --extra_neg_conj                        none
% 35.25/4.99  --large_theory_mode                     true
% 35.25/4.99  --prolific_symb_bound                   200
% 35.25/4.99  --lt_threshold                          2000
% 35.25/4.99  --clause_weak_htbl                      true
% 35.25/4.99  --gc_record_bc_elim                     false
% 35.25/4.99  
% 35.25/4.99  ------ Preprocessing Options
% 35.25/4.99  
% 35.25/4.99  --preprocessing_flag                    true
% 35.25/4.99  --time_out_prep_mult                    0.1
% 35.25/4.99  --splitting_mode                        input
% 35.25/4.99  --splitting_grd                         true
% 35.25/4.99  --splitting_cvd                         false
% 35.25/4.99  --splitting_cvd_svl                     false
% 35.25/4.99  --splitting_nvd                         32
% 35.25/4.99  --sub_typing                            true
% 35.25/4.99  --prep_gs_sim                           true
% 35.25/4.99  --prep_unflatten                        true
% 35.25/4.99  --prep_res_sim                          true
% 35.25/4.99  --prep_upred                            true
% 35.25/4.99  --prep_sem_filter                       exhaustive
% 35.25/4.99  --prep_sem_filter_out                   false
% 35.25/4.99  --pred_elim                             true
% 35.25/4.99  --res_sim_input                         true
% 35.25/4.99  --eq_ax_congr_red                       true
% 35.25/4.99  --pure_diseq_elim                       true
% 35.25/4.99  --brand_transform                       false
% 35.25/4.99  --non_eq_to_eq                          false
% 35.25/4.99  --prep_def_merge                        true
% 35.25/4.99  --prep_def_merge_prop_impl              false
% 35.25/4.99  --prep_def_merge_mbd                    true
% 35.25/4.99  --prep_def_merge_tr_red                 false
% 35.25/4.99  --prep_def_merge_tr_cl                  false
% 35.25/4.99  --smt_preprocessing                     true
% 35.25/4.99  --smt_ac_axioms                         fast
% 35.25/4.99  --preprocessed_out                      false
% 35.25/4.99  --preprocessed_stats                    false
% 35.25/4.99  
% 35.25/4.99  ------ Abstraction refinement Options
% 35.25/4.99  
% 35.25/4.99  --abstr_ref                             []
% 35.25/4.99  --abstr_ref_prep                        false
% 35.25/4.99  --abstr_ref_until_sat                   false
% 35.25/4.99  --abstr_ref_sig_restrict                funpre
% 35.25/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.25/4.99  --abstr_ref_under                       []
% 35.25/4.99  
% 35.25/4.99  ------ SAT Options
% 35.25/4.99  
% 35.25/4.99  --sat_mode                              false
% 35.25/4.99  --sat_fm_restart_options                ""
% 35.25/4.99  --sat_gr_def                            false
% 35.25/4.99  --sat_epr_types                         true
% 35.25/4.99  --sat_non_cyclic_types                  false
% 35.25/4.99  --sat_finite_models                     false
% 35.25/4.99  --sat_fm_lemmas                         false
% 35.25/4.99  --sat_fm_prep                           false
% 35.25/4.99  --sat_fm_uc_incr                        true
% 35.25/4.99  --sat_out_model                         small
% 35.25/4.99  --sat_out_clauses                       false
% 35.25/4.99  
% 35.25/4.99  ------ QBF Options
% 35.25/4.99  
% 35.25/4.99  --qbf_mode                              false
% 35.25/4.99  --qbf_elim_univ                         false
% 35.25/4.99  --qbf_dom_inst                          none
% 35.25/4.99  --qbf_dom_pre_inst                      false
% 35.25/4.99  --qbf_sk_in                             false
% 35.25/4.99  --qbf_pred_elim                         true
% 35.25/4.99  --qbf_split                             512
% 35.25/4.99  
% 35.25/4.99  ------ BMC1 Options
% 35.25/4.99  
% 35.25/4.99  --bmc1_incremental                      false
% 35.25/4.99  --bmc1_axioms                           reachable_all
% 35.25/4.99  --bmc1_min_bound                        0
% 35.25/4.99  --bmc1_max_bound                        -1
% 35.25/4.99  --bmc1_max_bound_default                -1
% 35.25/4.99  --bmc1_symbol_reachability              true
% 35.25/4.99  --bmc1_property_lemmas                  false
% 35.25/4.99  --bmc1_k_induction                      false
% 35.25/4.99  --bmc1_non_equiv_states                 false
% 35.25/4.99  --bmc1_deadlock                         false
% 35.25/4.99  --bmc1_ucm                              false
% 35.25/4.99  --bmc1_add_unsat_core                   none
% 35.25/4.99  --bmc1_unsat_core_children              false
% 35.25/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.25/4.99  --bmc1_out_stat                         full
% 35.25/4.99  --bmc1_ground_init                      false
% 35.25/4.99  --bmc1_pre_inst_next_state              false
% 35.25/4.99  --bmc1_pre_inst_state                   false
% 35.25/4.99  --bmc1_pre_inst_reach_state             false
% 35.25/4.99  --bmc1_out_unsat_core                   false
% 35.25/4.99  --bmc1_aig_witness_out                  false
% 35.25/4.99  --bmc1_verbose                          false
% 35.25/4.99  --bmc1_dump_clauses_tptp                false
% 35.25/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.25/4.99  --bmc1_dump_file                        -
% 35.25/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.25/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.25/4.99  --bmc1_ucm_extend_mode                  1
% 35.25/4.99  --bmc1_ucm_init_mode                    2
% 35.25/4.99  --bmc1_ucm_cone_mode                    none
% 35.25/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.25/4.99  --bmc1_ucm_relax_model                  4
% 35.25/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.25/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.25/4.99  --bmc1_ucm_layered_model                none
% 35.25/4.99  --bmc1_ucm_max_lemma_size               10
% 35.25/4.99  
% 35.25/4.99  ------ AIG Options
% 35.25/4.99  
% 35.25/4.99  --aig_mode                              false
% 35.25/4.99  
% 35.25/4.99  ------ Instantiation Options
% 35.25/4.99  
% 35.25/4.99  --instantiation_flag                    true
% 35.25/4.99  --inst_sos_flag                         true
% 35.25/4.99  --inst_sos_phase                        true
% 35.25/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.25/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.25/4.99  --inst_lit_sel_side                     num_symb
% 35.25/4.99  --inst_solver_per_active                1400
% 35.25/4.99  --inst_solver_calls_frac                1.
% 35.25/4.99  --inst_passive_queue_type               priority_queues
% 35.25/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.25/4.99  --inst_passive_queues_freq              [25;2]
% 35.25/4.99  --inst_dismatching                      true
% 35.25/4.99  --inst_eager_unprocessed_to_passive     true
% 35.25/4.99  --inst_prop_sim_given                   true
% 35.25/4.99  --inst_prop_sim_new                     false
% 35.25/4.99  --inst_subs_new                         false
% 35.25/4.99  --inst_eq_res_simp                      false
% 35.25/4.99  --inst_subs_given                       false
% 35.25/4.99  --inst_orphan_elimination               true
% 35.25/4.99  --inst_learning_loop_flag               true
% 35.25/4.99  --inst_learning_start                   3000
% 35.25/4.99  --inst_learning_factor                  2
% 35.25/4.99  --inst_start_prop_sim_after_learn       3
% 35.25/4.99  --inst_sel_renew                        solver
% 35.25/4.99  --inst_lit_activity_flag                true
% 35.25/4.99  --inst_restr_to_given                   false
% 35.25/4.99  --inst_activity_threshold               500
% 35.25/4.99  --inst_out_proof                        true
% 35.25/4.99  
% 35.25/4.99  ------ Resolution Options
% 35.25/4.99  
% 35.25/4.99  --resolution_flag                       true
% 35.25/4.99  --res_lit_sel                           adaptive
% 35.25/4.99  --res_lit_sel_side                      none
% 35.25/4.99  --res_ordering                          kbo
% 35.25/4.99  --res_to_prop_solver                    active
% 35.25/4.99  --res_prop_simpl_new                    false
% 35.25/4.99  --res_prop_simpl_given                  true
% 35.25/4.99  --res_passive_queue_type                priority_queues
% 35.25/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.25/4.99  --res_passive_queues_freq               [15;5]
% 35.25/4.99  --res_forward_subs                      full
% 35.25/4.99  --res_backward_subs                     full
% 35.25/4.99  --res_forward_subs_resolution           true
% 35.25/4.99  --res_backward_subs_resolution          true
% 35.25/4.99  --res_orphan_elimination                true
% 35.25/4.99  --res_time_limit                        2.
% 35.25/4.99  --res_out_proof                         true
% 35.25/4.99  
% 35.25/4.99  ------ Superposition Options
% 35.25/4.99  
% 35.25/4.99  --superposition_flag                    true
% 35.25/4.99  --sup_passive_queue_type                priority_queues
% 35.25/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.25/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.25/4.99  --demod_completeness_check              fast
% 35.25/4.99  --demod_use_ground                      true
% 35.25/4.99  --sup_to_prop_solver                    passive
% 35.25/4.99  --sup_prop_simpl_new                    true
% 35.25/4.99  --sup_prop_simpl_given                  true
% 35.25/4.99  --sup_fun_splitting                     true
% 35.25/4.99  --sup_smt_interval                      50000
% 35.25/4.99  
% 35.25/4.99  ------ Superposition Simplification Setup
% 35.25/4.99  
% 35.25/4.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.25/4.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.25/4.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.25/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.25/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.25/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.25/4.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.25/4.99  --sup_immed_triv                        [TrivRules]
% 35.25/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.25/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.25/4.99  --sup_immed_bw_main                     []
% 35.25/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.25/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.25/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.25/4.99  --sup_input_bw                          []
% 35.25/4.99  
% 35.25/4.99  ------ Combination Options
% 35.25/4.99  
% 35.25/4.99  --comb_res_mult                         3
% 35.25/4.99  --comb_sup_mult                         2
% 35.25/4.99  --comb_inst_mult                        10
% 35.25/4.99  
% 35.25/4.99  ------ Debug Options
% 35.25/4.99  
% 35.25/4.99  --dbg_backtrace                         false
% 35.25/4.99  --dbg_dump_prop_clauses                 false
% 35.25/4.99  --dbg_dump_prop_clauses_file            -
% 35.25/4.99  --dbg_out_stat                          false
% 35.25/4.99  ------ Parsing...
% 35.25/4.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.25/4.99  
% 35.25/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 35.25/4.99  
% 35.25/4.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.25/4.99  
% 35.25/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.25/4.99  ------ Proving...
% 35.25/4.99  ------ Problem Properties 
% 35.25/4.99  
% 35.25/4.99  
% 35.25/4.99  clauses                                 27
% 35.25/4.99  conjectures                             2
% 35.25/4.99  EPR                                     1
% 35.25/4.99  Horn                                    22
% 35.25/4.99  unary                                   13
% 35.25/4.99  binary                                  3
% 35.25/4.99  lits                                    56
% 35.25/4.99  lits eq                                 30
% 35.25/4.99  fd_pure                                 0
% 35.25/4.99  fd_pseudo                               0
% 35.25/4.99  fd_cond                                 0
% 35.25/4.99  fd_pseudo_cond                          9
% 35.25/4.99  AC symbols                              0
% 35.25/4.99  
% 35.25/4.99  ------ Schedule dynamic 5 is on 
% 35.25/4.99  
% 35.25/4.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.25/4.99  
% 35.25/4.99  
% 35.25/4.99  ------ 
% 35.25/4.99  Current options:
% 35.25/4.99  ------ 
% 35.25/4.99  
% 35.25/4.99  ------ Input Options
% 35.25/4.99  
% 35.25/4.99  --out_options                           all
% 35.25/4.99  --tptp_safe_out                         true
% 35.25/4.99  --problem_path                          ""
% 35.25/4.99  --include_path                          ""
% 35.25/4.99  --clausifier                            res/vclausify_rel
% 35.25/4.99  --clausifier_options                    ""
% 35.25/4.99  --stdin                                 false
% 35.25/4.99  --stats_out                             all
% 35.25/4.99  
% 35.25/4.99  ------ General Options
% 35.25/4.99  
% 35.25/4.99  --fof                                   false
% 35.25/4.99  --time_out_real                         305.
% 35.25/4.99  --time_out_virtual                      -1.
% 35.25/4.99  --symbol_type_check                     false
% 35.25/4.99  --clausify_out                          false
% 35.25/4.99  --sig_cnt_out                           false
% 35.25/4.99  --trig_cnt_out                          false
% 35.25/4.99  --trig_cnt_out_tolerance                1.
% 35.25/4.99  --trig_cnt_out_sk_spl                   false
% 35.25/4.99  --abstr_cl_out                          false
% 35.25/4.99  
% 35.25/4.99  ------ Global Options
% 35.25/4.99  
% 35.25/4.99  --schedule                              default
% 35.25/4.99  --add_important_lit                     false
% 35.25/4.99  --prop_solver_per_cl                    1000
% 35.25/4.99  --min_unsat_core                        false
% 35.25/4.99  --soft_assumptions                      false
% 35.25/4.99  --soft_lemma_size                       3
% 35.25/4.99  --prop_impl_unit_size                   0
% 35.25/4.99  --prop_impl_unit                        []
% 35.25/4.99  --share_sel_clauses                     true
% 35.25/4.99  --reset_solvers                         false
% 35.25/4.99  --bc_imp_inh                            [conj_cone]
% 35.25/4.99  --conj_cone_tolerance                   3.
% 35.25/4.99  --extra_neg_conj                        none
% 35.25/4.99  --large_theory_mode                     true
% 35.25/4.99  --prolific_symb_bound                   200
% 35.25/4.99  --lt_threshold                          2000
% 35.25/4.99  --clause_weak_htbl                      true
% 35.25/4.99  --gc_record_bc_elim                     false
% 35.25/4.99  
% 35.25/4.99  ------ Preprocessing Options
% 35.25/4.99  
% 35.25/4.99  --preprocessing_flag                    true
% 35.25/4.99  --time_out_prep_mult                    0.1
% 35.25/4.99  --splitting_mode                        input
% 35.25/4.99  --splitting_grd                         true
% 35.25/4.99  --splitting_cvd                         false
% 35.25/4.99  --splitting_cvd_svl                     false
% 35.25/4.99  --splitting_nvd                         32
% 35.25/4.99  --sub_typing                            true
% 35.25/4.99  --prep_gs_sim                           true
% 35.25/4.99  --prep_unflatten                        true
% 35.25/4.99  --prep_res_sim                          true
% 35.25/4.99  --prep_upred                            true
% 35.25/4.99  --prep_sem_filter                       exhaustive
% 35.25/4.99  --prep_sem_filter_out                   false
% 35.25/4.99  --pred_elim                             true
% 35.25/4.99  --res_sim_input                         true
% 35.25/4.99  --eq_ax_congr_red                       true
% 35.25/4.99  --pure_diseq_elim                       true
% 35.25/4.99  --brand_transform                       false
% 35.25/4.99  --non_eq_to_eq                          false
% 35.25/4.99  --prep_def_merge                        true
% 35.25/4.99  --prep_def_merge_prop_impl              false
% 35.25/4.99  --prep_def_merge_mbd                    true
% 35.25/4.99  --prep_def_merge_tr_red                 false
% 35.25/4.99  --prep_def_merge_tr_cl                  false
% 35.25/4.99  --smt_preprocessing                     true
% 35.25/4.99  --smt_ac_axioms                         fast
% 35.25/4.99  --preprocessed_out                      false
% 35.25/4.99  --preprocessed_stats                    false
% 35.25/4.99  
% 35.25/4.99  ------ Abstraction refinement Options
% 35.25/4.99  
% 35.25/4.99  --abstr_ref                             []
% 35.25/4.99  --abstr_ref_prep                        false
% 35.25/4.99  --abstr_ref_until_sat                   false
% 35.25/4.99  --abstr_ref_sig_restrict                funpre
% 35.25/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.25/4.99  --abstr_ref_under                       []
% 35.25/4.99  
% 35.25/4.99  ------ SAT Options
% 35.25/4.99  
% 35.25/4.99  --sat_mode                              false
% 35.25/4.99  --sat_fm_restart_options                ""
% 35.25/4.99  --sat_gr_def                            false
% 35.25/4.99  --sat_epr_types                         true
% 35.25/4.99  --sat_non_cyclic_types                  false
% 35.25/4.99  --sat_finite_models                     false
% 35.25/4.99  --sat_fm_lemmas                         false
% 35.25/4.99  --sat_fm_prep                           false
% 35.25/4.99  --sat_fm_uc_incr                        true
% 35.25/4.99  --sat_out_model                         small
% 35.25/4.99  --sat_out_clauses                       false
% 35.25/4.99  
% 35.25/4.99  ------ QBF Options
% 35.25/4.99  
% 35.25/4.99  --qbf_mode                              false
% 35.25/4.99  --qbf_elim_univ                         false
% 35.25/4.99  --qbf_dom_inst                          none
% 35.25/4.99  --qbf_dom_pre_inst                      false
% 35.25/4.99  --qbf_sk_in                             false
% 35.25/4.99  --qbf_pred_elim                         true
% 35.25/4.99  --qbf_split                             512
% 35.25/4.99  
% 35.25/4.99  ------ BMC1 Options
% 35.25/4.99  
% 35.25/4.99  --bmc1_incremental                      false
% 35.25/4.99  --bmc1_axioms                           reachable_all
% 35.25/4.99  --bmc1_min_bound                        0
% 35.25/4.99  --bmc1_max_bound                        -1
% 35.25/4.99  --bmc1_max_bound_default                -1
% 35.25/4.99  --bmc1_symbol_reachability              true
% 35.25/4.99  --bmc1_property_lemmas                  false
% 35.25/4.99  --bmc1_k_induction                      false
% 35.25/4.99  --bmc1_non_equiv_states                 false
% 35.25/4.99  --bmc1_deadlock                         false
% 35.25/4.99  --bmc1_ucm                              false
% 35.25/4.99  --bmc1_add_unsat_core                   none
% 35.25/4.99  --bmc1_unsat_core_children              false
% 35.25/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.25/4.99  --bmc1_out_stat                         full
% 35.25/4.99  --bmc1_ground_init                      false
% 35.25/4.99  --bmc1_pre_inst_next_state              false
% 35.25/4.99  --bmc1_pre_inst_state                   false
% 35.25/4.99  --bmc1_pre_inst_reach_state             false
% 35.25/4.99  --bmc1_out_unsat_core                   false
% 35.25/4.99  --bmc1_aig_witness_out                  false
% 35.25/4.99  --bmc1_verbose                          false
% 35.25/4.99  --bmc1_dump_clauses_tptp                false
% 35.25/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.25/4.99  --bmc1_dump_file                        -
% 35.25/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.25/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.25/4.99  --bmc1_ucm_extend_mode                  1
% 35.25/4.99  --bmc1_ucm_init_mode                    2
% 35.25/4.99  --bmc1_ucm_cone_mode                    none
% 35.25/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.25/4.99  --bmc1_ucm_relax_model                  4
% 35.25/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.25/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.25/4.99  --bmc1_ucm_layered_model                none
% 35.25/4.99  --bmc1_ucm_max_lemma_size               10
% 35.25/4.99  
% 35.25/4.99  ------ AIG Options
% 35.25/4.99  
% 35.25/4.99  --aig_mode                              false
% 35.25/4.99  
% 35.25/4.99  ------ Instantiation Options
% 35.25/4.99  
% 35.25/4.99  --instantiation_flag                    true
% 35.25/4.99  --inst_sos_flag                         true
% 35.25/4.99  --inst_sos_phase                        true
% 35.25/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.25/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.25/4.99  --inst_lit_sel_side                     none
% 35.25/4.99  --inst_solver_per_active                1400
% 35.25/4.99  --inst_solver_calls_frac                1.
% 35.25/4.99  --inst_passive_queue_type               priority_queues
% 35.25/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.25/4.99  --inst_passive_queues_freq              [25;2]
% 35.25/4.99  --inst_dismatching                      true
% 35.25/4.99  --inst_eager_unprocessed_to_passive     true
% 35.25/4.99  --inst_prop_sim_given                   true
% 35.25/4.99  --inst_prop_sim_new                     false
% 35.25/4.99  --inst_subs_new                         false
% 35.25/4.99  --inst_eq_res_simp                      false
% 35.25/4.99  --inst_subs_given                       false
% 35.25/4.99  --inst_orphan_elimination               true
% 35.25/4.99  --inst_learning_loop_flag               true
% 35.25/4.99  --inst_learning_start                   3000
% 35.25/4.99  --inst_learning_factor                  2
% 35.25/4.99  --inst_start_prop_sim_after_learn       3
% 35.25/4.99  --inst_sel_renew                        solver
% 35.25/4.99  --inst_lit_activity_flag                true
% 35.25/4.99  --inst_restr_to_given                   false
% 35.25/4.99  --inst_activity_threshold               500
% 35.25/4.99  --inst_out_proof                        true
% 35.25/4.99  
% 35.25/4.99  ------ Resolution Options
% 35.25/4.99  
% 35.25/4.99  --resolution_flag                       false
% 35.25/4.99  --res_lit_sel                           adaptive
% 35.25/4.99  --res_lit_sel_side                      none
% 35.25/4.99  --res_ordering                          kbo
% 35.25/4.99  --res_to_prop_solver                    active
% 35.25/4.99  --res_prop_simpl_new                    false
% 35.25/4.99  --res_prop_simpl_given                  true
% 35.25/4.99  --res_passive_queue_type                priority_queues
% 35.25/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.25/4.99  --res_passive_queues_freq               [15;5]
% 35.25/4.99  --res_forward_subs                      full
% 35.25/4.99  --res_backward_subs                     full
% 35.25/4.99  --res_forward_subs_resolution           true
% 35.25/4.99  --res_backward_subs_resolution          true
% 35.25/4.99  --res_orphan_elimination                true
% 35.25/4.99  --res_time_limit                        2.
% 35.25/4.99  --res_out_proof                         true
% 35.25/4.99  
% 35.25/4.99  ------ Superposition Options
% 35.25/4.99  
% 35.25/4.99  --superposition_flag                    true
% 35.25/4.99  --sup_passive_queue_type                priority_queues
% 35.25/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.25/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.25/4.99  --demod_completeness_check              fast
% 35.25/4.99  --demod_use_ground                      true
% 35.25/4.99  --sup_to_prop_solver                    passive
% 35.25/4.99  --sup_prop_simpl_new                    true
% 35.25/4.99  --sup_prop_simpl_given                  true
% 35.25/4.99  --sup_fun_splitting                     true
% 35.25/4.99  --sup_smt_interval                      50000
% 35.25/4.99  
% 35.25/4.99  ------ Superposition Simplification Setup
% 35.25/4.99  
% 35.25/4.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.25/4.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.25/4.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.25/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.25/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.25/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.25/4.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.25/4.99  --sup_immed_triv                        [TrivRules]
% 35.25/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.25/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.25/4.99  --sup_immed_bw_main                     []
% 35.25/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.25/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.25/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.25/4.99  --sup_input_bw                          []
% 35.25/4.99  
% 35.25/4.99  ------ Combination Options
% 35.25/4.99  
% 35.25/4.99  --comb_res_mult                         3
% 35.25/4.99  --comb_sup_mult                         2
% 35.25/4.99  --comb_inst_mult                        10
% 35.25/4.99  
% 35.25/4.99  ------ Debug Options
% 35.25/4.99  
% 35.25/4.99  --dbg_backtrace                         false
% 35.25/4.99  --dbg_dump_prop_clauses                 false
% 35.25/4.99  --dbg_dump_prop_clauses_file            -
% 35.25/4.99  --dbg_out_stat                          false
% 35.25/4.99  
% 35.25/4.99  
% 35.25/4.99  
% 35.25/4.99  
% 35.25/4.99  ------ Proving...
% 35.25/4.99  
% 35.25/4.99  
% 35.25/4.99  % SZS status Theorem for theBenchmark.p
% 35.25/4.99  
% 35.25/4.99  % SZS output start CNFRefutation for theBenchmark.p
% 35.25/4.99  
% 35.25/4.99  fof(f12,axiom,(
% 35.25/4.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 35.25/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/4.99  
% 35.25/4.99  fof(f25,plain,(
% 35.25/4.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 35.25/4.99    inference(ennf_transformation,[],[f12])).
% 35.25/4.99  
% 35.25/4.99  fof(f32,plain,(
% 35.25/4.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 35.25/4.99    inference(nnf_transformation,[],[f25])).
% 35.25/4.99  
% 35.25/4.99  fof(f33,plain,(
% 35.25/4.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 35.25/4.99    inference(flattening,[],[f32])).
% 35.25/4.99  
% 35.25/4.99  fof(f34,plain,(
% 35.25/4.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 35.25/4.99    inference(rectify,[],[f33])).
% 35.25/4.99  
% 35.25/4.99  fof(f35,plain,(
% 35.25/4.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 35.25/4.99    introduced(choice_axiom,[])).
% 35.25/4.99  
% 35.25/4.99  fof(f36,plain,(
% 35.25/4.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 35.25/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 35.25/4.99  
% 35.25/4.99  fof(f62,plain,(
% 35.25/4.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 35.25/4.99    inference(cnf_transformation,[],[f36])).
% 35.25/4.99  
% 35.25/4.99  fof(f16,axiom,(
% 35.25/4.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.25/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/4.99  
% 35.25/4.99  fof(f73,plain,(
% 35.25/4.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.25/4.99    inference(cnf_transformation,[],[f16])).
% 35.25/4.99  
% 35.25/4.99  fof(f17,axiom,(
% 35.25/4.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 35.25/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/4.99  
% 35.25/4.99  fof(f74,plain,(
% 35.25/4.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 35.25/4.99    inference(cnf_transformation,[],[f17])).
% 35.25/4.99  
% 35.25/4.99  fof(f18,axiom,(
% 35.25/4.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 35.25/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/4.99  
% 35.25/4.99  fof(f75,plain,(
% 35.25/4.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 35.25/4.99    inference(cnf_transformation,[],[f18])).
% 35.25/4.99  
% 35.25/4.99  fof(f19,axiom,(
% 35.25/4.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 35.25/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/4.99  
% 35.25/4.99  fof(f76,plain,(
% 35.25/4.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 35.25/4.99    inference(cnf_transformation,[],[f19])).
% 35.25/4.99  
% 35.25/4.99  fof(f20,axiom,(
% 35.25/4.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 35.25/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/4.99  
% 35.25/4.99  fof(f77,plain,(
% 35.25/4.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 35.25/4.99    inference(cnf_transformation,[],[f20])).
% 35.25/4.99  
% 35.25/4.99  fof(f81,plain,(
% 35.25/4.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 35.25/4.99    inference(definition_unfolding,[],[f76,f77])).
% 35.25/4.99  
% 35.25/4.99  fof(f82,plain,(
% 35.25/4.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 35.25/4.99    inference(definition_unfolding,[],[f75,f81])).
% 35.25/4.99  
% 35.25/4.99  fof(f83,plain,(
% 35.25/4.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 35.25/4.99    inference(definition_unfolding,[],[f74,f82])).
% 35.25/4.99  
% 35.25/4.99  fof(f84,plain,(
% 35.25/4.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 35.25/4.99    inference(definition_unfolding,[],[f73,f83])).
% 35.25/4.99  
% 35.25/4.99  fof(f93,plain,(
% 35.25/4.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 35.25/4.99    inference(definition_unfolding,[],[f62,f84])).
% 35.25/4.99  
% 35.25/4.99  fof(f105,plain,(
% 35.25/4.99    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 35.25/4.99    inference(equality_resolution,[],[f93])).
% 35.25/4.99  
% 35.25/4.99  fof(f106,plain,(
% 35.25/4.99    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 35.25/4.99    inference(equality_resolution,[],[f105])).
% 35.25/4.99  
% 35.25/4.99  fof(f1,axiom,(
% 35.25/4.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.25/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/4.99  
% 35.25/4.99  fof(f43,plain,(
% 35.25/4.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.25/4.99    inference(cnf_transformation,[],[f1])).
% 35.25/4.99  
% 35.25/4.99  fof(f21,conjecture,(
% 35.25/4.99    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 35.25/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/4.99  
% 35.25/4.99  fof(f22,negated_conjecture,(
% 35.25/4.99    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 35.25/4.99    inference(negated_conjecture,[],[f21])).
% 35.25/4.99  
% 35.25/4.99  fof(f26,plain,(
% 35.25/4.99    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 35.25/4.99    inference(ennf_transformation,[],[f22])).
% 35.25/4.99  
% 35.25/4.99  fof(f41,plain,(
% 35.25/4.99    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK3 != sK4 & k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3))),
% 35.25/4.99    introduced(choice_axiom,[])).
% 35.25/4.99  
% 35.25/4.99  fof(f42,plain,(
% 35.25/4.99    sK3 != sK4 & k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3)),
% 35.25/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f41])).
% 35.25/4.99  
% 35.25/4.99  fof(f78,plain,(
% 35.25/4.99    k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3)),
% 35.25/4.99    inference(cnf_transformation,[],[f42])).
% 35.25/4.99  
% 35.25/4.99  fof(f11,axiom,(
% 35.25/4.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 35.25/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/4.99  
% 35.25/4.99  fof(f58,plain,(
% 35.25/4.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 35.25/4.99    inference(cnf_transformation,[],[f11])).
% 35.25/4.99  
% 35.25/4.99  fof(f4,axiom,(
% 35.25/4.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 35.25/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/4.99  
% 35.25/4.99  fof(f51,plain,(
% 35.25/4.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.25/4.99    inference(cnf_transformation,[],[f4])).
% 35.25/4.99  
% 35.25/4.99  fof(f80,plain,(
% 35.25/4.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 35.25/4.99    inference(definition_unfolding,[],[f58,f51])).
% 35.25/4.99  
% 35.25/4.99  fof(f14,axiom,(
% 35.25/4.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 35.25/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/4.99  
% 35.25/4.99  fof(f71,plain,(
% 35.25/4.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 35.25/4.99    inference(cnf_transformation,[],[f14])).
% 35.25/4.99  
% 35.25/4.99  fof(f15,axiom,(
% 35.25/4.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 35.25/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/4.99  
% 35.25/4.99  fof(f72,plain,(
% 35.25/4.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 35.25/4.99    inference(cnf_transformation,[],[f15])).
% 35.25/4.99  
% 35.25/4.99  fof(f85,plain,(
% 35.25/4.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 35.25/4.99    inference(definition_unfolding,[],[f72,f84])).
% 35.25/4.99  
% 35.25/4.99  fof(f86,plain,(
% 35.25/4.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 35.25/4.99    inference(definition_unfolding,[],[f71,f85])).
% 35.25/4.99  
% 35.25/4.99  fof(f101,plain,(
% 35.25/4.99    k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 35.25/4.99    inference(definition_unfolding,[],[f78,f80,f86,f86,f86])).
% 35.25/4.99  
% 35.25/4.99  fof(f5,axiom,(
% 35.25/4.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.25/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/4.99  
% 35.25/4.99  fof(f24,plain,(
% 35.25/4.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.25/4.99    inference(ennf_transformation,[],[f5])).
% 35.25/4.99  
% 35.25/4.99  fof(f52,plain,(
% 35.25/4.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.25/4.99    inference(cnf_transformation,[],[f24])).
% 35.25/4.99  
% 35.25/4.99  fof(f6,axiom,(
% 35.25/4.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 35.25/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/4.99  
% 35.25/4.99  fof(f53,plain,(
% 35.25/4.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 35.25/4.99    inference(cnf_transformation,[],[f6])).
% 35.25/4.99  
% 35.25/4.99  fof(f10,axiom,(
% 35.25/4.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 35.25/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/4.99  
% 35.25/4.99  fof(f57,plain,(
% 35.25/4.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 35.25/4.99    inference(cnf_transformation,[],[f10])).
% 35.25/4.99  
% 35.25/4.99  fof(f7,axiom,(
% 35.25/4.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 35.25/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/5.00  
% 35.25/5.00  fof(f54,plain,(
% 35.25/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 35.25/5.00    inference(cnf_transformation,[],[f7])).
% 35.25/5.00  
% 35.25/5.00  fof(f87,plain,(
% 35.25/5.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))) )),
% 35.25/5.00    inference(definition_unfolding,[],[f54,f51,f51,f80])).
% 35.25/5.00  
% 35.25/5.00  fof(f8,axiom,(
% 35.25/5.00    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 35.25/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/5.00  
% 35.25/5.00  fof(f55,plain,(
% 35.25/5.00    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 35.25/5.00    inference(cnf_transformation,[],[f8])).
% 35.25/5.00  
% 35.25/5.00  fof(f88,plain,(
% 35.25/5.00    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)))) = X0) )),
% 35.25/5.00    inference(definition_unfolding,[],[f55,f80,f51])).
% 35.25/5.00  
% 35.25/5.00  fof(f9,axiom,(
% 35.25/5.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 35.25/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/5.00  
% 35.25/5.00  fof(f56,plain,(
% 35.25/5.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 35.25/5.00    inference(cnf_transformation,[],[f9])).
% 35.25/5.00  
% 35.25/5.00  fof(f3,axiom,(
% 35.25/5.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 35.25/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/5.00  
% 35.25/5.00  fof(f23,plain,(
% 35.25/5.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 35.25/5.00    inference(rectify,[],[f3])).
% 35.25/5.00  
% 35.25/5.00  fof(f50,plain,(
% 35.25/5.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 35.25/5.00    inference(cnf_transformation,[],[f23])).
% 35.25/5.00  
% 35.25/5.00  fof(f2,axiom,(
% 35.25/5.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 35.25/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/5.00  
% 35.25/5.00  fof(f27,plain,(
% 35.25/5.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 35.25/5.00    inference(nnf_transformation,[],[f2])).
% 35.25/5.00  
% 35.25/5.00  fof(f28,plain,(
% 35.25/5.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 35.25/5.00    inference(flattening,[],[f27])).
% 35.25/5.00  
% 35.25/5.00  fof(f29,plain,(
% 35.25/5.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 35.25/5.00    inference(rectify,[],[f28])).
% 35.25/5.00  
% 35.25/5.00  fof(f30,plain,(
% 35.25/5.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 35.25/5.00    introduced(choice_axiom,[])).
% 35.25/5.00  
% 35.25/5.00  fof(f31,plain,(
% 35.25/5.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 35.25/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 35.25/5.00  
% 35.25/5.00  fof(f44,plain,(
% 35.25/5.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 35.25/5.00    inference(cnf_transformation,[],[f31])).
% 35.25/5.00  
% 35.25/5.00  fof(f104,plain,(
% 35.25/5.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 35.25/5.00    inference(equality_resolution,[],[f44])).
% 35.25/5.00  
% 35.25/5.00  fof(f13,axiom,(
% 35.25/5.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 35.25/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/5.00  
% 35.25/5.00  fof(f37,plain,(
% 35.25/5.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 35.25/5.00    inference(nnf_transformation,[],[f13])).
% 35.25/5.00  
% 35.25/5.00  fof(f38,plain,(
% 35.25/5.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 35.25/5.00    inference(rectify,[],[f37])).
% 35.25/5.00  
% 35.25/5.00  fof(f39,plain,(
% 35.25/5.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 35.25/5.00    introduced(choice_axiom,[])).
% 35.25/5.00  
% 35.25/5.00  fof(f40,plain,(
% 35.25/5.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 35.25/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 35.25/5.00  
% 35.25/5.00  fof(f67,plain,(
% 35.25/5.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 35.25/5.00    inference(cnf_transformation,[],[f40])).
% 35.25/5.00  
% 35.25/5.00  fof(f100,plain,(
% 35.25/5.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 35.25/5.00    inference(definition_unfolding,[],[f67,f86])).
% 35.25/5.00  
% 35.25/5.00  fof(f114,plain,(
% 35.25/5.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 35.25/5.00    inference(equality_resolution,[],[f100])).
% 35.25/5.00  
% 35.25/5.00  fof(f68,plain,(
% 35.25/5.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 35.25/5.00    inference(cnf_transformation,[],[f40])).
% 35.25/5.00  
% 35.25/5.00  fof(f99,plain,(
% 35.25/5.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 35.25/5.00    inference(definition_unfolding,[],[f68,f86])).
% 35.25/5.00  
% 35.25/5.00  fof(f112,plain,(
% 35.25/5.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 35.25/5.00    inference(equality_resolution,[],[f99])).
% 35.25/5.00  
% 35.25/5.00  fof(f113,plain,(
% 35.25/5.00    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 35.25/5.00    inference(equality_resolution,[],[f112])).
% 35.25/5.00  
% 35.25/5.00  fof(f79,plain,(
% 35.25/5.00    sK3 != sK4),
% 35.25/5.00    inference(cnf_transformation,[],[f42])).
% 35.25/5.00  
% 35.25/5.00  cnf(c_18,plain,
% 35.25/5.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
% 35.25/5.00      inference(cnf_transformation,[],[f106]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_622,plain,
% 35.25/5.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_0,plain,
% 35.25/5.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 35.25/5.00      inference(cnf_transformation,[],[f43]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_27,negated_conjecture,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 35.25/5.00      inference(cnf_transformation,[],[f101]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_999,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_0,c_27]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_8,plain,
% 35.25/5.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 35.25/5.00      inference(cnf_transformation,[],[f52]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_9,plain,
% 35.25/5.00      ( r1_tarski(k1_xboole_0,X0) ),
% 35.25/5.00      inference(cnf_transformation,[],[f53]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_226,plain,
% 35.25/5.00      ( X0 != X1 | k3_xboole_0(X2,X1) = X2 | k1_xboole_0 != X2 ),
% 35.25/5.00      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_227,plain,
% 35.25/5.00      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 35.25/5.00      inference(unflattening,[status(thm)],[c_226]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1000,plain,
% 35.25/5.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_227,c_0]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_13,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 35.25/5.00      inference(cnf_transformation,[],[f57]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_10,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 35.25/5.00      inference(cnf_transformation,[],[f87]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1392,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0)))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0)))),k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,X2))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_13,c_10]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_34554,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))),k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))),k5_xboole_0(X0,X1))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_1000,c_1392]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_11,plain,
% 35.25/5.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)))) = X0 ),
% 35.25/5.00      inference(cnf_transformation,[],[f88]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1366,plain,
% 35.25/5.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = X0 ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_1000,c_11]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_12,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.25/5.00      inference(cnf_transformation,[],[f56]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1368,plain,
% 35.25/5.00      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_1366,c_12,c_1000]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_7,plain,
% 35.25/5.00      ( k3_xboole_0(X0,X0) = X0 ),
% 35.25/5.00      inference(cnf_transformation,[],[f50]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1347,plain,
% 35.25/5.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))))) = X0 ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_13,c_11]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_5422,plain,
% 35.25/5.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)))),X2)) = k5_xboole_0(X0,X2) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_1347,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_19336,plain,
% 35.25/5.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))),X2))) = k5_xboole_0(X0,X2) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_13,c_5422]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_25594,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,X0),X0)),X1))) = k5_xboole_0(X0,X1) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_7,c_19336]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1397,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)),X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_1000,c_10]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1404,plain,
% 35.25/5.00      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 35.25/5.00      inference(light_normalisation,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_1397,c_7,c_12,c_227,c_1368]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1405,plain,
% 35.25/5.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_1404,c_1368]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_25617,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
% 35.25/5.00      inference(light_normalisation,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_25594,c_12,c_227,c_1405]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26074,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_25617,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26164,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_26074,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26427,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X2),X3)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))),X3)) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_26164,c_26164]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26433,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X2),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_26164,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26555,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_26427,c_26164,c_26433]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_34902,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)),k5_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 35.25/5.00      inference(demodulation,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_34554,c_227,c_1368,c_26555]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_34903,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_34902,c_7,c_12]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_35692,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X1)),X2)) = k5_xboole_0(k1_xboole_0,X2) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_34903,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_35784,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = X2 ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_35692,c_1368,c_26555]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_35785,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_35784,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_39629,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_999,c_35785]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1282,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_999,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1465,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),X1) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_1282,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1607,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),X0)) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_10,c_1465]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1609,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),X1) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_13,c_1465]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1617,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),X1) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_1609,c_1282]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1827,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),X0)) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_1607,c_1282,c_1617]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_25973,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2)))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_13,c_25617]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26268,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_25973,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_35681,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_34903,c_26268]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_35807,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0)))) = k5_xboole_0(X0,k1_xboole_0) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_35681,c_34903]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_35808,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X0))) = X0 ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_35807,c_12]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_40628,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))))),k5_xboole_0(k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)))) = k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),X0) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_1827,c_35808]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1805,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1),X0)))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1),X0)))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1))) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_1617,c_10]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_2818,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k1_xboole_0))),k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k1_xboole_0))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_1000,c_1805]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_2859,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)),k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_2818,c_12]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_2860,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))) = k1_xboole_0 ),
% 35.25/5.00      inference(demodulation,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_2859,c_7,c_227,c_1368,c_1617]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_3801,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))) = k1_xboole_0 ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_1282,c_2860]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_4545,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))) = k1_xboole_0 ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_1282,c_3801]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_4841,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))),k1_xboole_0)) = k1_xboole_0 ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_3801,c_4545]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1619,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),X1)) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,X1)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_1617,c_1465]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_4869,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))) = k1_xboole_0 ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_4841,c_12,c_1282,c_1619]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26075,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),X2)))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_25617,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26163,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_26075,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_28898,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k1_xboole_0))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_4869,c_26163]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1462,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_13,c_1282]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1605,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)),X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),X1) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_1462,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_2057,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)),X1)) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,X1)) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_1605,c_1605,c_1617]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_29427,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1))))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1)) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_2057,c_26268]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_29031,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2)))),X3)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_26163,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_29202,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2)))),X3)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_29031,c_26555]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_29203,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))),X3))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_29202,c_26555]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_29204,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_29203,c_26555]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26434,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),X2)),X3))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_26164,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26857,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))),X3))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_26434,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26858,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_26857,c_26555]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26859,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3))))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_26858,c_26555]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_29205,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
% 35.25/5.00      inference(light_normalisation,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_29204,c_26555,c_26859]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_30194,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1))))))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X1))) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_29427,c_26555,c_29205]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_30195,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1))))))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X1))) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_30194,c_29205]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_30196,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1))))))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X1))) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_30195,c_29205]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_30197,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1)))))))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X1))) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_30196,c_26555]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_30198,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1))))))))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X1))) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_30197,c_1617]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_2061,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0),X1))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,X1)) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_13,c_2057]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_29209,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,X2))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_29205,c_26163]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_29311,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_29209,c_29205]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_29312,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_29311,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_30199,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X1)))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X1))) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_30198,c_2061,c_29312]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_29431,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k1_xboole_0)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_3801,c_26268]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_30180,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),X0)) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),X0)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_29431,c_12,c_29205]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_30181,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),X0)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_30180,c_999]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_30182,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X0))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_30181,c_26555,c_29205]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_30202,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_30199,c_30182]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_31225,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k1_xboole_0))) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_28898,c_30202]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_31226,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0))) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_31225,c_999]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_3818,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k1_xboole_0 ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_2860,c_1282]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_3831,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0 ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_3818,c_999]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26094,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_25617,c_1282]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26145,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_26094,c_1282]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_27474,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_13,c_26145]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_31227,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))))) = k1_xboole_0 ),
% 35.25/5.00      inference(demodulation,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_31226,c_12,c_1282,c_2061,c_3831,c_27474,c_29205]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_2844,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_1805,c_1619]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_2178,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),X1),X2)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,X1)),X2) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_1619,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1614,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),X1),X2)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),X1),X2) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_1465,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1819,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),X1),X2)) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(X0,X1),X2)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_1614,c_1617]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1820,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),X1),X2)) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_1819,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_2181,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,X1)),X2) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_2178,c_1820]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_2845,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_2844,c_1282,c_2181]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_33382,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))),k5_xboole_0(k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))),k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))))),k1_xboole_0))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))))))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_31227,c_2845]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_33395,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))),k5_xboole_0(k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))),k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))))),k1_xboole_0))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k1_xboole_0)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_33382,c_31227]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_4226,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_3831,c_1617]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_4233,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)) = X0 ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_4226,c_1368]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_33396,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)),k5_xboole_0(k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)))),k3_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))))),k1_xboole_0))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 35.25/5.00      inference(demodulation,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_33395,c_12,c_1000,c_2057,c_4233]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_33397,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0),k1_xboole_0)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 35.25/5.00      inference(demodulation,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_33396,c_227,c_1000,c_1368,c_26555]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_33398,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k1_xboole_0))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_33397,c_1617]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_33399,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_33398,c_12]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1386,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_0,c_10]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_9069,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_0,c_1386]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_13051,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_999,c_9069]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_13801,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k1_xboole_0 ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_13051,c_2860]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_34516,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0))),k5_xboole_0(X0,X1))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_1368,c_1392]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_34935,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X1)) = k1_xboole_0 ),
% 35.25/5.00      inference(demodulation,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_34516,c_7,c_12,c_227,c_1000,c_1368,c_26555,c_29205]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_35982,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k5_xboole_0(k1_xboole_0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_13801,c_34935]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_13071,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X0,X1)),k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_9069,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_16702,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_999,c_13071]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_17208,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_13,c_16702]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_17244,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_0,c_17208]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_17278,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_17244,c_12,c_1405,c_1462]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36199,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k1_xboole_0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_35982,c_17278]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36200,plain,
% 35.25/5.00      ( k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_36199,c_1368,c_26555]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36201,plain,
% 35.25/5.00      ( k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k1_xboole_0 ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_36200,c_1617]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_6393,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))))),k1_xboole_0)) = k1_xboole_0 ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_4869,c_4545]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_6412,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0))))) = k1_xboole_0 ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_6393,c_12,c_1282,c_1619]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_13795,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))))) = k1_xboole_0 ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_13051,c_6412]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_17600,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))) = k1_xboole_0 ),
% 35.25/5.00      inference(light_normalisation,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_13795,c_13795,c_17278]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_17629,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k1_xboole_0 ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_17600,c_1282]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_17880,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k1_xboole_0 ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_17629,c_1282]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_35991,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k5_xboole_0(k1_xboole_0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_17880,c_34935]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_29443,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k1_xboole_0)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_17880,c_26268]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_30102,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_29443,c_12,c_29205]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26046,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_13051,c_25617]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26194,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_26046,c_25617]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26195,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 35.25/5.00      inference(light_normalisation,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_26194,c_13051,c_17278]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_30103,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
% 35.25/5.00      inference(light_normalisation,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_30102,c_999,c_26195]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_30104,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_30103,c_26555,c_29205]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_30200,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_30199,c_30104]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36161,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),k5_xboole_0(k1_xboole_0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_35991,c_30200]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36162,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_36161,c_1368,c_26555]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36163,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k1_xboole_0 ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_36162,c_26555]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36164,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) = k1_xboole_0 ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_36163,c_26555]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36165,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))) = k1_xboole_0 ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_36164,c_1617]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36202,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k1_xboole_0)) = k1_xboole_0 ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_36201,c_36165]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36203,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k1_xboole_0 ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_36202,c_12]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_44441,plain,
% 35.25/5.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0))) = X0 ),
% 35.25/5.00      inference(light_normalisation,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_40628,c_7,c_12,c_227,c_1000,c_1368,c_33399,c_36203]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_39794,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_35785,c_35785]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_39964,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = sP0_iProver_split(X1,X2) ),
% 35.25/5.00      inference(splitting,
% 35.25/5.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 35.25/5.00                [c_39794]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_40686,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),X1),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),k1_xboole_0)) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_34903,c_35808]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_40824,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X0),X1),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),k1_xboole_0)))) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_40686,c_26555,c_29205]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36018,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X0),X1),X2)) = k5_xboole_0(k1_xboole_0,X2) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_34935,c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36113,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X0),X1),X2)) = X2 ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_36018,c_1368]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_40825,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(k5_xboole_0(X1,X0),k1_xboole_0)))) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_40824,c_29205,c_36113]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_40826,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),k5_xboole_0(k5_xboole_0(X1,X0),k1_xboole_0)))) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_40825,c_29205]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_40827,plain,
% 35.25/5.00      ( sP0_iProver_split(X0,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0))) = k5_xboole_0(X1,k5_xboole_0(X0,X1)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_40826,c_26555,c_39964]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_40828,plain,
% 35.25/5.00      ( sP0_iProver_split(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X1)),k1_xboole_0))) = k5_xboole_0(X1,k5_xboole_0(X0,X1)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_40827,c_29205]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_40829,plain,
% 35.25/5.00      ( sP0_iProver_split(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)))) = k5_xboole_0(X1,k5_xboole_0(X0,X1)) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_40828,c_26555]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_40830,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = sP0_iProver_split(X1,k1_xboole_0) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_40829,c_12,c_34903]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_44442,plain,
% 35.25/5.00      ( sP0_iProver_split(X0,k1_xboole_0) = X0 ),
% 35.25/5.00      inference(demodulation,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_44441,c_12,c_39964,c_40830]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36052,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k1_xboole_0)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k5_xboole_0(X0,X1)) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_34935,c_26268]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36055,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,X1),X1) ),
% 35.25/5.00      inference(demodulation,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_36052,c_12,c_1368,c_1405,c_29205]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36056,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X0,X1),X0))) = k5_xboole_0(k5_xboole_0(X0,X1),X1) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_36055,c_26555,c_29205]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36057,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X0))) = k5_xboole_0(k5_xboole_0(X0,X1),X1) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_36056,c_1405]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36058,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,X1),X1) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_36057,c_1368,c_29205]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36059,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X0))) = k5_xboole_0(k5_xboole_0(X0,X1),X1) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_36058,c_26555]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_36060,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_36059,c_12,c_34935]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_40695,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),k5_xboole_0(X0,X1)) = X0 ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_36060,c_35808]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_44122,plain,
% 35.25/5.00      ( k5_xboole_0(sP0_iProver_split(X0,k1_xboole_0),k5_xboole_0(X1,X0)) = X1 ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_40695,c_40830]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_40730,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),k5_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),X0)) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_35808,c_35808]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_44054,plain,
% 35.25/5.00      ( k5_xboole_0(k5_xboole_0(sP0_iProver_split(X0,k1_xboole_0),k5_xboole_0(X1,X0)),k5_xboole_0(sP0_iProver_split(X0,k1_xboole_0),X1)) = sP0_iProver_split(X0,k1_xboole_0) ),
% 35.25/5.00      inference(light_normalisation,[status(thm)],[c_40730,c_40830]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_44123,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split(X1,k1_xboole_0),X0)) = sP0_iProver_split(X1,k1_xboole_0) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_44122,c_44054]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_44448,plain,
% 35.25/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_44442,c_44123]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_45916,plain,
% 35.25/5.00      ( k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_39629,c_44448]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_6,plain,
% 35.25/5.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 35.25/5.00      inference(cnf_transformation,[],[f104]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_627,plain,
% 35.25/5.00      ( r2_hidden(X0,X1) = iProver_top
% 35.25/5.00      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_47977,plain,
% 35.25/5.00      ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 35.25/5.00      | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_45916,c_627]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_56319,plain,
% 35.25/5.00      ( r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_622,c_47977]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_25,plain,
% 35.25/5.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 35.25/5.00      inference(cnf_transformation,[],[f114]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_678,plain,
% 35.25/5.00      ( ~ r2_hidden(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 35.25/5.00      | sK4 = X0 ),
% 35.25/5.00      inference(instantiation,[status(thm)],[c_25]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_679,plain,
% 35.25/5.00      ( sK4 = X0
% 35.25/5.00      | r2_hidden(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_681,plain,
% 35.25/5.00      ( sK4 = sK3
% 35.25/5.00      | r2_hidden(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 35.25/5.00      inference(instantiation,[status(thm)],[c_679]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_353,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_657,plain,
% 35.25/5.00      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 35.25/5.00      inference(instantiation,[status(thm)],[c_353]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_658,plain,
% 35.25/5.00      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 35.25/5.00      inference(instantiation,[status(thm)],[c_657]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_24,plain,
% 35.25/5.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 35.25/5.00      inference(cnf_transformation,[],[f113]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_32,plain,
% 35.25/5.00      ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
% 35.25/5.00      inference(instantiation,[status(thm)],[c_24]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_29,plain,
% 35.25/5.00      ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 35.25/5.00      | sK3 = sK3 ),
% 35.25/5.00      inference(instantiation,[status(thm)],[c_25]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26,negated_conjecture,
% 35.25/5.00      ( sK3 != sK4 ),
% 35.25/5.00      inference(cnf_transformation,[],[f79]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(contradiction,plain,
% 35.25/5.00      ( $false ),
% 35.25/5.00      inference(minisat,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_56319,c_681,c_658,c_32,c_29,c_26]) ).
% 35.25/5.00  
% 35.25/5.00  
% 35.25/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.25/5.00  
% 35.25/5.00  ------                               Statistics
% 35.25/5.00  
% 35.25/5.00  ------ General
% 35.25/5.00  
% 35.25/5.00  abstr_ref_over_cycles:                  0
% 35.25/5.00  abstr_ref_under_cycles:                 0
% 35.25/5.00  gc_basic_clause_elim:                   0
% 35.25/5.00  forced_gc_time:                         0
% 35.25/5.00  parsing_time:                           0.009
% 35.25/5.00  unif_index_cands_time:                  0.
% 35.25/5.00  unif_index_add_time:                    0.
% 35.25/5.00  orderings_time:                         0.
% 35.25/5.00  out_proof_time:                         0.027
% 35.25/5.00  total_time:                             4.056
% 35.25/5.00  num_of_symbols:                         43
% 35.25/5.00  num_of_terms:                           119237
% 35.25/5.00  
% 35.25/5.00  ------ Preprocessing
% 35.25/5.00  
% 35.25/5.00  num_of_splits:                          0
% 35.25/5.00  num_of_split_atoms:                     1
% 35.25/5.00  num_of_reused_defs:                     0
% 35.25/5.00  num_eq_ax_congr_red:                    28
% 35.25/5.00  num_of_sem_filtered_clauses:            1
% 35.25/5.00  num_of_subtypes:                        0
% 35.25/5.00  monotx_restored_types:                  0
% 35.25/5.00  sat_num_of_epr_types:                   0
% 35.25/5.00  sat_num_of_non_cyclic_types:            0
% 35.25/5.00  sat_guarded_non_collapsed_types:        0
% 35.25/5.00  num_pure_diseq_elim:                    0
% 35.25/5.00  simp_replaced_by:                       0
% 35.25/5.00  res_preprocessed:                       122
% 35.25/5.00  prep_upred:                             0
% 35.25/5.00  prep_unflattend:                        2
% 35.25/5.00  smt_new_axioms:                         0
% 35.25/5.00  pred_elim_cands:                        1
% 35.25/5.00  pred_elim:                              1
% 35.25/5.00  pred_elim_cl:                           1
% 35.25/5.00  pred_elim_cycles:                       3
% 35.25/5.00  merged_defs:                            0
% 35.25/5.00  merged_defs_ncl:                        0
% 35.25/5.00  bin_hyper_res:                          0
% 35.25/5.00  prep_cycles:                            4
% 35.25/5.00  pred_elim_time:                         0.001
% 35.25/5.00  splitting_time:                         0.
% 35.25/5.00  sem_filter_time:                        0.
% 35.25/5.00  monotx_time:                            0.
% 35.25/5.00  subtype_inf_time:                       0.
% 35.25/5.00  
% 35.25/5.00  ------ Problem properties
% 35.25/5.00  
% 35.25/5.00  clauses:                                27
% 35.25/5.00  conjectures:                            2
% 35.25/5.00  epr:                                    1
% 35.25/5.00  horn:                                   22
% 35.25/5.00  ground:                                 2
% 35.25/5.00  unary:                                  13
% 35.25/5.00  binary:                                 3
% 35.25/5.00  lits:                                   56
% 35.25/5.00  lits_eq:                                30
% 35.25/5.00  fd_pure:                                0
% 35.25/5.00  fd_pseudo:                              0
% 35.25/5.00  fd_cond:                                0
% 35.25/5.00  fd_pseudo_cond:                         9
% 35.25/5.00  ac_symbols:                             1
% 35.25/5.00  
% 35.25/5.00  ------ Propositional Solver
% 35.25/5.00  
% 35.25/5.00  prop_solver_calls:                      34
% 35.25/5.00  prop_fast_solver_calls:                 874
% 35.25/5.00  smt_solver_calls:                       0
% 35.25/5.00  smt_fast_solver_calls:                  0
% 35.25/5.00  prop_num_of_clauses:                    18201
% 35.25/5.00  prop_preprocess_simplified:             32439
% 35.25/5.00  prop_fo_subsumed:                       0
% 35.25/5.00  prop_solver_time:                       0.
% 35.25/5.00  smt_solver_time:                        0.
% 35.25/5.00  smt_fast_solver_time:                   0.
% 35.25/5.00  prop_fast_solver_time:                  0.
% 35.25/5.00  prop_unsat_core_time:                   0.001
% 35.25/5.00  
% 35.25/5.00  ------ QBF
% 35.25/5.00  
% 35.25/5.00  qbf_q_res:                              0
% 35.25/5.00  qbf_num_tautologies:                    0
% 35.25/5.00  qbf_prep_cycles:                        0
% 35.25/5.00  
% 35.25/5.00  ------ BMC1
% 35.25/5.00  
% 35.25/5.00  bmc1_current_bound:                     -1
% 35.25/5.00  bmc1_last_solved_bound:                 -1
% 35.25/5.00  bmc1_unsat_core_size:                   -1
% 35.25/5.00  bmc1_unsat_core_parents_size:           -1
% 35.25/5.00  bmc1_merge_next_fun:                    0
% 35.25/5.00  bmc1_unsat_core_clauses_time:           0.
% 35.25/5.00  
% 35.25/5.00  ------ Instantiation
% 35.25/5.00  
% 35.25/5.00  inst_num_of_clauses:                    4117
% 35.25/5.00  inst_num_in_passive:                    2229
% 35.25/5.00  inst_num_in_active:                     814
% 35.25/5.00  inst_num_in_unprocessed:                1077
% 35.25/5.00  inst_num_of_loops:                      950
% 35.25/5.00  inst_num_of_learning_restarts:          0
% 35.25/5.00  inst_num_moves_active_passive:          135
% 35.25/5.00  inst_lit_activity:                      0
% 35.25/5.00  inst_lit_activity_moves:                1
% 35.25/5.00  inst_num_tautologies:                   0
% 35.25/5.00  inst_num_prop_implied:                  0
% 35.25/5.00  inst_num_existing_simplified:           0
% 35.25/5.00  inst_num_eq_res_simplified:             0
% 35.25/5.00  inst_num_child_elim:                    0
% 35.25/5.00  inst_num_of_dismatching_blockings:      3253
% 35.25/5.00  inst_num_of_non_proper_insts:           3356
% 35.25/5.00  inst_num_of_duplicates:                 0
% 35.25/5.00  inst_inst_num_from_inst_to_res:         0
% 35.25/5.00  inst_dismatching_checking_time:         0.
% 35.25/5.00  
% 35.25/5.00  ------ Resolution
% 35.25/5.00  
% 35.25/5.00  res_num_of_clauses:                     0
% 35.25/5.00  res_num_in_passive:                     0
% 35.25/5.00  res_num_in_active:                      0
% 35.25/5.00  res_num_of_loops:                       126
% 35.25/5.00  res_forward_subset_subsumed:            1104
% 35.25/5.00  res_backward_subset_subsumed:           6
% 35.25/5.00  res_forward_subsumed:                   0
% 35.25/5.00  res_backward_subsumed:                  0
% 35.25/5.00  res_forward_subsumption_resolution:     0
% 35.25/5.00  res_backward_subsumption_resolution:    0
% 35.25/5.00  res_clause_to_clause_subsumption:       42176
% 35.25/5.00  res_orphan_elimination:                 0
% 35.25/5.00  res_tautology_del:                      25
% 35.25/5.00  res_num_eq_res_simplified:              0
% 35.25/5.00  res_num_sel_changes:                    0
% 35.25/5.00  res_moves_from_active_to_pass:          0
% 35.25/5.00  
% 35.25/5.00  ------ Superposition
% 35.25/5.00  
% 35.25/5.00  sup_time_total:                         0.
% 35.25/5.00  sup_time_generating:                    0.
% 35.25/5.00  sup_time_sim_full:                      0.
% 35.25/5.00  sup_time_sim_immed:                     0.
% 35.25/5.00  
% 35.25/5.00  sup_num_of_clauses:                     2711
% 35.25/5.00  sup_num_in_active:                      45
% 35.25/5.00  sup_num_in_passive:                     2666
% 35.25/5.00  sup_num_of_loops:                       189
% 35.25/5.00  sup_fw_superposition:                   6339
% 35.25/5.00  sup_bw_superposition:                   3667
% 35.25/5.00  sup_immediate_simplified:               6750
% 35.25/5.00  sup_given_eliminated:                   13
% 35.25/5.00  comparisons_done:                       0
% 35.25/5.00  comparisons_avoided:                    8
% 35.25/5.00  
% 35.25/5.00  ------ Simplifications
% 35.25/5.00  
% 35.25/5.00  
% 35.25/5.00  sim_fw_subset_subsumed:                 0
% 35.25/5.00  sim_bw_subset_subsumed:                 0
% 35.25/5.00  sim_fw_subsumed:                        432
% 35.25/5.00  sim_bw_subsumed:                        63
% 35.25/5.00  sim_fw_subsumption_res:                 0
% 35.25/5.00  sim_bw_subsumption_res:                 0
% 35.25/5.00  sim_tautology_del:                      14
% 35.25/5.00  sim_eq_tautology_del:                   1888
% 35.25/5.00  sim_eq_res_simp:                        2
% 35.25/5.00  sim_fw_demodulated:                     10470
% 35.25/5.00  sim_bw_demodulated:                     1090
% 35.25/5.00  sim_light_normalised:                   3449
% 35.25/5.00  sim_joinable_taut:                      11
% 35.25/5.00  sim_joinable_simp:                      0
% 35.25/5.00  sim_ac_normalised:                      0
% 35.25/5.00  sim_smt_subsumption:                    0
% 35.25/5.00  
%------------------------------------------------------------------------------
