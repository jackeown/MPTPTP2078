%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:02 EST 2020

% Result     : Theorem 11.78s
% Output     : CNFRefutation 11.78s
% Verified   : 
% Statistics : Number of formulae       :  270 (1031105 expanded)
%              Number of clauses        :  196 (289570 expanded)
%              Number of leaves         :   27 (298313 expanded)
%              Depth                    :   58
%              Number of atoms          :  424 (1047425 expanded)
%              Number of equality atoms :  346 (1047325 expanded)
%              Maximal formula depth    :   13 (   2 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

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

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f70])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f71])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f72])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f73])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f61,f74])).

fof(f86,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f69,f52,f75])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f68,f52,f74])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f47,f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f54,f73])).

fof(f91,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f92,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f91])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f73])).

fof(f93,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f84])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_315,negated_conjecture,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_21,c_10,c_1])).

cnf(c_1067,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_0,c_315])).

cnf(c_1216,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1067,c_10])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1149,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_1222,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1216,c_1149])).

cnf(c_1486,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_1222])).

cnf(c_1607,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_1486])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1487,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11,c_1222])).

cnf(c_1491,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_1487,c_8])).

cnf(c_1495,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1491,c_1222])).

cnf(c_2599,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1607,c_1495])).

cnf(c_559,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_560,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_10976,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1495,c_560])).

cnf(c_11969,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(sK3,X2)) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_559,c_10976])).

cnf(c_1503,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1495,c_10])).

cnf(c_1785,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11,c_1503])).

cnf(c_1805,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = sK3 ),
    inference(demodulation,[status(thm)],[c_1785,c_8])).

cnf(c_2120,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),X0) = sK3 ),
    inference(superposition,[status(thm)],[c_1495,c_1805])).

cnf(c_2454,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_2120,c_10])).

cnf(c_5064,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_2454,c_1])).

cnf(c_31551,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(sK3,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))) = k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_11969,c_5064])).

cnf(c_12029,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X1,k5_xboole_0(sK3,X2))) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_10976,c_559])).

cnf(c_1497,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,sK3)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_1495])).

cnf(c_2121,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),X0) = sK3 ),
    inference(superposition,[status(thm)],[c_1497,c_1805])).

cnf(c_1618,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,sK3))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_10,c_1497])).

cnf(c_2924,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,sK3),sK3),X0) = k5_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_2121,c_1618])).

cnf(c_2942,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,sK3),sK3),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2924,c_11])).

cnf(c_3977,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK3,X0),sK3),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_2942])).

cnf(c_5937,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK3,X0),sK3),k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3977,c_559])).

cnf(c_1781,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_1503])).

cnf(c_6010,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))) = k5_xboole_0(k5_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_559,c_1781])).

cnf(c_4232,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10,c_1781])).

cnf(c_6024,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_6010,c_4232])).

cnf(c_6150,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,sK3),k5_xboole_0(k5_xboole_0(X0,X1),X1)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5937,c_6024])).

cnf(c_6151,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),sK3)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6150,c_6024])).

cnf(c_6152,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X0))) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6151,c_6024])).

cnf(c_6153,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK3,X1),X1))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6152,c_6024])).

cnf(c_6004,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK3,X1),X2))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_559,c_1503])).

cnf(c_6053,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,sK3)))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_6004,c_6024])).

cnf(c_6154,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6153,c_6024,c_6053])).

cnf(c_6155,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_6154,c_8])).

cnf(c_6614,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X0))) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_6155,c_1503])).

cnf(c_15361,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,k5_xboole_0(X0,X1))) = k5_xboole_0(sK3,k5_xboole_0(sK3,X1)) ),
    inference(superposition,[status(thm)],[c_12029,c_6614])).

cnf(c_15383,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,k5_xboole_0(X0,X1))) = X1 ),
    inference(demodulation,[status(thm)],[c_15361,c_1495,c_10976])).

cnf(c_15807,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X0)),k5_xboole_0(sK3,k5_xboole_0(X1,k5_xboole_0(X2,X0)))) = k5_xboole_0(X1,k5_xboole_0(sK3,X2)) ),
    inference(superposition,[status(thm)],[c_12029,c_15383])).

cnf(c_15884,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(X1,k5_xboole_0(X2,X0)))) = k5_xboole_0(X1,k5_xboole_0(sK3,X2)) ),
    inference(light_normalisation,[status(thm)],[c_15807,c_1495])).

cnf(c_16120,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(sK3,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X3))))) = k5_xboole_0(X2,k5_xboole_0(sK3,k5_xboole_0(sK3,X3))) ),
    inference(superposition,[status(thm)],[c_12029,c_15884])).

cnf(c_15343,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(sK3,X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_12029,c_1])).

cnf(c_16254,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(sK3,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X3))))) = k5_xboole_0(X2,X3) ),
    inference(demodulation,[status(thm)],[c_16120,c_1495,c_15343])).

cnf(c_24291,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(sK3,X1))),k5_xboole_0(sK3,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X4,X1)))))) = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(sK3,X4))) ),
    inference(superposition,[status(thm)],[c_12029,c_16254])).

cnf(c_16111,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,k5_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(sK3,k5_xboole_0(sK3,X0))) ),
    inference(superposition,[status(thm)],[c_15383,c_15884])).

cnf(c_16262,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,k5_xboole_0(X2,X1))) = k5_xboole_0(X2,X0) ),
    inference(light_normalisation,[status(thm)],[c_16111,c_1495])).

cnf(c_17155,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,k5_xboole_0(X2,k5_xboole_0(sK3,k5_xboole_0(X0,X3))))) = k5_xboole_0(X2,k5_xboole_0(sK3,k5_xboole_0(X1,X3))) ),
    inference(superposition,[status(thm)],[c_16262,c_16262])).

cnf(c_11069,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_560,c_1503])).

cnf(c_2932,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1618,c_10])).

cnf(c_2939,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_2932,c_10])).

cnf(c_11101,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_11069,c_2939])).

cnf(c_11073,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_560,c_1503])).

cnf(c_13812,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(X1,X2)))) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_559,c_11073])).

cnf(c_561,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_14041,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_561,c_11969])).

cnf(c_17261,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,k5_xboole_0(X2,k5_xboole_0(X0,X3)))) = k5_xboole_0(X3,k5_xboole_0(sK3,k5_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_17155,c_11101,c_13812,c_14041])).

cnf(c_24446,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(sK3,k5_xboole_0(X2,X3))) = k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) ),
    inference(demodulation,[status(thm)],[c_24291,c_1495,c_15343,c_17261])).

cnf(c_26814,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))),k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X3,X0),X4))) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),k5_xboole_0(sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_24446,c_24446])).

cnf(c_14081,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))),k5_xboole_0(sK3,X3)) = k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_561,c_11969])).

cnf(c_24354,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(sK3,sK3)),k5_xboole_0(sK3,k5_xboole_0(X2,k5_xboole_0(X3,X4)))) = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X1,X4)))) ),
    inference(superposition,[status(thm)],[c_16254,c_16254])).

cnf(c_11970,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(sK3,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_560,c_10976])).

cnf(c_24358,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X4)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X4,k5_xboole_0(X3,X2)))) ),
    inference(demodulation,[status(thm)],[c_24354,c_11970,c_15343])).

cnf(c_26907,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X3,X4))) = k5_xboole_0(X2,k5_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(sK3,k5_xboole_0(sK3,X1))))) ),
    inference(demodulation,[status(thm)],[c_26814,c_11101,c_14081,c_24358])).

cnf(c_26908,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X3,X4))) = k5_xboole_0(X2,k5_xboole_0(X4,k5_xboole_0(X3,X1))) ),
    inference(demodulation,[status(thm)],[c_26907,c_1495,c_24358])).

cnf(c_31636,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X2,X3))) = k5_xboole_0(X1,k5_xboole_0(X3,k5_xboole_0(X2,sK3))) ),
    inference(superposition,[status(thm)],[c_5064,c_26908])).

cnf(c_16013,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(sK3,X1)) ),
    inference(superposition,[status(thm)],[c_11073,c_15884])).

cnf(c_26742,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))),k5_xboole_0(sK3,sK3)) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) ),
    inference(superposition,[status(thm)],[c_2120,c_24446])).

cnf(c_5928,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X1,X0)) = k5_xboole_0(X1,sK3) ),
    inference(superposition,[status(thm)],[c_2120,c_559])).

cnf(c_7404,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))),k5_xboole_0(X1,X0)) = k5_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_1781,c_5928])).

cnf(c_2925,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_1618])).

cnf(c_7472,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k5_xboole_0(sK3,sK3) ),
    inference(light_normalisation,[status(thm)],[c_7404,c_2925])).

cnf(c_7473,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7472,c_11,c_6024])).

cnf(c_17140,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))),k5_xboole_0(sK3,k5_xboole_0(sK3,X1))) = k5_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_6614,c_16262])).

cnf(c_14145,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_11969,c_561])).

cnf(c_17280,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(sK3,k5_xboole_0(sK3,X1))) = k5_xboole_0(X2,X0) ),
    inference(light_normalisation,[status(thm)],[c_17140,c_14145])).

cnf(c_17281,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_17280,c_1495,c_11101])).

cnf(c_18344,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7473,c_17281])).

cnf(c_18469,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_18344,c_11101])).

cnf(c_26994,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))) = k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_26742,c_11,c_14081,c_18469])).

cnf(c_16997,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(X1,X0))) = k5_xboole_0(X1,sK3) ),
    inference(superposition,[status(thm)],[c_1495,c_16262])).

cnf(c_17996,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(sK3,k5_xboole_0(sK3,X0))) = k5_xboole_0(X1,sK3) ),
    inference(superposition,[status(thm)],[c_6614,c_16997])).

cnf(c_18150,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X0) = k5_xboole_0(X1,sK3) ),
    inference(light_normalisation,[status(thm)],[c_17996,c_1495])).

cnf(c_29168,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X2)),k5_xboole_0(X3,X4)),k5_xboole_0(X2,sK3)) = k5_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X0,X3))) ),
    inference(superposition,[status(thm)],[c_18150,c_26908])).

cnf(c_14099,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(X2,sK3)) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_11969])).

cnf(c_29637,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X3,k5_xboole_0(X4,X0)))) = k5_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(X1,X4))) ),
    inference(demodulation,[status(thm)],[c_29168,c_14099,c_24358])).

cnf(c_26646,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X1,X2),X3))) = k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(sK3,X2)))) ),
    inference(superposition,[status(thm)],[c_5928,c_24446])).

cnf(c_27083,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X0)) ),
    inference(demodulation,[status(thm)],[c_26646,c_1495,c_11101,c_11970])).

cnf(c_28173,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)),k1_xboole_0) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X2,X1),X0)) ),
    inference(superposition,[status(thm)],[c_7473,c_27083])).

cnf(c_28422,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X3,X2))) ),
    inference(demodulation,[status(thm)],[c_28173,c_11101,c_18469])).

cnf(c_29638,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,X0),X4)))) = k5_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_29637,c_28422])).

cnf(c_28231,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3)))) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_27083,c_561])).

cnf(c_29639,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X0))) ),
    inference(demodulation,[status(thm)],[c_29638,c_11101,c_28231])).

cnf(c_20,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_316,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(theory_normalisation,[status(thm)],[c_20,c_10,c_1])).

cnf(c_1501,plain,
    ( k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = k5_xboole_0(X0,k3_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_316,c_1495])).

cnf(c_2006,plain,
    ( k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = k5_xboole_0(X0,k3_xboole_0(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_0,c_1501])).

cnf(c_9829,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)) = k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) ),
    inference(superposition,[status(thm)],[c_2006,c_1495])).

cnf(c_9924,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X0,sK3)))) = k5_xboole_0(X0,k3_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_9829,c_1501])).

cnf(c_26582,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK3,X0)),k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1))) = k5_xboole_0(X1,k5_xboole_0(sK3,k5_xboole_0(sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_9924,c_24446])).

cnf(c_9921,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) = k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(sK3,X0))) ),
    inference(superposition,[status(thm)],[c_9829,c_316])).

cnf(c_12732,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X0,sK3))),X1)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK3,X0)),X1) ),
    inference(superposition,[status(thm)],[c_9921,c_1503])).

cnf(c_9819,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK3)) = k5_xboole_0(X0,k3_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_2006,c_1501])).

cnf(c_10383,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sK3),X1)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK3,X0)),X1) ),
    inference(superposition,[status(thm)],[c_9819,c_10])).

cnf(c_12739,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X0,sK3))),X1)) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sK3),X1)) ),
    inference(light_normalisation,[status(thm)],[c_12732,c_10383])).

cnf(c_12740,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sK3),X1)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1) ),
    inference(demodulation,[status(thm)],[c_12739,c_1503,c_2925,c_11101])).

cnf(c_27164,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK3,X0)),k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sK3),X1)))) = k5_xboole_0(X1,k5_xboole_0(sK3,k5_xboole_0(sK3,sK3))) ),
    inference(light_normalisation,[status(thm)],[c_26582,c_12740])).

cnf(c_24212,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,sK3)),k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK3,X1))))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,sK3))) ),
    inference(superposition,[status(thm)],[c_9924,c_16254])).

cnf(c_6011,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(X0,X1))) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_559,c_1781])).

cnf(c_24552,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,sK3))) = k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(sK3,X1)),X0) ),
    inference(demodulation,[status(thm)],[c_24212,c_1495,c_6011,c_14041])).

cnf(c_24964,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,sK3))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK3,X0)),X1) ),
    inference(superposition,[status(thm)],[c_24552,c_559])).

cnf(c_27165,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK3,X0)),k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sK3),X1)))) = k5_xboole_0(X1,sK3) ),
    inference(demodulation,[status(thm)],[c_27164,c_1495,c_24964])).

cnf(c_30037,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,sK3)),k5_xboole_0(k3_xboole_0(sK3,sK3),X0)) = k5_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_1495,c_27165])).

cnf(c_30830,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK3,sK3),X0),k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK3))))) = k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X0,sK3)),k5_xboole_0(X3,k5_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_30037,c_26908])).

cnf(c_29084,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(sK3,X0)))) = k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(sK3,X1)),k5_xboole_0(X4,k5_xboole_0(X3,X2))) ),
    inference(superposition,[status(thm)],[c_2454,c_26908])).

cnf(c_29192,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X3,X4))) = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,X1))) ),
    inference(superposition,[status(thm)],[c_1,c_26908])).

cnf(c_29740,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(sK3,X0)))) = k5_xboole_0(X1,k5_xboole_0(X3,k5_xboole_0(X2,sK3))) ),
    inference(demodulation,[status(thm)],[c_29084,c_29192,c_29639])).

cnf(c_30117,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sK3),X1))),k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X0,k3_xboole_0(sK3,X0))))) = k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X1,sK3)),k5_xboole_0(X4,k5_xboole_0(X3,X2))) ),
    inference(superposition,[status(thm)],[c_27165,c_26908])).

cnf(c_30223,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(X0,k5_xboole_0(X2,X3))) = sP0_iProver_split(X1,X2,X3) ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_30117])).

cnf(c_30918,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,sK3))) = sP0_iProver_split(X0,X1,X2) ),
    inference(demodulation,[status(thm)],[c_30830,c_29740,c_30223])).

cnf(c_31727,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X2)) = sP0_iProver_split(X1,X0,X2) ),
    inference(demodulation,[status(thm)],[c_31636,c_16013,c_26994,c_29639,c_30918])).

cnf(c_31645,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)),k5_xboole_0(sK3,X2)) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(sK3,X1),X0)) ),
    inference(superposition,[status(thm)],[c_5064,c_27083])).

cnf(c_17138,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,X2))),k5_xboole_0(sK3,k5_xboole_0(X1,sK3))) = k5_xboole_0(k5_xboole_0(sK3,X2),X0) ),
    inference(superposition,[status(thm)],[c_5928,c_16262])).

cnf(c_17284,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(sK3,X1)) = k5_xboole_0(X2,k5_xboole_0(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_17138,c_6155,c_11101,c_14041])).

cnf(c_18341,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK3,X0),X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,k5_xboole_0(sK3,X2)) ),
    inference(superposition,[status(thm)],[c_10976,c_17281])).

cnf(c_16036,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(sK3,k5_xboole_0(X1,X0))) = k5_xboole_0(sK3,k5_xboole_0(sK3,X1)) ),
    inference(superposition,[status(thm)],[c_1618,c_15884])).

cnf(c_6584,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),sK3) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2942,c_6155])).

cnf(c_6628,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),sK3) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6584,c_8])).

cnf(c_8670,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(sK3,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6628,c_10])).

cnf(c_16327,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(sK3,k5_xboole_0(X1,X0))) = X1 ),
    inference(demodulation,[status(thm)],[c_16036,c_1495,c_8670])).

cnf(c_16828,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X1,sK3),X2)) = k5_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_16327,c_560])).

cnf(c_16868,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_16828,c_11101,c_14041])).

cnf(c_18471,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),X1) = k5_xboole_0(X0,k5_xboole_0(sK3,X1)) ),
    inference(demodulation,[status(thm)],[c_18341,c_11101,c_16868])).

cnf(c_31724,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(sK3,X2))) ),
    inference(demodulation,[status(thm)],[c_31645,c_11101,c_17284,c_18471,c_24358])).

cnf(c_31728,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))) = sP0_iProver_split(X0,X1,X2) ),
    inference(demodulation,[status(thm)],[c_31727,c_31724])).

cnf(c_31631,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(k5_xboole_0(X2,X1),X3)) = k5_xboole_0(k5_xboole_0(sK3,X2),k5_xboole_0(X3,X0)) ),
    inference(superposition,[status(thm)],[c_5064,c_27083])).

cnf(c_10997,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_6614,c_560])).

cnf(c_31731,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X2)) ),
    inference(demodulation,[status(thm)],[c_31631,c_10997,c_11101,c_24358,c_26994])).

cnf(c_31815,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),sP0_iProver_split(sK3,X1,X2)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_31551,c_31728,c_31731])).

cnf(c_31688,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X0)),k5_xboole_0(sK3,k5_xboole_0(sK3,X1))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X2),X1),X2) ),
    inference(superposition,[status(thm)],[c_5064,c_16254])).

cnf(c_31696,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),X1) = k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(sK3,X2))) ),
    inference(light_normalisation,[status(thm)],[c_31688,c_1495])).

cnf(c_6593,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_6155,c_6155])).

cnf(c_17127,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X1,sK3))),k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1))))) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2006,c_16262])).

cnf(c_17295,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,sK3)),k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1)))) = k5_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_17127,c_1495,c_11101,c_14041])).

cnf(c_31064,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,sK3)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X2)))) = k5_xboole_0(k5_xboole_0(X2,X1),k5_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_17295,c_11969])).

cnf(c_31092,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,sK3),k5_xboole_0(X2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1))))) = k5_xboole_0(X2,k5_xboole_0(sK3,k5_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_31064,c_11101,c_29639])).

cnf(c_17983,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK3),k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))))) = k5_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_2006,c_16997])).

cnf(c_18161,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = k5_xboole_0(X0,sK3) ),
    inference(demodulation,[status(thm)],[c_17983,c_1495])).

cnf(c_21514,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK3),k5_xboole_0(X1,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)))) = k5_xboole_0(X1,k5_xboole_0(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_18161,c_559])).

cnf(c_31093,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(X1,X2))) = sP0_iProver_split(X1,X0,X2) ),
    inference(demodulation,[status(thm)],[c_31092,c_21514,c_30918])).

cnf(c_31697,plain,
    ( sP0_iProver_split(sK3,X0,X1) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_31696,c_6593,c_11101,c_31093])).

cnf(c_31816,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X2)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_31815,c_31697])).

cnf(c_31817,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X2)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_31816,c_1495])).

cnf(c_33197,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_2599,c_31817])).

cnf(c_7,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_540,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2319,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_540])).

cnf(c_3843,plain,
    ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1491,c_2319])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_542,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_31454,plain,
    ( k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_3843,c_542])).

cnf(c_33570,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_33197,c_31454])).

cnf(c_7383,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,sK3) ),
    inference(superposition,[status(thm)],[c_1,c_5928])).

cnf(c_33571,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_33570,c_11,c_7383])).

cnf(c_319,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_652,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3
    | k3_xboole_0(X4,k1_xboole_0) != X3
    | k3_xboole_0(X4,k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_749,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != k1_xboole_0
    | k3_xboole_0(X3,k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)
    | k3_xboole_0(X3,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_750,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0
    | k3_xboole_0(sK2,k1_xboole_0) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k3_xboole_0(sK2,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_322,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_566,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k3_xboole_0(X3,k1_xboole_0))
    | X2 != X0
    | k3_xboole_0(X3,k1_xboole_0) != X1 ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_578,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
    | r2_hidden(X3,k3_xboole_0(X4,k1_xboole_0))
    | X3 != X0
    | k3_xboole_0(X4,k1_xboole_0) != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_580,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK2,k3_xboole_0(sK2,k1_xboole_0))
    | k3_xboole_0(sK2,k1_xboole_0) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_200,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_201,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_203,plain,
    ( ~ r2_hidden(sK2,k3_xboole_0(sK2,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_5,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_51,plain,
    ( k3_xboole_0(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_18,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_27,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_24,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33571,c_750,c_580,c_203,c_51,c_27,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n020.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:24:37 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 11.78/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.78/1.99  
% 11.78/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.78/1.99  
% 11.78/1.99  ------  iProver source info
% 11.78/1.99  
% 11.78/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.78/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.78/1.99  git: non_committed_changes: false
% 11.78/1.99  git: last_make_outside_of_git: false
% 11.78/1.99  
% 11.78/1.99  ------ 
% 11.78/1.99  
% 11.78/1.99  ------ Input Options
% 11.78/1.99  
% 11.78/1.99  --out_options                           all
% 11.78/1.99  --tptp_safe_out                         true
% 11.78/1.99  --problem_path                          ""
% 11.78/1.99  --include_path                          ""
% 11.78/1.99  --clausifier                            res/vclausify_rel
% 11.78/1.99  --clausifier_options                    ""
% 11.78/1.99  --stdin                                 false
% 11.78/1.99  --stats_out                             all
% 11.78/1.99  
% 11.78/1.99  ------ General Options
% 11.78/1.99  
% 11.78/1.99  --fof                                   false
% 11.78/1.99  --time_out_real                         305.
% 11.78/1.99  --time_out_virtual                      -1.
% 11.78/1.99  --symbol_type_check                     false
% 11.78/1.99  --clausify_out                          false
% 11.78/1.99  --sig_cnt_out                           false
% 11.78/1.99  --trig_cnt_out                          false
% 11.78/1.99  --trig_cnt_out_tolerance                1.
% 11.78/1.99  --trig_cnt_out_sk_spl                   false
% 11.78/1.99  --abstr_cl_out                          false
% 11.78/1.99  
% 11.78/1.99  ------ Global Options
% 11.78/1.99  
% 11.78/1.99  --schedule                              default
% 11.78/1.99  --add_important_lit                     false
% 11.78/1.99  --prop_solver_per_cl                    1000
% 11.78/1.99  --min_unsat_core                        false
% 11.78/1.99  --soft_assumptions                      false
% 11.78/1.99  --soft_lemma_size                       3
% 11.78/1.99  --prop_impl_unit_size                   0
% 11.78/1.99  --prop_impl_unit                        []
% 11.78/1.99  --share_sel_clauses                     true
% 11.78/1.99  --reset_solvers                         false
% 11.78/1.99  --bc_imp_inh                            [conj_cone]
% 11.78/1.99  --conj_cone_tolerance                   3.
% 11.78/1.99  --extra_neg_conj                        none
% 11.78/1.99  --large_theory_mode                     true
% 11.78/1.99  --prolific_symb_bound                   200
% 11.78/1.99  --lt_threshold                          2000
% 11.78/1.99  --clause_weak_htbl                      true
% 11.78/1.99  --gc_record_bc_elim                     false
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing Options
% 11.78/1.99  
% 11.78/1.99  --preprocessing_flag                    true
% 11.78/1.99  --time_out_prep_mult                    0.1
% 11.78/1.99  --splitting_mode                        input
% 11.78/1.99  --splitting_grd                         true
% 11.78/1.99  --splitting_cvd                         false
% 11.78/1.99  --splitting_cvd_svl                     false
% 11.78/1.99  --splitting_nvd                         32
% 11.78/1.99  --sub_typing                            true
% 11.78/1.99  --prep_gs_sim                           true
% 11.78/1.99  --prep_unflatten                        true
% 11.78/1.99  --prep_res_sim                          true
% 11.78/1.99  --prep_upred                            true
% 11.78/1.99  --prep_sem_filter                       exhaustive
% 11.78/1.99  --prep_sem_filter_out                   false
% 11.78/1.99  --pred_elim                             true
% 11.78/1.99  --res_sim_input                         true
% 11.78/1.99  --eq_ax_congr_red                       true
% 11.78/1.99  --pure_diseq_elim                       true
% 11.78/1.99  --brand_transform                       false
% 11.78/1.99  --non_eq_to_eq                          false
% 11.78/1.99  --prep_def_merge                        true
% 11.78/1.99  --prep_def_merge_prop_impl              false
% 11.78/1.99  --prep_def_merge_mbd                    true
% 11.78/1.99  --prep_def_merge_tr_red                 false
% 11.78/1.99  --prep_def_merge_tr_cl                  false
% 11.78/1.99  --smt_preprocessing                     true
% 11.78/1.99  --smt_ac_axioms                         fast
% 11.78/1.99  --preprocessed_out                      false
% 11.78/1.99  --preprocessed_stats                    false
% 11.78/1.99  
% 11.78/1.99  ------ Abstraction refinement Options
% 11.78/1.99  
% 11.78/1.99  --abstr_ref                             []
% 11.78/1.99  --abstr_ref_prep                        false
% 11.78/1.99  --abstr_ref_until_sat                   false
% 11.78/1.99  --abstr_ref_sig_restrict                funpre
% 11.78/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.78/1.99  --abstr_ref_under                       []
% 11.78/1.99  
% 11.78/1.99  ------ SAT Options
% 11.78/1.99  
% 11.78/1.99  --sat_mode                              false
% 11.78/1.99  --sat_fm_restart_options                ""
% 11.78/1.99  --sat_gr_def                            false
% 11.78/1.99  --sat_epr_types                         true
% 11.78/1.99  --sat_non_cyclic_types                  false
% 11.78/1.99  --sat_finite_models                     false
% 11.78/1.99  --sat_fm_lemmas                         false
% 11.78/1.99  --sat_fm_prep                           false
% 11.78/1.99  --sat_fm_uc_incr                        true
% 11.78/1.99  --sat_out_model                         small
% 11.78/1.99  --sat_out_clauses                       false
% 11.78/1.99  
% 11.78/1.99  ------ QBF Options
% 11.78/1.99  
% 11.78/1.99  --qbf_mode                              false
% 11.78/1.99  --qbf_elim_univ                         false
% 11.78/1.99  --qbf_dom_inst                          none
% 11.78/1.99  --qbf_dom_pre_inst                      false
% 11.78/1.99  --qbf_sk_in                             false
% 11.78/1.99  --qbf_pred_elim                         true
% 11.78/1.99  --qbf_split                             512
% 11.78/1.99  
% 11.78/1.99  ------ BMC1 Options
% 11.78/1.99  
% 11.78/1.99  --bmc1_incremental                      false
% 11.78/1.99  --bmc1_axioms                           reachable_all
% 11.78/1.99  --bmc1_min_bound                        0
% 11.78/1.99  --bmc1_max_bound                        -1
% 11.78/1.99  --bmc1_max_bound_default                -1
% 11.78/1.99  --bmc1_symbol_reachability              true
% 11.78/1.99  --bmc1_property_lemmas                  false
% 11.78/1.99  --bmc1_k_induction                      false
% 11.78/1.99  --bmc1_non_equiv_states                 false
% 11.78/1.99  --bmc1_deadlock                         false
% 11.78/1.99  --bmc1_ucm                              false
% 11.78/1.99  --bmc1_add_unsat_core                   none
% 11.78/1.99  --bmc1_unsat_core_children              false
% 11.78/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.78/1.99  --bmc1_out_stat                         full
% 11.78/1.99  --bmc1_ground_init                      false
% 11.78/1.99  --bmc1_pre_inst_next_state              false
% 11.78/1.99  --bmc1_pre_inst_state                   false
% 11.78/1.99  --bmc1_pre_inst_reach_state             false
% 11.78/1.99  --bmc1_out_unsat_core                   false
% 11.78/1.99  --bmc1_aig_witness_out                  false
% 11.78/1.99  --bmc1_verbose                          false
% 11.78/1.99  --bmc1_dump_clauses_tptp                false
% 11.78/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.78/1.99  --bmc1_dump_file                        -
% 11.78/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.78/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.78/1.99  --bmc1_ucm_extend_mode                  1
% 11.78/1.99  --bmc1_ucm_init_mode                    2
% 11.78/1.99  --bmc1_ucm_cone_mode                    none
% 11.78/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.78/1.99  --bmc1_ucm_relax_model                  4
% 11.78/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.78/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.78/1.99  --bmc1_ucm_layered_model                none
% 11.78/1.99  --bmc1_ucm_max_lemma_size               10
% 11.78/1.99  
% 11.78/1.99  ------ AIG Options
% 11.78/1.99  
% 11.78/1.99  --aig_mode                              false
% 11.78/1.99  
% 11.78/1.99  ------ Instantiation Options
% 11.78/1.99  
% 11.78/1.99  --instantiation_flag                    true
% 11.78/1.99  --inst_sos_flag                         true
% 11.78/1.99  --inst_sos_phase                        true
% 11.78/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.78/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.78/1.99  --inst_lit_sel_side                     num_symb
% 11.78/1.99  --inst_solver_per_active                1400
% 11.78/1.99  --inst_solver_calls_frac                1.
% 11.78/1.99  --inst_passive_queue_type               priority_queues
% 11.78/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.78/1.99  --inst_passive_queues_freq              [25;2]
% 11.78/1.99  --inst_dismatching                      true
% 11.78/1.99  --inst_eager_unprocessed_to_passive     true
% 11.78/1.99  --inst_prop_sim_given                   true
% 11.78/1.99  --inst_prop_sim_new                     false
% 11.78/1.99  --inst_subs_new                         false
% 11.78/1.99  --inst_eq_res_simp                      false
% 11.78/1.99  --inst_subs_given                       false
% 11.78/1.99  --inst_orphan_elimination               true
% 11.78/1.99  --inst_learning_loop_flag               true
% 11.78/1.99  --inst_learning_start                   3000
% 11.78/1.99  --inst_learning_factor                  2
% 11.78/1.99  --inst_start_prop_sim_after_learn       3
% 11.78/1.99  --inst_sel_renew                        solver
% 11.78/1.99  --inst_lit_activity_flag                true
% 11.78/1.99  --inst_restr_to_given                   false
% 11.78/1.99  --inst_activity_threshold               500
% 11.78/1.99  --inst_out_proof                        true
% 11.78/1.99  
% 11.78/1.99  ------ Resolution Options
% 11.78/1.99  
% 11.78/1.99  --resolution_flag                       true
% 11.78/1.99  --res_lit_sel                           adaptive
% 11.78/1.99  --res_lit_sel_side                      none
% 11.78/1.99  --res_ordering                          kbo
% 11.78/1.99  --res_to_prop_solver                    active
% 11.78/1.99  --res_prop_simpl_new                    false
% 11.78/1.99  --res_prop_simpl_given                  true
% 11.78/1.99  --res_passive_queue_type                priority_queues
% 11.78/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.78/1.99  --res_passive_queues_freq               [15;5]
% 11.78/1.99  --res_forward_subs                      full
% 11.78/1.99  --res_backward_subs                     full
% 11.78/1.99  --res_forward_subs_resolution           true
% 11.78/1.99  --res_backward_subs_resolution          true
% 11.78/1.99  --res_orphan_elimination                true
% 11.78/1.99  --res_time_limit                        2.
% 11.78/1.99  --res_out_proof                         true
% 11.78/1.99  
% 11.78/1.99  ------ Superposition Options
% 11.78/1.99  
% 11.78/1.99  --superposition_flag                    true
% 11.78/1.99  --sup_passive_queue_type                priority_queues
% 11.78/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.78/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.78/1.99  --demod_completeness_check              fast
% 11.78/1.99  --demod_use_ground                      true
% 11.78/1.99  --sup_to_prop_solver                    passive
% 11.78/1.99  --sup_prop_simpl_new                    true
% 11.78/1.99  --sup_prop_simpl_given                  true
% 11.78/1.99  --sup_fun_splitting                     true
% 11.78/1.99  --sup_smt_interval                      50000
% 11.78/1.99  
% 11.78/1.99  ------ Superposition Simplification Setup
% 11.78/1.99  
% 11.78/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.78/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.78/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.78/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.78/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.78/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.78/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.78/1.99  --sup_immed_triv                        [TrivRules]
% 11.78/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.78/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.78/1.99  --sup_immed_bw_main                     []
% 11.78/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.78/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.78/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.78/1.99  --sup_input_bw                          []
% 11.78/1.99  
% 11.78/1.99  ------ Combination Options
% 11.78/1.99  
% 11.78/1.99  --comb_res_mult                         3
% 11.78/1.99  --comb_sup_mult                         2
% 11.78/1.99  --comb_inst_mult                        10
% 11.78/1.99  
% 11.78/1.99  ------ Debug Options
% 11.78/1.99  
% 11.78/1.99  --dbg_backtrace                         false
% 11.78/1.99  --dbg_dump_prop_clauses                 false
% 11.78/1.99  --dbg_dump_prop_clauses_file            -
% 11.78/1.99  --dbg_out_stat                          false
% 11.78/1.99  ------ Parsing...
% 11.78/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.78/1.99  ------ Proving...
% 11.78/1.99  ------ Problem Properties 
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  clauses                                 21
% 11.78/1.99  conjectures                             1
% 11.78/1.99  EPR                                     1
% 11.78/1.99  Horn                                    19
% 11.78/1.99  unary                                   14
% 11.78/1.99  binary                                  2
% 11.78/1.99  lits                                    36
% 11.78/1.99  lits eq                                 22
% 11.78/1.99  fd_pure                                 0
% 11.78/1.99  fd_pseudo                               0
% 11.78/1.99  fd_cond                                 0
% 11.78/1.99  fd_pseudo_cond                          4
% 11.78/1.99  AC symbols                              1
% 11.78/1.99  
% 11.78/1.99  ------ Schedule dynamic 5 is on 
% 11.78/1.99  
% 11.78/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ 
% 11.78/1.99  Current options:
% 11.78/1.99  ------ 
% 11.78/1.99  
% 11.78/1.99  ------ Input Options
% 11.78/1.99  
% 11.78/1.99  --out_options                           all
% 11.78/1.99  --tptp_safe_out                         true
% 11.78/1.99  --problem_path                          ""
% 11.78/1.99  --include_path                          ""
% 11.78/1.99  --clausifier                            res/vclausify_rel
% 11.78/1.99  --clausifier_options                    ""
% 11.78/1.99  --stdin                                 false
% 11.78/1.99  --stats_out                             all
% 11.78/1.99  
% 11.78/1.99  ------ General Options
% 11.78/1.99  
% 11.78/1.99  --fof                                   false
% 11.78/1.99  --time_out_real                         305.
% 11.78/1.99  --time_out_virtual                      -1.
% 11.78/1.99  --symbol_type_check                     false
% 11.78/1.99  --clausify_out                          false
% 11.78/1.99  --sig_cnt_out                           false
% 11.78/1.99  --trig_cnt_out                          false
% 11.78/1.99  --trig_cnt_out_tolerance                1.
% 11.78/1.99  --trig_cnt_out_sk_spl                   false
% 11.78/1.99  --abstr_cl_out                          false
% 11.78/1.99  
% 11.78/1.99  ------ Global Options
% 11.78/1.99  
% 11.78/1.99  --schedule                              default
% 11.78/1.99  --add_important_lit                     false
% 11.78/1.99  --prop_solver_per_cl                    1000
% 11.78/1.99  --min_unsat_core                        false
% 11.78/1.99  --soft_assumptions                      false
% 11.78/1.99  --soft_lemma_size                       3
% 11.78/1.99  --prop_impl_unit_size                   0
% 11.78/1.99  --prop_impl_unit                        []
% 11.78/1.99  --share_sel_clauses                     true
% 11.78/1.99  --reset_solvers                         false
% 11.78/1.99  --bc_imp_inh                            [conj_cone]
% 11.78/1.99  --conj_cone_tolerance                   3.
% 11.78/1.99  --extra_neg_conj                        none
% 11.78/1.99  --large_theory_mode                     true
% 11.78/1.99  --prolific_symb_bound                   200
% 11.78/1.99  --lt_threshold                          2000
% 11.78/1.99  --clause_weak_htbl                      true
% 11.78/1.99  --gc_record_bc_elim                     false
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing Options
% 11.78/1.99  
% 11.78/1.99  --preprocessing_flag                    true
% 11.78/1.99  --time_out_prep_mult                    0.1
% 11.78/1.99  --splitting_mode                        input
% 11.78/1.99  --splitting_grd                         true
% 11.78/1.99  --splitting_cvd                         false
% 11.78/1.99  --splitting_cvd_svl                     false
% 11.78/1.99  --splitting_nvd                         32
% 11.78/1.99  --sub_typing                            true
% 11.78/1.99  --prep_gs_sim                           true
% 11.78/1.99  --prep_unflatten                        true
% 11.78/1.99  --prep_res_sim                          true
% 11.78/1.99  --prep_upred                            true
% 11.78/1.99  --prep_sem_filter                       exhaustive
% 11.78/1.99  --prep_sem_filter_out                   false
% 11.78/1.99  --pred_elim                             true
% 11.78/1.99  --res_sim_input                         true
% 11.78/1.99  --eq_ax_congr_red                       true
% 11.78/1.99  --pure_diseq_elim                       true
% 11.78/1.99  --brand_transform                       false
% 11.78/1.99  --non_eq_to_eq                          false
% 11.78/1.99  --prep_def_merge                        true
% 11.78/1.99  --prep_def_merge_prop_impl              false
% 11.78/1.99  --prep_def_merge_mbd                    true
% 11.78/1.99  --prep_def_merge_tr_red                 false
% 11.78/1.99  --prep_def_merge_tr_cl                  false
% 11.78/1.99  --smt_preprocessing                     true
% 11.78/1.99  --smt_ac_axioms                         fast
% 11.78/1.99  --preprocessed_out                      false
% 11.78/1.99  --preprocessed_stats                    false
% 11.78/1.99  
% 11.78/1.99  ------ Abstraction refinement Options
% 11.78/1.99  
% 11.78/1.99  --abstr_ref                             []
% 11.78/1.99  --abstr_ref_prep                        false
% 11.78/1.99  --abstr_ref_until_sat                   false
% 11.78/1.99  --abstr_ref_sig_restrict                funpre
% 11.78/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.78/1.99  --abstr_ref_under                       []
% 11.78/1.99  
% 11.78/1.99  ------ SAT Options
% 11.78/1.99  
% 11.78/1.99  --sat_mode                              false
% 11.78/1.99  --sat_fm_restart_options                ""
% 11.78/1.99  --sat_gr_def                            false
% 11.78/1.99  --sat_epr_types                         true
% 11.78/1.99  --sat_non_cyclic_types                  false
% 11.78/1.99  --sat_finite_models                     false
% 11.78/1.99  --sat_fm_lemmas                         false
% 11.78/1.99  --sat_fm_prep                           false
% 11.78/1.99  --sat_fm_uc_incr                        true
% 11.78/1.99  --sat_out_model                         small
% 11.78/1.99  --sat_out_clauses                       false
% 11.78/1.99  
% 11.78/1.99  ------ QBF Options
% 11.78/1.99  
% 11.78/1.99  --qbf_mode                              false
% 11.78/1.99  --qbf_elim_univ                         false
% 11.78/1.99  --qbf_dom_inst                          none
% 11.78/1.99  --qbf_dom_pre_inst                      false
% 11.78/1.99  --qbf_sk_in                             false
% 11.78/1.99  --qbf_pred_elim                         true
% 11.78/1.99  --qbf_split                             512
% 11.78/1.99  
% 11.78/1.99  ------ BMC1 Options
% 11.78/1.99  
% 11.78/1.99  --bmc1_incremental                      false
% 11.78/1.99  --bmc1_axioms                           reachable_all
% 11.78/1.99  --bmc1_min_bound                        0
% 11.78/1.99  --bmc1_max_bound                        -1
% 11.78/1.99  --bmc1_max_bound_default                -1
% 11.78/1.99  --bmc1_symbol_reachability              true
% 11.78/1.99  --bmc1_property_lemmas                  false
% 11.78/1.99  --bmc1_k_induction                      false
% 11.78/1.99  --bmc1_non_equiv_states                 false
% 11.78/1.99  --bmc1_deadlock                         false
% 11.78/1.99  --bmc1_ucm                              false
% 11.78/1.99  --bmc1_add_unsat_core                   none
% 11.78/1.99  --bmc1_unsat_core_children              false
% 11.78/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.78/1.99  --bmc1_out_stat                         full
% 11.78/1.99  --bmc1_ground_init                      false
% 11.78/1.99  --bmc1_pre_inst_next_state              false
% 11.78/1.99  --bmc1_pre_inst_state                   false
% 11.78/1.99  --bmc1_pre_inst_reach_state             false
% 11.78/1.99  --bmc1_out_unsat_core                   false
% 11.78/1.99  --bmc1_aig_witness_out                  false
% 11.78/1.99  --bmc1_verbose                          false
% 11.78/1.99  --bmc1_dump_clauses_tptp                false
% 11.78/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.78/1.99  --bmc1_dump_file                        -
% 11.78/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.78/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.78/1.99  --bmc1_ucm_extend_mode                  1
% 11.78/1.99  --bmc1_ucm_init_mode                    2
% 11.78/1.99  --bmc1_ucm_cone_mode                    none
% 11.78/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.78/1.99  --bmc1_ucm_relax_model                  4
% 11.78/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.78/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.78/1.99  --bmc1_ucm_layered_model                none
% 11.78/1.99  --bmc1_ucm_max_lemma_size               10
% 11.78/1.99  
% 11.78/1.99  ------ AIG Options
% 11.78/1.99  
% 11.78/1.99  --aig_mode                              false
% 11.78/1.99  
% 11.78/1.99  ------ Instantiation Options
% 11.78/1.99  
% 11.78/1.99  --instantiation_flag                    true
% 11.78/1.99  --inst_sos_flag                         true
% 11.78/1.99  --inst_sos_phase                        true
% 11.78/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.78/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.78/1.99  --inst_lit_sel_side                     none
% 11.78/1.99  --inst_solver_per_active                1400
% 11.78/1.99  --inst_solver_calls_frac                1.
% 11.78/1.99  --inst_passive_queue_type               priority_queues
% 11.78/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.78/1.99  --inst_passive_queues_freq              [25;2]
% 11.78/1.99  --inst_dismatching                      true
% 11.78/1.99  --inst_eager_unprocessed_to_passive     true
% 11.78/1.99  --inst_prop_sim_given                   true
% 11.78/1.99  --inst_prop_sim_new                     false
% 11.78/1.99  --inst_subs_new                         false
% 11.78/1.99  --inst_eq_res_simp                      false
% 11.78/1.99  --inst_subs_given                       false
% 11.78/1.99  --inst_orphan_elimination               true
% 11.78/1.99  --inst_learning_loop_flag               true
% 11.78/1.99  --inst_learning_start                   3000
% 11.78/1.99  --inst_learning_factor                  2
% 11.78/1.99  --inst_start_prop_sim_after_learn       3
% 11.78/1.99  --inst_sel_renew                        solver
% 11.78/1.99  --inst_lit_activity_flag                true
% 11.78/1.99  --inst_restr_to_given                   false
% 11.78/1.99  --inst_activity_threshold               500
% 11.78/1.99  --inst_out_proof                        true
% 11.78/1.99  
% 11.78/1.99  ------ Resolution Options
% 11.78/1.99  
% 11.78/1.99  --resolution_flag                       false
% 11.78/1.99  --res_lit_sel                           adaptive
% 11.78/1.99  --res_lit_sel_side                      none
% 11.78/1.99  --res_ordering                          kbo
% 11.78/1.99  --res_to_prop_solver                    active
% 11.78/1.99  --res_prop_simpl_new                    false
% 11.78/1.99  --res_prop_simpl_given                  true
% 11.78/1.99  --res_passive_queue_type                priority_queues
% 11.78/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.78/1.99  --res_passive_queues_freq               [15;5]
% 11.78/1.99  --res_forward_subs                      full
% 11.78/1.99  --res_backward_subs                     full
% 11.78/1.99  --res_forward_subs_resolution           true
% 11.78/1.99  --res_backward_subs_resolution          true
% 11.78/1.99  --res_orphan_elimination                true
% 11.78/1.99  --res_time_limit                        2.
% 11.78/1.99  --res_out_proof                         true
% 11.78/1.99  
% 11.78/1.99  ------ Superposition Options
% 11.78/1.99  
% 11.78/1.99  --superposition_flag                    true
% 11.78/1.99  --sup_passive_queue_type                priority_queues
% 11.78/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.78/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.78/1.99  --demod_completeness_check              fast
% 11.78/1.99  --demod_use_ground                      true
% 11.78/1.99  --sup_to_prop_solver                    passive
% 11.78/1.99  --sup_prop_simpl_new                    true
% 11.78/1.99  --sup_prop_simpl_given                  true
% 11.78/1.99  --sup_fun_splitting                     true
% 11.78/1.99  --sup_smt_interval                      50000
% 11.78/1.99  
% 11.78/1.99  ------ Superposition Simplification Setup
% 11.78/1.99  
% 11.78/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.78/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.78/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.78/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.78/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.78/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.78/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.78/1.99  --sup_immed_triv                        [TrivRules]
% 11.78/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.78/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.78/1.99  --sup_immed_bw_main                     []
% 11.78/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.78/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.78/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.78/1.99  --sup_input_bw                          []
% 11.78/1.99  
% 11.78/1.99  ------ Combination Options
% 11.78/1.99  
% 11.78/1.99  --comb_res_mult                         3
% 11.78/1.99  --comb_sup_mult                         2
% 11.78/1.99  --comb_inst_mult                        10
% 11.78/1.99  
% 11.78/1.99  ------ Debug Options
% 11.78/1.99  
% 11.78/1.99  --dbg_backtrace                         false
% 11.78/1.99  --dbg_dump_prop_clauses                 false
% 11.78/1.99  --dbg_dump_prop_clauses_file            -
% 11.78/1.99  --dbg_out_stat                          false
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  ------ Proving...
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  % SZS status Theorem for theBenchmark.p
% 11.78/1.99  
% 11.78/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.78/1.99  
% 11.78/1.99  fof(f2,axiom,(
% 11.78/1.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f40,plain,(
% 11.78/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f2])).
% 11.78/1.99  
% 11.78/1.99  fof(f11,axiom,(
% 11.78/1.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f50,plain,(
% 11.78/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f11])).
% 11.78/1.99  
% 11.78/1.99  fof(f1,axiom,(
% 11.78/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f39,plain,(
% 11.78/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f1])).
% 11.78/1.99  
% 11.78/1.99  fof(f23,conjecture,(
% 11.78/1.99    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f24,negated_conjecture,(
% 11.78/1.99    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 11.78/1.99    inference(negated_conjecture,[],[f23])).
% 11.78/1.99  
% 11.78/1.99  fof(f29,plain,(
% 11.78/1.99    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 11.78/1.99    inference(ennf_transformation,[],[f24])).
% 11.78/1.99  
% 11.78/1.99  fof(f37,plain,(
% 11.78/1.99    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 11.78/1.99    introduced(choice_axiom,[])).
% 11.78/1.99  
% 11.78/1.99  fof(f38,plain,(
% 11.78/1.99    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 11.78/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f37])).
% 11.78/1.99  
% 11.78/1.99  fof(f69,plain,(
% 11.78/1.99    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 11.78/1.99    inference(cnf_transformation,[],[f38])).
% 11.78/1.99  
% 11.78/1.99  fof(f13,axiom,(
% 11.78/1.99    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f52,plain,(
% 11.78/1.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f13])).
% 11.78/1.99  
% 11.78/1.99  fof(f15,axiom,(
% 11.78/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f61,plain,(
% 11.78/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f15])).
% 11.78/1.99  
% 11.78/1.99  fof(f16,axiom,(
% 11.78/1.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f62,plain,(
% 11.78/1.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f16])).
% 11.78/1.99  
% 11.78/1.99  fof(f17,axiom,(
% 11.78/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f63,plain,(
% 11.78/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f17])).
% 11.78/1.99  
% 11.78/1.99  fof(f18,axiom,(
% 11.78/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f64,plain,(
% 11.78/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f18])).
% 11.78/1.99  
% 11.78/1.99  fof(f19,axiom,(
% 11.78/1.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f65,plain,(
% 11.78/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f19])).
% 11.78/1.99  
% 11.78/1.99  fof(f20,axiom,(
% 11.78/1.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f66,plain,(
% 11.78/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f20])).
% 11.78/1.99  
% 11.78/1.99  fof(f21,axiom,(
% 11.78/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f67,plain,(
% 11.78/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f21])).
% 11.78/1.99  
% 11.78/1.99  fof(f70,plain,(
% 11.78/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.78/1.99    inference(definition_unfolding,[],[f66,f67])).
% 11.78/1.99  
% 11.78/1.99  fof(f71,plain,(
% 11.78/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.78/1.99    inference(definition_unfolding,[],[f65,f70])).
% 11.78/1.99  
% 11.78/1.99  fof(f72,plain,(
% 11.78/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.78/1.99    inference(definition_unfolding,[],[f64,f71])).
% 11.78/1.99  
% 11.78/1.99  fof(f73,plain,(
% 11.78/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.78/1.99    inference(definition_unfolding,[],[f63,f72])).
% 11.78/1.99  
% 11.78/1.99  fof(f74,plain,(
% 11.78/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.78/1.99    inference(definition_unfolding,[],[f62,f73])).
% 11.78/1.99  
% 11.78/1.99  fof(f75,plain,(
% 11.78/1.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.78/1.99    inference(definition_unfolding,[],[f61,f74])).
% 11.78/1.99  
% 11.78/1.99  fof(f86,plain,(
% 11.78/1.99    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0),
% 11.78/1.99    inference(definition_unfolding,[],[f69,f52,f75])).
% 11.78/1.99  
% 11.78/1.99  fof(f9,axiom,(
% 11.78/1.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f48,plain,(
% 11.78/1.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.78/1.99    inference(cnf_transformation,[],[f9])).
% 11.78/1.99  
% 11.78/1.99  fof(f12,axiom,(
% 11.78/1.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f51,plain,(
% 11.78/1.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 11.78/1.99    inference(cnf_transformation,[],[f12])).
% 11.78/1.99  
% 11.78/1.99  fof(f22,axiom,(
% 11.78/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f68,plain,(
% 11.78/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.78/1.99    inference(cnf_transformation,[],[f22])).
% 11.78/1.99  
% 11.78/1.99  fof(f85,plain,(
% 11.78/1.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.78/1.99    inference(definition_unfolding,[],[f68,f52,f74])).
% 11.78/1.99  
% 11.78/1.99  fof(f8,axiom,(
% 11.78/1.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f47,plain,(
% 11.78/1.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f8])).
% 11.78/1.99  
% 11.78/1.99  fof(f4,axiom,(
% 11.78/1.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f43,plain,(
% 11.78/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f4])).
% 11.78/1.99  
% 11.78/1.99  fof(f76,plain,(
% 11.78/1.99    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 11.78/1.99    inference(definition_unfolding,[],[f47,f43])).
% 11.78/1.99  
% 11.78/1.99  fof(f5,axiom,(
% 11.78/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f27,plain,(
% 11.78/1.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.78/1.99    inference(ennf_transformation,[],[f5])).
% 11.78/1.99  
% 11.78/1.99  fof(f44,plain,(
% 11.78/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f27])).
% 11.78/1.99  
% 11.78/1.99  fof(f3,axiom,(
% 11.78/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f25,plain,(
% 11.78/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.78/1.99    inference(rectify,[],[f3])).
% 11.78/1.99  
% 11.78/1.99  fof(f26,plain,(
% 11.78/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.78/1.99    inference(ennf_transformation,[],[f25])).
% 11.78/1.99  
% 11.78/1.99  fof(f30,plain,(
% 11.78/1.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 11.78/1.99    introduced(choice_axiom,[])).
% 11.78/1.99  
% 11.78/1.99  fof(f31,plain,(
% 11.78/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.78/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f30])).
% 11.78/1.99  
% 11.78/1.99  fof(f42,plain,(
% 11.78/1.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 11.78/1.99    inference(cnf_transformation,[],[f31])).
% 11.78/1.99  
% 11.78/1.99  fof(f10,axiom,(
% 11.78/1.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f49,plain,(
% 11.78/1.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 11.78/1.99    inference(cnf_transformation,[],[f10])).
% 11.78/1.99  
% 11.78/1.99  fof(f6,axiom,(
% 11.78/1.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f45,plain,(
% 11.78/1.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 11.78/1.99    inference(cnf_transformation,[],[f6])).
% 11.78/1.99  
% 11.78/1.99  fof(f14,axiom,(
% 11.78/1.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 11.78/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.78/1.99  
% 11.78/1.99  fof(f28,plain,(
% 11.78/1.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 11.78/1.99    inference(ennf_transformation,[],[f14])).
% 11.78/1.99  
% 11.78/1.99  fof(f32,plain,(
% 11.78/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.78/1.99    inference(nnf_transformation,[],[f28])).
% 11.78/1.99  
% 11.78/1.99  fof(f33,plain,(
% 11.78/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.78/1.99    inference(flattening,[],[f32])).
% 11.78/1.99  
% 11.78/1.99  fof(f34,plain,(
% 11.78/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.78/1.99    inference(rectify,[],[f33])).
% 11.78/1.99  
% 11.78/1.99  fof(f35,plain,(
% 11.78/1.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 11.78/1.99    introduced(choice_axiom,[])).
% 11.78/1.99  
% 11.78/1.99  fof(f36,plain,(
% 11.78/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.78/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 11.78/1.99  
% 11.78/1.99  fof(f54,plain,(
% 11.78/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.78/1.99    inference(cnf_transformation,[],[f36])).
% 11.78/1.99  
% 11.78/1.99  fof(f83,plain,(
% 11.78/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 11.78/1.99    inference(definition_unfolding,[],[f54,f73])).
% 11.78/1.99  
% 11.78/1.99  fof(f91,plain,(
% 11.78/1.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 11.78/1.99    inference(equality_resolution,[],[f83])).
% 11.78/1.99  
% 11.78/1.99  fof(f92,plain,(
% 11.78/1.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 11.78/1.99    inference(equality_resolution,[],[f91])).
% 11.78/1.99  
% 11.78/1.99  fof(f53,plain,(
% 11.78/1.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 11.78/1.99    inference(cnf_transformation,[],[f36])).
% 11.78/1.99  
% 11.78/1.99  fof(f84,plain,(
% 11.78/1.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 11.78/1.99    inference(definition_unfolding,[],[f53,f73])).
% 11.78/1.99  
% 11.78/1.99  fof(f93,plain,(
% 11.78/1.99    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 11.78/1.99    inference(equality_resolution,[],[f84])).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1,plain,
% 11.78/1.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 11.78/1.99      inference(cnf_transformation,[],[f40]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_10,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.78/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_0,plain,
% 11.78/1.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.78/1.99      inference(cnf_transformation,[],[f39]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_21,negated_conjecture,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
% 11.78/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_315,negated_conjecture,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
% 11.78/1.99      inference(theory_normalisation,[status(thm)],[c_21,c_10,c_1]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1067,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k1_xboole_0 ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_0,c_315]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1216,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1067,c_10]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_8,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.78/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1149,plain,
% 11.78/1.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1222,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = X0 ),
% 11.78/1.99      inference(light_normalisation,[status(thm)],[c_1216,c_1149]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1486,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) = X0 ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_10,c_1222]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1607,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) = X0 ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1,c_1486]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_11,plain,
% 11.78/1.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.78/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1487,plain,
% 11.78/1.99      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(sK3,k1_xboole_0) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_11,c_1222]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1491,plain,
% 11.78/1.99      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_1487,c_8]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1495,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_1491,c_1222]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_2599,plain,
% 11.78/1.99      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(sK3,X0) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1607,c_1495]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_559,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_560,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_10976,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,X1)) = k5_xboole_0(X1,X0) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1495,c_560]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_11969,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(sK3,X2)) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_559,c_10976]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1503,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X0,X1) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1495,c_10]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1785,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k1_xboole_0) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_11,c_1503]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1805,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = sK3 ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_1785,c_8]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_2120,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),X0) = sK3 ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1495,c_1805]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_2454,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(sK3,X1) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_2120,c_10]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_5064,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,X1) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_2454,c_1]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31551,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(sK3,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))) = k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_11969,c_5064]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_12029,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X1,k5_xboole_0(sK3,X2))) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_10976,c_559]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1497,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(X0,sK3)) = X0 ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1,c_1495]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_2121,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,sK3),X0) = sK3 ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1497,c_1805]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1618,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,sK3))) = k5_xboole_0(X0,X1) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_10,c_1497]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_2924,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,sK3),sK3),X0) = k5_xboole_0(sK3,sK3) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_2121,c_1618]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_2942,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,sK3),sK3),X0) = k1_xboole_0 ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_2924,c_11]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_3977,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK3,X0),sK3),X0) = k1_xboole_0 ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1,c_2942]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_5937,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK3,X0),sK3),k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_3977,c_559]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1781,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X1,X0) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1,c_1503]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6010,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))) = k5_xboole_0(k5_xboole_0(X1,X2),X0) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_559,c_1781]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_4232,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_10,c_1781]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6024,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 11.78/1.99      inference(light_normalisation,[status(thm)],[c_6010,c_4232]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6150,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,sK3),k5_xboole_0(k5_xboole_0(X0,X1),X1)) = k5_xboole_0(X0,k1_xboole_0) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_5937,c_6024]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6151,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,X1)),sK3)) = k5_xboole_0(X1,k1_xboole_0) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_6150,c_6024]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6152,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X0))) = k5_xboole_0(X1,k1_xboole_0) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_6151,c_6024]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6153,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK3,X1),X1))) = k5_xboole_0(X0,k1_xboole_0) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_6152,c_6024]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6004,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK3,X1),X2))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_559,c_1503]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6053,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,sK3)))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_6004,c_6024]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6154,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_6153,c_6024,c_6053]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6155,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_6154,c_8]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6614,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X0))) = k5_xboole_0(sK3,X1) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_6155,c_1503]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_15361,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,k5_xboole_0(X0,X1))) = k5_xboole_0(sK3,k5_xboole_0(sK3,X1)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_12029,c_6614]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_15383,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,k5_xboole_0(X0,X1))) = X1 ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_15361,c_1495,c_10976]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_15807,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X0)),k5_xboole_0(sK3,k5_xboole_0(X1,k5_xboole_0(X2,X0)))) = k5_xboole_0(X1,k5_xboole_0(sK3,X2)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_12029,c_15383]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_15884,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(X1,k5_xboole_0(X2,X0)))) = k5_xboole_0(X1,k5_xboole_0(sK3,X2)) ),
% 11.78/1.99      inference(light_normalisation,[status(thm)],[c_15807,c_1495]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_16120,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(sK3,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X3))))) = k5_xboole_0(X2,k5_xboole_0(sK3,k5_xboole_0(sK3,X3))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_12029,c_15884]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_15343,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(sK3,X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_12029,c_1]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_16254,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(sK3,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X3))))) = k5_xboole_0(X2,X3) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_16120,c_1495,c_15343]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_24291,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(sK3,X1))),k5_xboole_0(sK3,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X4,X1)))))) = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(sK3,X4))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_12029,c_16254]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_16111,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,k5_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(sK3,k5_xboole_0(sK3,X0))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_15383,c_15884]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_16262,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,k5_xboole_0(X2,X1))) = k5_xboole_0(X2,X0) ),
% 11.78/1.99      inference(light_normalisation,[status(thm)],[c_16111,c_1495]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_17155,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,k5_xboole_0(X2,k5_xboole_0(sK3,k5_xboole_0(X0,X3))))) = k5_xboole_0(X2,k5_xboole_0(sK3,k5_xboole_0(X1,X3))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_16262,c_16262]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_11069,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_560,c_1503]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_2932,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1618,c_10]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_2939,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.78/1.99      inference(light_normalisation,[status(thm)],[c_2932,c_10]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_11101,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 11.78/1.99      inference(light_normalisation,[status(thm)],[c_11069,c_2939]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_11073,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_560,c_1503]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_13812,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(X1,X2)))) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_559,c_11073]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_561,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_14041,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(sK3,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_561,c_11969]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_17261,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,k5_xboole_0(X2,k5_xboole_0(X0,X3)))) = k5_xboole_0(X3,k5_xboole_0(sK3,k5_xboole_0(X1,X2))) ),
% 11.78/1.99      inference(demodulation,
% 11.78/1.99                [status(thm)],
% 11.78/1.99                [c_17155,c_11101,c_13812,c_14041]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_24446,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(sK3,k5_xboole_0(X2,X3))) = k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) ),
% 11.78/1.99      inference(demodulation,
% 11.78/1.99                [status(thm)],
% 11.78/1.99                [c_24291,c_1495,c_15343,c_17261]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_26814,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))),k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X3,X0),X4))) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),k5_xboole_0(sK3,sK3))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_24446,c_24446]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_14081,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))),k5_xboole_0(sK3,X3)) = k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X2,X1))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_561,c_11969]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_24354,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(sK3,sK3)),k5_xboole_0(sK3,k5_xboole_0(X2,k5_xboole_0(X3,X4)))) = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(X1,X4)))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_16254,c_16254]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_11970,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(sK3,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_560,c_10976]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_24358,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X4)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X4,k5_xboole_0(X3,X2)))) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_24354,c_11970,c_15343]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_26907,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X3,X4))) = k5_xboole_0(X2,k5_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(sK3,k5_xboole_0(sK3,X1))))) ),
% 11.78/1.99      inference(demodulation,
% 11.78/1.99                [status(thm)],
% 11.78/1.99                [c_26814,c_11101,c_14081,c_24358]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_26908,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X3,X4))) = k5_xboole_0(X2,k5_xboole_0(X4,k5_xboole_0(X3,X1))) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_26907,c_1495,c_24358]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31636,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X2,X3))) = k5_xboole_0(X1,k5_xboole_0(X3,k5_xboole_0(X2,sK3))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_5064,c_26908]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_16013,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(sK3,X1)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_11073,c_15884]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_26742,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))),k5_xboole_0(sK3,sK3)) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_2120,c_24446]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_5928,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X1,X0)) = k5_xboole_0(X1,sK3) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_2120,c_559]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_7404,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))),k5_xboole_0(X1,X0)) = k5_xboole_0(sK3,sK3) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1781,c_5928]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_2925,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X0,X1) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1,c_1618]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_7472,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k5_xboole_0(sK3,sK3) ),
% 11.78/1.99      inference(light_normalisation,[status(thm)],[c_7404,c_2925]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_7473,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_7472,c_11,c_6024]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_17140,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))),k5_xboole_0(sK3,k5_xboole_0(sK3,X1))) = k5_xboole_0(X2,X0) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_6614,c_16262]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_14145,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2)))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_11969,c_561]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_17280,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(sK3,k5_xboole_0(sK3,X1))) = k5_xboole_0(X2,X0) ),
% 11.78/1.99      inference(light_normalisation,[status(thm)],[c_17140,c_14145]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_17281,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X1,X2) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_17280,c_1495,c_11101]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_18344,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_7473,c_17281]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_18469,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 11.78/1.99      inference(light_normalisation,[status(thm)],[c_18344,c_11101]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_26994,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))) = k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X1,X2)) ),
% 11.78/1.99      inference(demodulation,
% 11.78/1.99                [status(thm)],
% 11.78/1.99                [c_26742,c_11,c_14081,c_18469]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_16997,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(X1,X0))) = k5_xboole_0(X1,sK3) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1495,c_16262]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_17996,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(sK3,k5_xboole_0(sK3,X0))) = k5_xboole_0(X1,sK3) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_6614,c_16997]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_18150,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X0) = k5_xboole_0(X1,sK3) ),
% 11.78/1.99      inference(light_normalisation,[status(thm)],[c_17996,c_1495]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_29168,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X2)),k5_xboole_0(X3,X4)),k5_xboole_0(X2,sK3)) = k5_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X0,X3))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_18150,c_26908]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_14099,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(X2,sK3)) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1,c_11969]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_29637,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X3,k5_xboole_0(X4,X0)))) = k5_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(X1,X4))) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_29168,c_14099,c_24358]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_26646,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X1,X2),X3))) = k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(sK3,X2)))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_5928,c_24446]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_27083,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X0)) ),
% 11.78/1.99      inference(demodulation,
% 11.78/1.99                [status(thm)],
% 11.78/1.99                [c_26646,c_1495,c_11101,c_11970]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_28173,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)),k1_xboole_0) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X2,X1),X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_7473,c_27083]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_28422,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X3,X2))) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_28173,c_11101,c_18469]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_29638,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,X0),X4)))) = k5_xboole_0(X4,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_29637,c_28422]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_28231,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3)))) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_27083,c_561]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_29639,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X0))) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_29638,c_11101,c_28231]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_20,plain,
% 11.78/1.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 11.78/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_316,plain,
% 11.78/1.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
% 11.78/1.99      inference(theory_normalisation,[status(thm)],[c_20,c_10,c_1]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_1501,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = k5_xboole_0(X0,k3_xboole_0(sK3,X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_316,c_1495]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_2006,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = k5_xboole_0(X0,k3_xboole_0(X0,sK3)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_0,c_1501]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_9829,plain,
% 11.78/1.99      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)) = k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_2006,c_1495]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_9924,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X0,sK3)))) = k5_xboole_0(X0,k3_xboole_0(sK3,X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_9829,c_1501]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_26582,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK3,X0)),k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1))) = k5_xboole_0(X1,k5_xboole_0(sK3,k5_xboole_0(sK3,sK3))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_9924,c_24446]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_9921,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) = k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(sK3,X0))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_9829,c_316]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_12732,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X0,sK3))),X1)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK3,X0)),X1) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_9921,c_1503]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_9819,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k3_xboole_0(X0,sK3)) = k5_xboole_0(X0,k3_xboole_0(sK3,X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_2006,c_1501]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_10383,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sK3),X1)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK3,X0)),X1) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_9819,c_10]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_12739,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X0,sK3))),X1)) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sK3),X1)) ),
% 11.78/1.99      inference(light_normalisation,[status(thm)],[c_12732,c_10383]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_12740,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sK3),X1)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK3)),X1) ),
% 11.78/1.99      inference(demodulation,
% 11.78/1.99                [status(thm)],
% 11.78/1.99                [c_12739,c_1503,c_2925,c_11101]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_27164,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK3,X0)),k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sK3),X1)))) = k5_xboole_0(X1,k5_xboole_0(sK3,k5_xboole_0(sK3,sK3))) ),
% 11.78/1.99      inference(light_normalisation,[status(thm)],[c_26582,c_12740]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_24212,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,sK3)),k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK3,X1))))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,sK3))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_9924,c_16254]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6011,plain,
% 11.78/1.99      ( k5_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(X0,X1))) = k5_xboole_0(X1,X0) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_559,c_1781]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_24552,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,sK3))) = k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(sK3,X1)),X0) ),
% 11.78/1.99      inference(demodulation,
% 11.78/1.99                [status(thm)],
% 11.78/1.99                [c_24212,c_1495,c_6011,c_14041]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_24964,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,sK3))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK3,X0)),X1) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_24552,c_559]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_27165,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK3,X0)),k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sK3),X1)))) = k5_xboole_0(X1,sK3) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_27164,c_1495,c_24964]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_30037,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,sK3)),k5_xboole_0(k3_xboole_0(sK3,sK3),X0)) = k5_xboole_0(X0,sK3) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1495,c_27165]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_30830,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK3,sK3),X0),k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK3))))) = k5_xboole_0(k5_xboole_0(X3,k5_xboole_0(X0,sK3)),k5_xboole_0(X3,k5_xboole_0(X2,X1))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_30037,c_26908]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_29084,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(sK3,X0)))) = k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(sK3,X1)),k5_xboole_0(X4,k5_xboole_0(X3,X2))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_2454,c_26908]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_29192,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X3,X4))) = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,X1))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1,c_26908]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_29740,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(sK3,X0)))) = k5_xboole_0(X1,k5_xboole_0(X3,k5_xboole_0(X2,sK3))) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_29084,c_29192,c_29639]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_30117,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,sK3),X1))),k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X0,k3_xboole_0(sK3,X0))))) = k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X1,sK3)),k5_xboole_0(X4,k5_xboole_0(X3,X2))) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_27165,c_26908]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_30223,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(X0,k5_xboole_0(X2,X3))) = sP0_iProver_split(X1,X2,X3) ),
% 11.78/1.99      inference(splitting,
% 11.78/1.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 11.78/1.99                [c_30117]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_30918,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,sK3))) = sP0_iProver_split(X0,X1,X2) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_30830,c_29740,c_30223]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31727,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X2)) = sP0_iProver_split(X1,X0,X2) ),
% 11.78/1.99      inference(demodulation,
% 11.78/1.99                [status(thm)],
% 11.78/1.99                [c_31636,c_16013,c_26994,c_29639,c_30918]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31645,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)),k5_xboole_0(sK3,X2)) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(sK3,X1),X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_5064,c_27083]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_17138,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,X2))),k5_xboole_0(sK3,k5_xboole_0(X1,sK3))) = k5_xboole_0(k5_xboole_0(sK3,X2),X0) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_5928,c_16262]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_17284,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(sK3,X1)) = k5_xboole_0(X2,k5_xboole_0(sK3,X0)) ),
% 11.78/1.99      inference(demodulation,
% 11.78/1.99                [status(thm)],
% 11.78/1.99                [c_17138,c_6155,c_11101,c_14041]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_18341,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK3,X0),X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,k5_xboole_0(sK3,X2)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_10976,c_17281]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_16036,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(sK3,k5_xboole_0(X1,X0))) = k5_xboole_0(sK3,k5_xboole_0(sK3,X1)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1618,c_15884]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6584,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,sK3),sK3) = k5_xboole_0(X0,k1_xboole_0) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_2942,c_6155]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6628,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,sK3),sK3) = X0 ),
% 11.78/1.99      inference(light_normalisation,[status(thm)],[c_6584,c_8]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_8670,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(sK3,X1)) = k5_xboole_0(X0,X1) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_6628,c_10]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_16327,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(sK3,k5_xboole_0(X1,X0))) = X1 ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_16036,c_1495,c_8670]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_16828,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X1,sK3),X2)) = k5_xboole_0(X2,X0) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_16327,c_560]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_16868,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_16828,c_11101,c_14041]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_18471,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),X1) = k5_xboole_0(X0,k5_xboole_0(sK3,X1)) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_18341,c_11101,c_16868]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31724,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(sK3,X2))) ),
% 11.78/1.99      inference(demodulation,
% 11.78/1.99                [status(thm)],
% 11.78/1.99                [c_31645,c_11101,c_17284,c_18471,c_24358]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31728,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))) = sP0_iProver_split(X0,X1,X2) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_31727,c_31724]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31631,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(k5_xboole_0(X2,X1),X3)) = k5_xboole_0(k5_xboole_0(sK3,X2),k5_xboole_0(X3,X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_5064,c_27083]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_10997,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(sK3,X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_6614,c_560]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31731,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK3,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X2)) ),
% 11.78/1.99      inference(demodulation,
% 11.78/1.99                [status(thm)],
% 11.78/1.99                [c_31631,c_10997,c_11101,c_24358,c_26994]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31815,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),sP0_iProver_split(sK3,X1,X2)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_31551,c_31728,c_31731]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31688,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X0)),k5_xboole_0(sK3,k5_xboole_0(sK3,X1))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X2),X1),X2) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_5064,c_16254]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31696,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),X1) = k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(sK3,X2))) ),
% 11.78/1.99      inference(light_normalisation,[status(thm)],[c_31688,c_1495]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_6593,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_6155,c_6155]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_17127,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k3_xboole_0(X1,sK3))),k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1))))) = k5_xboole_0(X1,X0) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_2006,c_16262]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_17295,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,sK3)),k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1)))) = k5_xboole_0(X1,X0) ),
% 11.78/1.99      inference(demodulation,
% 11.78/1.99                [status(thm)],
% 11.78/1.99                [c_17127,c_1495,c_11101,c_14041]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31064,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,sK3)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X2)))) = k5_xboole_0(k5_xboole_0(X2,X1),k5_xboole_0(sK3,X0)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_17295,c_11969]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31092,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,sK3),k5_xboole_0(X2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1))))) = k5_xboole_0(X2,k5_xboole_0(sK3,k5_xboole_0(X0,X1))) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_31064,c_11101,c_29639]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_17983,plain,
% 11.78/1.99      ( k5_xboole_0(k3_xboole_0(X0,sK3),k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))))) = k5_xboole_0(X0,sK3) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_2006,c_16997]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_18161,plain,
% 11.78/1.99      ( k5_xboole_0(k3_xboole_0(X0,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = k5_xboole_0(X0,sK3) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_17983,c_1495]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_21514,plain,
% 11.78/1.99      ( k5_xboole_0(k3_xboole_0(X0,sK3),k5_xboole_0(X1,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)))) = k5_xboole_0(X1,k5_xboole_0(X0,sK3)) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_18161,c_559]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31093,plain,
% 11.78/1.99      ( k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(X1,X2))) = sP0_iProver_split(X1,X0,X2) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_31092,c_21514,c_30918]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31697,plain,
% 11.78/1.99      ( sP0_iProver_split(sK3,X0,X1) = k5_xboole_0(X0,X1) ),
% 11.78/1.99      inference(demodulation,
% 11.78/1.99                [status(thm)],
% 11.78/1.99                [c_31696,c_6593,c_11101,c_31093]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31816,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X2)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_31815,c_31697]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31817,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X2)) = X0 ),
% 11.78/1.99      inference(light_normalisation,[status(thm)],[c_31816,c_1495]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_33197,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_2599,c_31817]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_7,plain,
% 11.78/1.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 11.78/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_540,plain,
% 11.78/1.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 11.78/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_2319,plain,
% 11.78/1.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_0,c_540]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_3843,plain,
% 11.78/1.99      ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1491,c_2319]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_4,plain,
% 11.78/1.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 11.78/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_542,plain,
% 11.78/1.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 11.78/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_31454,plain,
% 11.78/1.99      ( k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_3843,c_542]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_33570,plain,
% 11.78/1.99      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,sK3)) ),
% 11.78/1.99      inference(light_normalisation,[status(thm)],[c_33197,c_31454]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_7383,plain,
% 11.78/1.99      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,sK3) ),
% 11.78/1.99      inference(superposition,[status(thm)],[c_1,c_5928]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_33571,plain,
% 11.78/1.99      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 11.78/1.99      inference(demodulation,[status(thm)],[c_33570,c_11,c_7383]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_319,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_652,plain,
% 11.78/1.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3
% 11.78/1.99      | k3_xboole_0(X4,k1_xboole_0) != X3
% 11.78/1.99      | k3_xboole_0(X4,k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_319]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_749,plain,
% 11.78/1.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != k1_xboole_0
% 11.78/1.99      | k3_xboole_0(X3,k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)
% 11.78/1.99      | k3_xboole_0(X3,k1_xboole_0) != k1_xboole_0 ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_652]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_750,plain,
% 11.78/1.99      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0
% 11.78/1.99      | k3_xboole_0(sK2,k1_xboole_0) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 11.78/1.99      | k3_xboole_0(sK2,k1_xboole_0) != k1_xboole_0 ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_749]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_322,plain,
% 11.78/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.78/1.99      theory(equality) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_566,plain,
% 11.78/1.99      ( ~ r2_hidden(X0,X1)
% 11.78/1.99      | r2_hidden(X2,k3_xboole_0(X3,k1_xboole_0))
% 11.78/1.99      | X2 != X0
% 11.78/1.99      | k3_xboole_0(X3,k1_xboole_0) != X1 ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_322]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_578,plain,
% 11.78/1.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
% 11.78/1.99      | r2_hidden(X3,k3_xboole_0(X4,k1_xboole_0))
% 11.78/1.99      | X3 != X0
% 11.78/1.99      | k3_xboole_0(X4,k1_xboole_0) != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_566]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_580,plain,
% 11.78/1.99      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 11.78/1.99      | r2_hidden(sK2,k3_xboole_0(sK2,k1_xboole_0))
% 11.78/1.99      | k3_xboole_0(sK2,k1_xboole_0) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 11.78/1.99      | sK2 != sK2 ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_578]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_2,plain,
% 11.78/1.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 11.78/1.99      inference(cnf_transformation,[],[f42]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_9,plain,
% 11.78/1.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 11.78/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_200,plain,
% 11.78/1.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 11.78/1.99      | X3 != X1
% 11.78/1.99      | k1_xboole_0 != X2 ),
% 11.78/1.99      inference(resolution_lifted,[status(thm)],[c_2,c_9]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_201,plain,
% 11.78/1.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 11.78/1.99      inference(unflattening,[status(thm)],[c_200]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_203,plain,
% 11.78/1.99      ( ~ r2_hidden(sK2,k3_xboole_0(sK2,k1_xboole_0)) ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_201]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_5,plain,
% 11.78/1.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.78/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_51,plain,
% 11.78/1.99      ( k3_xboole_0(sK2,k1_xboole_0) = k1_xboole_0 ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_18,plain,
% 11.78/1.99      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 11.78/1.99      inference(cnf_transformation,[],[f92]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_27,plain,
% 11.78/1.99      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_18]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_19,plain,
% 11.78/1.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 11.78/1.99      | X0 = X1
% 11.78/1.99      | X0 = X2
% 11.78/1.99      | X0 = X3 ),
% 11.78/1.99      inference(cnf_transformation,[],[f93]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(c_24,plain,
% 11.78/1.99      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 11.78/1.99      | sK2 = sK2 ),
% 11.78/1.99      inference(instantiation,[status(thm)],[c_19]) ).
% 11.78/1.99  
% 11.78/1.99  cnf(contradiction,plain,
% 11.78/1.99      ( $false ),
% 11.78/1.99      inference(minisat,
% 11.78/1.99                [status(thm)],
% 11.78/1.99                [c_33571,c_750,c_580,c_203,c_51,c_27,c_24]) ).
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.78/1.99  
% 11.78/1.99  ------                               Statistics
% 11.78/1.99  
% 11.78/1.99  ------ General
% 11.78/1.99  
% 11.78/1.99  abstr_ref_over_cycles:                  0
% 11.78/1.99  abstr_ref_under_cycles:                 0
% 11.78/1.99  gc_basic_clause_elim:                   0
% 11.78/1.99  forced_gc_time:                         0
% 11.78/1.99  parsing_time:                           0.01
% 11.78/1.99  unif_index_cands_time:                  0.
% 11.78/1.99  unif_index_add_time:                    0.
% 11.78/1.99  orderings_time:                         0.
% 11.78/1.99  out_proof_time:                         0.013
% 11.78/1.99  total_time:                             1.142
% 11.78/1.99  num_of_symbols:                         44
% 11.78/1.99  num_of_terms:                           67952
% 11.78/1.99  
% 11.78/1.99  ------ Preprocessing
% 11.78/1.99  
% 11.78/1.99  num_of_splits:                          0
% 11.78/1.99  num_of_split_atoms:                     1
% 11.78/1.99  num_of_reused_defs:                     0
% 11.78/1.99  num_eq_ax_congr_red:                    22
% 11.78/1.99  num_of_sem_filtered_clauses:            1
% 11.78/1.99  num_of_subtypes:                        0
% 11.78/1.99  monotx_restored_types:                  0
% 11.78/1.99  sat_num_of_epr_types:                   0
% 11.78/1.99  sat_num_of_non_cyclic_types:            0
% 11.78/1.99  sat_guarded_non_collapsed_types:        0
% 11.78/1.99  num_pure_diseq_elim:                    0
% 11.78/1.99  simp_replaced_by:                       0
% 11.78/1.99  res_preprocessed:                       102
% 11.78/1.99  prep_upred:                             0
% 11.78/1.99  prep_unflattend:                        12
% 11.78/1.99  smt_new_axioms:                         0
% 11.78/1.99  pred_elim_cands:                        2
% 11.78/1.99  pred_elim:                              1
% 11.78/1.99  pred_elim_cl:                           1
% 11.78/1.99  pred_elim_cycles:                       4
% 11.78/1.99  merged_defs:                            0
% 11.78/1.99  merged_defs_ncl:                        0
% 11.78/1.99  bin_hyper_res:                          0
% 11.78/1.99  prep_cycles:                            4
% 11.78/1.99  pred_elim_time:                         0.001
% 11.78/1.99  splitting_time:                         0.
% 11.78/1.99  sem_filter_time:                        0.
% 11.78/1.99  monotx_time:                            0.
% 11.78/1.99  subtype_inf_time:                       0.
% 11.78/1.99  
% 11.78/1.99  ------ Problem properties
% 11.78/1.99  
% 11.78/1.99  clauses:                                21
% 11.78/1.99  conjectures:                            1
% 11.78/1.99  epr:                                    1
% 11.78/1.99  horn:                                   19
% 11.78/1.99  ground:                                 1
% 11.78/1.99  unary:                                  14
% 11.78/1.99  binary:                                 2
% 11.78/1.99  lits:                                   36
% 11.78/1.99  lits_eq:                                22
% 11.78/1.99  fd_pure:                                0
% 11.78/1.99  fd_pseudo:                              0
% 11.78/1.99  fd_cond:                                0
% 11.78/1.99  fd_pseudo_cond:                         4
% 11.78/1.99  ac_symbols:                             1
% 11.78/1.99  
% 11.78/1.99  ------ Propositional Solver
% 11.78/1.99  
% 11.78/1.99  prop_solver_calls:                      31
% 11.78/1.99  prop_fast_solver_calls:                 572
% 11.78/1.99  smt_solver_calls:                       0
% 11.78/1.99  smt_fast_solver_calls:                  0
% 11.78/1.99  prop_num_of_clauses:                    8333
% 11.78/1.99  prop_preprocess_simplified:             13610
% 11.78/1.99  prop_fo_subsumed:                       0
% 11.78/1.99  prop_solver_time:                       0.
% 11.78/1.99  smt_solver_time:                        0.
% 11.78/1.99  smt_fast_solver_time:                   0.
% 11.78/1.99  prop_fast_solver_time:                  0.
% 11.78/1.99  prop_unsat_core_time:                   0.
% 11.78/1.99  
% 11.78/1.99  ------ QBF
% 11.78/1.99  
% 11.78/1.99  qbf_q_res:                              0
% 11.78/1.99  qbf_num_tautologies:                    0
% 11.78/1.99  qbf_prep_cycles:                        0
% 11.78/1.99  
% 11.78/1.99  ------ BMC1
% 11.78/1.99  
% 11.78/1.99  bmc1_current_bound:                     -1
% 11.78/1.99  bmc1_last_solved_bound:                 -1
% 11.78/1.99  bmc1_unsat_core_size:                   -1
% 11.78/1.99  bmc1_unsat_core_parents_size:           -1
% 11.78/1.99  bmc1_merge_next_fun:                    0
% 11.78/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.78/1.99  
% 11.78/1.99  ------ Instantiation
% 11.78/1.99  
% 11.78/1.99  inst_num_of_clauses:                    1858
% 11.78/1.99  inst_num_in_passive:                    1041
% 11.78/1.99  inst_num_in_active:                     526
% 11.78/1.99  inst_num_in_unprocessed:                291
% 11.78/1.99  inst_num_of_loops:                      590
% 11.78/1.99  inst_num_of_learning_restarts:          0
% 11.78/1.99  inst_num_moves_active_passive:          61
% 11.78/1.99  inst_lit_activity:                      0
% 11.78/1.99  inst_lit_activity_moves:                0
% 11.78/1.99  inst_num_tautologies:                   0
% 11.78/1.99  inst_num_prop_implied:                  0
% 11.78/1.99  inst_num_existing_simplified:           0
% 11.78/1.99  inst_num_eq_res_simplified:             0
% 11.78/1.99  inst_num_child_elim:                    0
% 11.78/1.99  inst_num_of_dismatching_blockings:      4023
% 11.78/1.99  inst_num_of_non_proper_insts:           3778
% 11.78/1.99  inst_num_of_duplicates:                 0
% 11.78/1.99  inst_inst_num_from_inst_to_res:         0
% 11.78/1.99  inst_dismatching_checking_time:         0.
% 11.78/1.99  
% 11.78/1.99  ------ Resolution
% 11.78/1.99  
% 11.78/1.99  res_num_of_clauses:                     0
% 11.78/1.99  res_num_in_passive:                     0
% 11.78/1.99  res_num_in_active:                      0
% 11.78/1.99  res_num_of_loops:                       106
% 11.78/1.99  res_forward_subset_subsumed:            866
% 11.78/1.99  res_backward_subset_subsumed:           2
% 11.78/1.99  res_forward_subsumed:                   0
% 11.78/1.99  res_backward_subsumed:                  0
% 11.78/1.99  res_forward_subsumption_resolution:     0
% 11.78/1.99  res_backward_subsumption_resolution:    0
% 11.78/1.99  res_clause_to_clause_subsumption:       47718
% 11.78/1.99  res_orphan_elimination:                 0
% 11.78/1.99  res_tautology_del:                      290
% 11.78/1.99  res_num_eq_res_simplified:              0
% 11.78/1.99  res_num_sel_changes:                    0
% 11.78/1.99  res_moves_from_active_to_pass:          0
% 11.78/1.99  
% 11.78/1.99  ------ Superposition
% 11.78/1.99  
% 11.78/1.99  sup_time_total:                         0.
% 11.78/1.99  sup_time_generating:                    0.
% 11.78/1.99  sup_time_sim_full:                      0.
% 11.78/1.99  sup_time_sim_immed:                     0.
% 11.78/1.99  
% 11.78/1.99  sup_num_of_clauses:                     2213
% 11.78/1.99  sup_num_in_active:                      103
% 11.78/1.99  sup_num_in_passive:                     2110
% 11.78/1.99  sup_num_of_loops:                       116
% 11.78/1.99  sup_fw_superposition:                   5532
% 11.78/1.99  sup_bw_superposition:                   3604
% 11.78/1.99  sup_immediate_simplified:               5107
% 11.78/1.99  sup_given_eliminated:                   3
% 11.78/1.99  comparisons_done:                       0
% 11.78/1.99  comparisons_avoided:                    6
% 11.78/1.99  
% 11.78/1.99  ------ Simplifications
% 11.78/1.99  
% 11.78/1.99  
% 11.78/1.99  sim_fw_subset_subsumed:                 2
% 11.78/1.99  sim_bw_subset_subsumed:                 0
% 11.78/1.99  sim_fw_subsumed:                        328
% 11.78/1.99  sim_bw_subsumed:                        19
% 11.78/1.99  sim_fw_subsumption_res:                 0
% 11.78/1.99  sim_bw_subsumption_res:                 0
% 11.78/1.99  sim_tautology_del:                      0
% 11.78/1.99  sim_eq_tautology_del:                   1061
% 11.78/1.99  sim_eq_res_simp:                        0
% 11.78/1.99  sim_fw_demodulated:                     4282
% 11.78/1.99  sim_bw_demodulated:                     90
% 11.78/1.99  sim_light_normalised:                   1411
% 11.78/1.99  sim_joinable_taut:                      538
% 11.78/1.99  sim_joinable_simp:                      0
% 11.78/1.99  sim_ac_normalised:                      0
% 11.78/1.99  sim_smt_subsumption:                    0
% 11.78/1.99  
%------------------------------------------------------------------------------
