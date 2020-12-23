%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:01 EST 2020

% Result     : Theorem 7.91s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :  167 (29844 expanded)
%              Number of clauses        :   99 (8382 expanded)
%              Number of leaves         :   24 (8640 expanded)
%              Depth                    :   37
%              Number of atoms          :  286 (30425 expanded)
%              Number of equality atoms :  223 (30362 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f48,f44])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_315,negated_conjecture,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_21,c_10,c_1])).

cnf(c_928,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_0,c_315])).

cnf(c_1268,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_928,c_10])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1123,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_1274,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1268,c_1123])).

cnf(c_1446,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_1274])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1447,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11,c_1274])).

cnf(c_1451,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_1447,c_9])).

cnf(c_1455,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1451,c_1274])).

cnf(c_1721,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1446,c_1455])).

cnf(c_1457,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,sK3)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_1455])).

cnf(c_1463,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1455,c_10])).

cnf(c_1899,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11,c_1463])).

cnf(c_1919,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = sK3 ),
    inference(demodulation,[status(thm)],[c_1899,c_9])).

cnf(c_2297,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),X0) = sK3 ),
    inference(superposition,[status(thm)],[c_1457,c_1919])).

cnf(c_3731,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X0,X1)) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_2297,c_10])).

cnf(c_557,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_6314,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1455,c_557])).

cnf(c_6861,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(sK3,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_557,c_6314])).

cnf(c_15696,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),sK3),k5_xboole_0(X2,k5_xboole_0(X1,X0))) = k5_xboole_0(sK3,k5_xboole_0(sK3,X2)) ),
    inference(superposition,[status(thm)],[c_6861,c_3731])).

cnf(c_558,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_6304,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_9,c_557])).

cnf(c_6759,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),sK3) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1455,c_6304])).

cnf(c_6819,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),sK3) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6759,c_1123])).

cnf(c_9130,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),sK3) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_558,c_6819])).

cnf(c_15778,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X0))) = k5_xboole_0(sK3,k5_xboole_0(sK3,X2)) ),
    inference(light_normalisation,[status(thm)],[c_15696,c_9130])).

cnf(c_6853,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(sK3,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_6314])).

cnf(c_10491,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(k5_xboole_0(sK3,X1),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_6853,c_10])).

cnf(c_1895,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_1463])).

cnf(c_9055,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1895,c_558])).

cnf(c_556,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_4335,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_556,c_1463])).

cnf(c_4346,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_4335,c_10])).

cnf(c_4336,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_556,c_1455])).

cnf(c_4645,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_4336])).

cnf(c_5262,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_1895,c_10])).

cnf(c_5291,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_5262,c_4346])).

cnf(c_9247,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_9055,c_4346,c_4645,c_5291])).

cnf(c_10536,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_10491,c_9247])).

cnf(c_1726,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,sK3))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_10,c_1457])).

cnf(c_4917,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,sK3),X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_1726])).

cnf(c_4938,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1726,c_10])).

cnf(c_4956,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_4938,c_10])).

cnf(c_10537,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_10536,c_4917,c_4956,c_9247])).

cnf(c_15779,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X0))) = X2 ),
    inference(demodulation,[status(thm)],[c_15778,c_1455,c_10537])).

cnf(c_17326,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X0)) = k5_xboole_0(X1,sK3) ),
    inference(superposition,[status(thm)],[c_3731,c_15779])).

cnf(c_2296,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),X0) = sK3 ),
    inference(superposition,[status(thm)],[c_1455,c_1919])).

cnf(c_3037,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_2296,c_10])).

cnf(c_18086,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X1,sK3)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_17326,c_3037])).

cnf(c_18162,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X1,sK3)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_18086,c_1455])).

cnf(c_18397,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),X1) = k5_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_18162,c_1726])).

cnf(c_24296,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X0)),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_1721,c_18397])).

cnf(c_1718,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0)) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_11,c_1446])).

cnf(c_1732,plain,
    ( k5_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(demodulation,[status(thm)],[c_1718,c_9])).

cnf(c_1715,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_1446])).

cnf(c_3241,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1715,c_1455])).

cnf(c_4285,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11,c_556])).

cnf(c_4350,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_4285,c_9])).

cnf(c_17414,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_15779,c_4350])).

cnf(c_20595,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0) ),
    inference(superposition,[status(thm)],[c_3241,c_17414])).

cnf(c_20881,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) = k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0) ),
    inference(demodulation,[status(thm)],[c_20595,c_10537])).

cnf(c_24523,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0))) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_24296,c_1455,c_1732,c_20881])).

cnf(c_25475,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0),k5_xboole_0(sK3,k5_xboole_0(sK3,X0))) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_1721,c_24523])).

cnf(c_25676,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)),X0) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_25475,c_1455,c_20881])).

cnf(c_8,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_540,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1371,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_540])).

cnf(c_3973,plain,
    ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1451,c_1371])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_542,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_27858,plain,
    ( k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_3973,c_542])).

cnf(c_27861,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)),X0) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_25676,c_25676,c_27858])).

cnf(c_6377,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,sK3)))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_557,c_4336])).

cnf(c_28009,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(X1,sK3)))),k5_xboole_0(X1,X0)) = k5_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_27861,c_6377])).

cnf(c_1729,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,sK3),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1457,c_10])).

cnf(c_9142,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,sK3)))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_558,c_1729])).

cnf(c_24437,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,sK3)))),k5_xboole_0(X2,X1)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_18397,c_6377])).

cnf(c_24442,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X2)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_24437,c_1455,c_9142])).

cnf(c_28017,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28009,c_11,c_9142,c_10537,c_24442])).

cnf(c_18,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_533,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_29493,plain,
    ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_28017,c_533])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_200,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | k5_xboole_0(X3,X4) != X2
    | k3_xboole_0(X3,X4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_201,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_530,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_201])).

cnf(c_2069,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1123,c_530])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_929,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_2075,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2069,c_929])).

cnf(c_2103,plain,
    ( r2_hidden(sK2,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2075])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29493,c_2103])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:18:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.91/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/1.50  
% 7.91/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.91/1.50  
% 7.91/1.50  ------  iProver source info
% 7.91/1.50  
% 7.91/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.91/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.91/1.50  git: non_committed_changes: false
% 7.91/1.50  git: last_make_outside_of_git: false
% 7.91/1.50  
% 7.91/1.50  ------ 
% 7.91/1.50  
% 7.91/1.50  ------ Input Options
% 7.91/1.50  
% 7.91/1.50  --out_options                           all
% 7.91/1.50  --tptp_safe_out                         true
% 7.91/1.50  --problem_path                          ""
% 7.91/1.50  --include_path                          ""
% 7.91/1.50  --clausifier                            res/vclausify_rel
% 7.91/1.50  --clausifier_options                    ""
% 7.91/1.50  --stdin                                 false
% 7.91/1.50  --stats_out                             all
% 7.91/1.50  
% 7.91/1.50  ------ General Options
% 7.91/1.50  
% 7.91/1.50  --fof                                   false
% 7.91/1.50  --time_out_real                         305.
% 7.91/1.50  --time_out_virtual                      -1.
% 7.91/1.50  --symbol_type_check                     false
% 7.91/1.50  --clausify_out                          false
% 7.91/1.50  --sig_cnt_out                           false
% 7.91/1.50  --trig_cnt_out                          false
% 7.91/1.50  --trig_cnt_out_tolerance                1.
% 7.91/1.50  --trig_cnt_out_sk_spl                   false
% 7.91/1.50  --abstr_cl_out                          false
% 7.91/1.50  
% 7.91/1.50  ------ Global Options
% 7.91/1.50  
% 7.91/1.50  --schedule                              default
% 7.91/1.50  --add_important_lit                     false
% 7.91/1.50  --prop_solver_per_cl                    1000
% 7.91/1.50  --min_unsat_core                        false
% 7.91/1.50  --soft_assumptions                      false
% 7.91/1.50  --soft_lemma_size                       3
% 7.91/1.50  --prop_impl_unit_size                   0
% 7.91/1.50  --prop_impl_unit                        []
% 7.91/1.50  --share_sel_clauses                     true
% 7.91/1.50  --reset_solvers                         false
% 7.91/1.50  --bc_imp_inh                            [conj_cone]
% 7.91/1.50  --conj_cone_tolerance                   3.
% 7.91/1.50  --extra_neg_conj                        none
% 7.91/1.50  --large_theory_mode                     true
% 7.91/1.50  --prolific_symb_bound                   200
% 7.91/1.50  --lt_threshold                          2000
% 7.91/1.50  --clause_weak_htbl                      true
% 7.91/1.50  --gc_record_bc_elim                     false
% 7.91/1.50  
% 7.91/1.50  ------ Preprocessing Options
% 7.91/1.50  
% 7.91/1.50  --preprocessing_flag                    true
% 7.91/1.50  --time_out_prep_mult                    0.1
% 7.91/1.50  --splitting_mode                        input
% 7.91/1.50  --splitting_grd                         true
% 7.91/1.50  --splitting_cvd                         false
% 7.91/1.50  --splitting_cvd_svl                     false
% 7.91/1.50  --splitting_nvd                         32
% 7.91/1.50  --sub_typing                            true
% 7.91/1.50  --prep_gs_sim                           true
% 7.91/1.50  --prep_unflatten                        true
% 7.91/1.50  --prep_res_sim                          true
% 7.91/1.50  --prep_upred                            true
% 7.91/1.50  --prep_sem_filter                       exhaustive
% 7.91/1.50  --prep_sem_filter_out                   false
% 7.91/1.50  --pred_elim                             true
% 7.91/1.50  --res_sim_input                         true
% 7.91/1.50  --eq_ax_congr_red                       true
% 7.91/1.50  --pure_diseq_elim                       true
% 7.91/1.50  --brand_transform                       false
% 7.91/1.50  --non_eq_to_eq                          false
% 7.91/1.50  --prep_def_merge                        true
% 7.91/1.50  --prep_def_merge_prop_impl              false
% 7.91/1.50  --prep_def_merge_mbd                    true
% 7.91/1.50  --prep_def_merge_tr_red                 false
% 7.91/1.50  --prep_def_merge_tr_cl                  false
% 7.91/1.50  --smt_preprocessing                     true
% 7.91/1.50  --smt_ac_axioms                         fast
% 7.91/1.50  --preprocessed_out                      false
% 7.91/1.50  --preprocessed_stats                    false
% 7.91/1.50  
% 7.91/1.50  ------ Abstraction refinement Options
% 7.91/1.50  
% 7.91/1.50  --abstr_ref                             []
% 7.91/1.50  --abstr_ref_prep                        false
% 7.91/1.50  --abstr_ref_until_sat                   false
% 7.91/1.50  --abstr_ref_sig_restrict                funpre
% 7.91/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.91/1.50  --abstr_ref_under                       []
% 7.91/1.50  
% 7.91/1.50  ------ SAT Options
% 7.91/1.50  
% 7.91/1.50  --sat_mode                              false
% 7.91/1.50  --sat_fm_restart_options                ""
% 7.91/1.50  --sat_gr_def                            false
% 7.91/1.50  --sat_epr_types                         true
% 7.91/1.50  --sat_non_cyclic_types                  false
% 7.91/1.50  --sat_finite_models                     false
% 7.91/1.50  --sat_fm_lemmas                         false
% 7.91/1.50  --sat_fm_prep                           false
% 7.91/1.50  --sat_fm_uc_incr                        true
% 7.91/1.50  --sat_out_model                         small
% 7.91/1.50  --sat_out_clauses                       false
% 7.91/1.50  
% 7.91/1.50  ------ QBF Options
% 7.91/1.50  
% 7.91/1.50  --qbf_mode                              false
% 7.91/1.50  --qbf_elim_univ                         false
% 7.91/1.50  --qbf_dom_inst                          none
% 7.91/1.50  --qbf_dom_pre_inst                      false
% 7.91/1.50  --qbf_sk_in                             false
% 7.91/1.50  --qbf_pred_elim                         true
% 7.91/1.50  --qbf_split                             512
% 7.91/1.50  
% 7.91/1.50  ------ BMC1 Options
% 7.91/1.50  
% 7.91/1.50  --bmc1_incremental                      false
% 7.91/1.50  --bmc1_axioms                           reachable_all
% 7.91/1.50  --bmc1_min_bound                        0
% 7.91/1.50  --bmc1_max_bound                        -1
% 7.91/1.50  --bmc1_max_bound_default                -1
% 7.91/1.50  --bmc1_symbol_reachability              true
% 7.91/1.50  --bmc1_property_lemmas                  false
% 7.91/1.50  --bmc1_k_induction                      false
% 7.91/1.50  --bmc1_non_equiv_states                 false
% 7.91/1.50  --bmc1_deadlock                         false
% 7.91/1.50  --bmc1_ucm                              false
% 7.91/1.50  --bmc1_add_unsat_core                   none
% 7.91/1.50  --bmc1_unsat_core_children              false
% 7.91/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.91/1.50  --bmc1_out_stat                         full
% 7.91/1.50  --bmc1_ground_init                      false
% 7.91/1.50  --bmc1_pre_inst_next_state              false
% 7.91/1.50  --bmc1_pre_inst_state                   false
% 7.91/1.50  --bmc1_pre_inst_reach_state             false
% 7.91/1.50  --bmc1_out_unsat_core                   false
% 7.91/1.50  --bmc1_aig_witness_out                  false
% 7.91/1.50  --bmc1_verbose                          false
% 7.91/1.50  --bmc1_dump_clauses_tptp                false
% 7.91/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.91/1.50  --bmc1_dump_file                        -
% 7.91/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.91/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.91/1.50  --bmc1_ucm_extend_mode                  1
% 7.91/1.50  --bmc1_ucm_init_mode                    2
% 7.91/1.50  --bmc1_ucm_cone_mode                    none
% 7.91/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.91/1.50  --bmc1_ucm_relax_model                  4
% 7.91/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.91/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.91/1.50  --bmc1_ucm_layered_model                none
% 7.91/1.50  --bmc1_ucm_max_lemma_size               10
% 7.91/1.50  
% 7.91/1.50  ------ AIG Options
% 7.91/1.50  
% 7.91/1.50  --aig_mode                              false
% 7.91/1.50  
% 7.91/1.50  ------ Instantiation Options
% 7.91/1.50  
% 7.91/1.50  --instantiation_flag                    true
% 7.91/1.50  --inst_sos_flag                         true
% 7.91/1.50  --inst_sos_phase                        true
% 7.91/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.91/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.91/1.50  --inst_lit_sel_side                     num_symb
% 7.91/1.50  --inst_solver_per_active                1400
% 7.91/1.50  --inst_solver_calls_frac                1.
% 7.91/1.50  --inst_passive_queue_type               priority_queues
% 7.91/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.91/1.50  --inst_passive_queues_freq              [25;2]
% 7.91/1.50  --inst_dismatching                      true
% 7.91/1.50  --inst_eager_unprocessed_to_passive     true
% 7.91/1.50  --inst_prop_sim_given                   true
% 7.91/1.50  --inst_prop_sim_new                     false
% 7.91/1.50  --inst_subs_new                         false
% 7.91/1.50  --inst_eq_res_simp                      false
% 7.91/1.50  --inst_subs_given                       false
% 7.91/1.50  --inst_orphan_elimination               true
% 7.91/1.50  --inst_learning_loop_flag               true
% 7.91/1.50  --inst_learning_start                   3000
% 7.91/1.50  --inst_learning_factor                  2
% 7.91/1.50  --inst_start_prop_sim_after_learn       3
% 7.91/1.50  --inst_sel_renew                        solver
% 7.91/1.50  --inst_lit_activity_flag                true
% 7.91/1.50  --inst_restr_to_given                   false
% 7.91/1.50  --inst_activity_threshold               500
% 7.91/1.50  --inst_out_proof                        true
% 7.91/1.50  
% 7.91/1.50  ------ Resolution Options
% 7.91/1.50  
% 7.91/1.50  --resolution_flag                       true
% 7.91/1.50  --res_lit_sel                           adaptive
% 7.91/1.50  --res_lit_sel_side                      none
% 7.91/1.50  --res_ordering                          kbo
% 7.91/1.50  --res_to_prop_solver                    active
% 7.91/1.50  --res_prop_simpl_new                    false
% 7.91/1.50  --res_prop_simpl_given                  true
% 7.91/1.50  --res_passive_queue_type                priority_queues
% 7.91/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.91/1.50  --res_passive_queues_freq               [15;5]
% 7.91/1.50  --res_forward_subs                      full
% 7.91/1.50  --res_backward_subs                     full
% 7.91/1.50  --res_forward_subs_resolution           true
% 7.91/1.50  --res_backward_subs_resolution          true
% 7.91/1.50  --res_orphan_elimination                true
% 7.91/1.50  --res_time_limit                        2.
% 7.91/1.50  --res_out_proof                         true
% 7.91/1.50  
% 7.91/1.50  ------ Superposition Options
% 7.91/1.50  
% 7.91/1.50  --superposition_flag                    true
% 7.91/1.50  --sup_passive_queue_type                priority_queues
% 7.91/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.91/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.91/1.50  --demod_completeness_check              fast
% 7.91/1.50  --demod_use_ground                      true
% 7.91/1.50  --sup_to_prop_solver                    passive
% 7.91/1.50  --sup_prop_simpl_new                    true
% 7.91/1.50  --sup_prop_simpl_given                  true
% 7.91/1.50  --sup_fun_splitting                     true
% 7.91/1.50  --sup_smt_interval                      50000
% 7.91/1.50  
% 7.91/1.50  ------ Superposition Simplification Setup
% 7.91/1.50  
% 7.91/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.91/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.91/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.91/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.91/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.91/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.91/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.91/1.50  --sup_immed_triv                        [TrivRules]
% 7.91/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.50  --sup_immed_bw_main                     []
% 7.91/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.91/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.91/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.50  --sup_input_bw                          []
% 7.91/1.50  
% 7.91/1.50  ------ Combination Options
% 7.91/1.50  
% 7.91/1.50  --comb_res_mult                         3
% 7.91/1.50  --comb_sup_mult                         2
% 7.91/1.50  --comb_inst_mult                        10
% 7.91/1.50  
% 7.91/1.50  ------ Debug Options
% 7.91/1.50  
% 7.91/1.50  --dbg_backtrace                         false
% 7.91/1.50  --dbg_dump_prop_clauses                 false
% 7.91/1.50  --dbg_dump_prop_clauses_file            -
% 7.91/1.50  --dbg_out_stat                          false
% 7.91/1.50  ------ Parsing...
% 7.91/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.91/1.50  
% 7.91/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.91/1.50  
% 7.91/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.91/1.50  
% 7.91/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.50  ------ Proving...
% 7.91/1.50  ------ Problem Properties 
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  clauses                                 21
% 7.91/1.50  conjectures                             1
% 7.91/1.50  EPR                                     1
% 7.91/1.50  Horn                                    19
% 7.91/1.50  unary                                   14
% 7.91/1.50  binary                                  2
% 7.91/1.50  lits                                    36
% 7.91/1.50  lits eq                                 22
% 7.91/1.50  fd_pure                                 0
% 7.91/1.50  fd_pseudo                               0
% 7.91/1.50  fd_cond                                 0
% 7.91/1.50  fd_pseudo_cond                          4
% 7.91/1.50  AC symbols                              1
% 7.91/1.50  
% 7.91/1.50  ------ Schedule dynamic 5 is on 
% 7.91/1.50  
% 7.91/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  ------ 
% 7.91/1.50  Current options:
% 7.91/1.50  ------ 
% 7.91/1.50  
% 7.91/1.50  ------ Input Options
% 7.91/1.50  
% 7.91/1.50  --out_options                           all
% 7.91/1.50  --tptp_safe_out                         true
% 7.91/1.50  --problem_path                          ""
% 7.91/1.50  --include_path                          ""
% 7.91/1.50  --clausifier                            res/vclausify_rel
% 7.91/1.50  --clausifier_options                    ""
% 7.91/1.50  --stdin                                 false
% 7.91/1.50  --stats_out                             all
% 7.91/1.50  
% 7.91/1.50  ------ General Options
% 7.91/1.50  
% 7.91/1.50  --fof                                   false
% 7.91/1.50  --time_out_real                         305.
% 7.91/1.50  --time_out_virtual                      -1.
% 7.91/1.50  --symbol_type_check                     false
% 7.91/1.50  --clausify_out                          false
% 7.91/1.50  --sig_cnt_out                           false
% 7.91/1.50  --trig_cnt_out                          false
% 7.91/1.50  --trig_cnt_out_tolerance                1.
% 7.91/1.50  --trig_cnt_out_sk_spl                   false
% 7.91/1.50  --abstr_cl_out                          false
% 7.91/1.50  
% 7.91/1.50  ------ Global Options
% 7.91/1.50  
% 7.91/1.50  --schedule                              default
% 7.91/1.50  --add_important_lit                     false
% 7.91/1.50  --prop_solver_per_cl                    1000
% 7.91/1.50  --min_unsat_core                        false
% 7.91/1.50  --soft_assumptions                      false
% 7.91/1.50  --soft_lemma_size                       3
% 7.91/1.50  --prop_impl_unit_size                   0
% 7.91/1.50  --prop_impl_unit                        []
% 7.91/1.50  --share_sel_clauses                     true
% 7.91/1.50  --reset_solvers                         false
% 7.91/1.50  --bc_imp_inh                            [conj_cone]
% 7.91/1.50  --conj_cone_tolerance                   3.
% 7.91/1.50  --extra_neg_conj                        none
% 7.91/1.50  --large_theory_mode                     true
% 7.91/1.50  --prolific_symb_bound                   200
% 7.91/1.50  --lt_threshold                          2000
% 7.91/1.50  --clause_weak_htbl                      true
% 7.91/1.50  --gc_record_bc_elim                     false
% 7.91/1.50  
% 7.91/1.50  ------ Preprocessing Options
% 7.91/1.50  
% 7.91/1.50  --preprocessing_flag                    true
% 7.91/1.50  --time_out_prep_mult                    0.1
% 7.91/1.50  --splitting_mode                        input
% 7.91/1.50  --splitting_grd                         true
% 7.91/1.50  --splitting_cvd                         false
% 7.91/1.50  --splitting_cvd_svl                     false
% 7.91/1.50  --splitting_nvd                         32
% 7.91/1.50  --sub_typing                            true
% 7.91/1.50  --prep_gs_sim                           true
% 7.91/1.50  --prep_unflatten                        true
% 7.91/1.50  --prep_res_sim                          true
% 7.91/1.50  --prep_upred                            true
% 7.91/1.50  --prep_sem_filter                       exhaustive
% 7.91/1.50  --prep_sem_filter_out                   false
% 7.91/1.50  --pred_elim                             true
% 7.91/1.50  --res_sim_input                         true
% 7.91/1.50  --eq_ax_congr_red                       true
% 7.91/1.50  --pure_diseq_elim                       true
% 7.91/1.50  --brand_transform                       false
% 7.91/1.50  --non_eq_to_eq                          false
% 7.91/1.50  --prep_def_merge                        true
% 7.91/1.50  --prep_def_merge_prop_impl              false
% 7.91/1.50  --prep_def_merge_mbd                    true
% 7.91/1.50  --prep_def_merge_tr_red                 false
% 7.91/1.50  --prep_def_merge_tr_cl                  false
% 7.91/1.50  --smt_preprocessing                     true
% 7.91/1.50  --smt_ac_axioms                         fast
% 7.91/1.50  --preprocessed_out                      false
% 7.91/1.50  --preprocessed_stats                    false
% 7.91/1.50  
% 7.91/1.50  ------ Abstraction refinement Options
% 7.91/1.50  
% 7.91/1.50  --abstr_ref                             []
% 7.91/1.50  --abstr_ref_prep                        false
% 7.91/1.50  --abstr_ref_until_sat                   false
% 7.91/1.50  --abstr_ref_sig_restrict                funpre
% 7.91/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.91/1.50  --abstr_ref_under                       []
% 7.91/1.50  
% 7.91/1.50  ------ SAT Options
% 7.91/1.50  
% 7.91/1.50  --sat_mode                              false
% 7.91/1.50  --sat_fm_restart_options                ""
% 7.91/1.50  --sat_gr_def                            false
% 7.91/1.50  --sat_epr_types                         true
% 7.91/1.50  --sat_non_cyclic_types                  false
% 7.91/1.50  --sat_finite_models                     false
% 7.91/1.50  --sat_fm_lemmas                         false
% 7.91/1.50  --sat_fm_prep                           false
% 7.91/1.50  --sat_fm_uc_incr                        true
% 7.91/1.50  --sat_out_model                         small
% 7.91/1.50  --sat_out_clauses                       false
% 7.91/1.50  
% 7.91/1.50  ------ QBF Options
% 7.91/1.50  
% 7.91/1.50  --qbf_mode                              false
% 7.91/1.50  --qbf_elim_univ                         false
% 7.91/1.50  --qbf_dom_inst                          none
% 7.91/1.50  --qbf_dom_pre_inst                      false
% 7.91/1.50  --qbf_sk_in                             false
% 7.91/1.50  --qbf_pred_elim                         true
% 7.91/1.50  --qbf_split                             512
% 7.91/1.50  
% 7.91/1.50  ------ BMC1 Options
% 7.91/1.50  
% 7.91/1.50  --bmc1_incremental                      false
% 7.91/1.50  --bmc1_axioms                           reachable_all
% 7.91/1.50  --bmc1_min_bound                        0
% 7.91/1.50  --bmc1_max_bound                        -1
% 7.91/1.50  --bmc1_max_bound_default                -1
% 7.91/1.50  --bmc1_symbol_reachability              true
% 7.91/1.50  --bmc1_property_lemmas                  false
% 7.91/1.50  --bmc1_k_induction                      false
% 7.91/1.50  --bmc1_non_equiv_states                 false
% 7.91/1.50  --bmc1_deadlock                         false
% 7.91/1.50  --bmc1_ucm                              false
% 7.91/1.50  --bmc1_add_unsat_core                   none
% 7.91/1.50  --bmc1_unsat_core_children              false
% 7.91/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.91/1.50  --bmc1_out_stat                         full
% 7.91/1.50  --bmc1_ground_init                      false
% 7.91/1.50  --bmc1_pre_inst_next_state              false
% 7.91/1.50  --bmc1_pre_inst_state                   false
% 7.91/1.50  --bmc1_pre_inst_reach_state             false
% 7.91/1.50  --bmc1_out_unsat_core                   false
% 7.91/1.50  --bmc1_aig_witness_out                  false
% 7.91/1.50  --bmc1_verbose                          false
% 7.91/1.50  --bmc1_dump_clauses_tptp                false
% 7.91/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.91/1.50  --bmc1_dump_file                        -
% 7.91/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.91/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.91/1.50  --bmc1_ucm_extend_mode                  1
% 7.91/1.50  --bmc1_ucm_init_mode                    2
% 7.91/1.50  --bmc1_ucm_cone_mode                    none
% 7.91/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.91/1.50  --bmc1_ucm_relax_model                  4
% 7.91/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.91/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.91/1.50  --bmc1_ucm_layered_model                none
% 7.91/1.50  --bmc1_ucm_max_lemma_size               10
% 7.91/1.50  
% 7.91/1.50  ------ AIG Options
% 7.91/1.50  
% 7.91/1.50  --aig_mode                              false
% 7.91/1.50  
% 7.91/1.50  ------ Instantiation Options
% 7.91/1.50  
% 7.91/1.50  --instantiation_flag                    true
% 7.91/1.50  --inst_sos_flag                         true
% 7.91/1.50  --inst_sos_phase                        true
% 7.91/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.91/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.91/1.50  --inst_lit_sel_side                     none
% 7.91/1.50  --inst_solver_per_active                1400
% 7.91/1.50  --inst_solver_calls_frac                1.
% 7.91/1.50  --inst_passive_queue_type               priority_queues
% 7.91/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.91/1.50  --inst_passive_queues_freq              [25;2]
% 7.91/1.50  --inst_dismatching                      true
% 7.91/1.50  --inst_eager_unprocessed_to_passive     true
% 7.91/1.50  --inst_prop_sim_given                   true
% 7.91/1.50  --inst_prop_sim_new                     false
% 7.91/1.50  --inst_subs_new                         false
% 7.91/1.50  --inst_eq_res_simp                      false
% 7.91/1.50  --inst_subs_given                       false
% 7.91/1.50  --inst_orphan_elimination               true
% 7.91/1.50  --inst_learning_loop_flag               true
% 7.91/1.50  --inst_learning_start                   3000
% 7.91/1.50  --inst_learning_factor                  2
% 7.91/1.50  --inst_start_prop_sim_after_learn       3
% 7.91/1.50  --inst_sel_renew                        solver
% 7.91/1.50  --inst_lit_activity_flag                true
% 7.91/1.50  --inst_restr_to_given                   false
% 7.91/1.50  --inst_activity_threshold               500
% 7.91/1.50  --inst_out_proof                        true
% 7.91/1.50  
% 7.91/1.50  ------ Resolution Options
% 7.91/1.50  
% 7.91/1.50  --resolution_flag                       false
% 7.91/1.50  --res_lit_sel                           adaptive
% 7.91/1.50  --res_lit_sel_side                      none
% 7.91/1.50  --res_ordering                          kbo
% 7.91/1.50  --res_to_prop_solver                    active
% 7.91/1.50  --res_prop_simpl_new                    false
% 7.91/1.50  --res_prop_simpl_given                  true
% 7.91/1.50  --res_passive_queue_type                priority_queues
% 7.91/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.91/1.50  --res_passive_queues_freq               [15;5]
% 7.91/1.50  --res_forward_subs                      full
% 7.91/1.50  --res_backward_subs                     full
% 7.91/1.50  --res_forward_subs_resolution           true
% 7.91/1.50  --res_backward_subs_resolution          true
% 7.91/1.50  --res_orphan_elimination                true
% 7.91/1.50  --res_time_limit                        2.
% 7.91/1.50  --res_out_proof                         true
% 7.91/1.50  
% 7.91/1.50  ------ Superposition Options
% 7.91/1.50  
% 7.91/1.50  --superposition_flag                    true
% 7.91/1.50  --sup_passive_queue_type                priority_queues
% 7.91/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.91/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.91/1.50  --demod_completeness_check              fast
% 7.91/1.50  --demod_use_ground                      true
% 7.91/1.50  --sup_to_prop_solver                    passive
% 7.91/1.50  --sup_prop_simpl_new                    true
% 7.91/1.50  --sup_prop_simpl_given                  true
% 7.91/1.50  --sup_fun_splitting                     true
% 7.91/1.50  --sup_smt_interval                      50000
% 7.91/1.50  
% 7.91/1.50  ------ Superposition Simplification Setup
% 7.91/1.50  
% 7.91/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.91/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.91/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.91/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.91/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.91/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.91/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.91/1.50  --sup_immed_triv                        [TrivRules]
% 7.91/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.50  --sup_immed_bw_main                     []
% 7.91/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.91/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.91/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.50  --sup_input_bw                          []
% 7.91/1.50  
% 7.91/1.50  ------ Combination Options
% 7.91/1.50  
% 7.91/1.50  --comb_res_mult                         3
% 7.91/1.50  --comb_sup_mult                         2
% 7.91/1.50  --comb_inst_mult                        10
% 7.91/1.50  
% 7.91/1.50  ------ Debug Options
% 7.91/1.50  
% 7.91/1.50  --dbg_backtrace                         false
% 7.91/1.50  --dbg_dump_prop_clauses                 false
% 7.91/1.50  --dbg_dump_prop_clauses_file            -
% 7.91/1.50  --dbg_out_stat                          false
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  ------ Proving...
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  % SZS status Theorem for theBenchmark.p
% 7.91/1.50  
% 7.91/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.91/1.50  
% 7.91/1.50  fof(f11,axiom,(
% 7.91/1.50    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f50,plain,(
% 7.91/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f11])).
% 7.91/1.50  
% 7.91/1.50  fof(f1,axiom,(
% 7.91/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f39,plain,(
% 7.91/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f1])).
% 7.91/1.50  
% 7.91/1.50  fof(f23,conjecture,(
% 7.91/1.50    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f24,negated_conjecture,(
% 7.91/1.50    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 7.91/1.50    inference(negated_conjecture,[],[f23])).
% 7.91/1.50  
% 7.91/1.50  fof(f29,plain,(
% 7.91/1.50    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 7.91/1.50    inference(ennf_transformation,[],[f24])).
% 7.91/1.50  
% 7.91/1.50  fof(f37,plain,(
% 7.91/1.50    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 7.91/1.50    introduced(choice_axiom,[])).
% 7.91/1.50  
% 7.91/1.50  fof(f38,plain,(
% 7.91/1.50    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 7.91/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f37])).
% 7.91/1.50  
% 7.91/1.50  fof(f69,plain,(
% 7.91/1.50    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 7.91/1.50    inference(cnf_transformation,[],[f38])).
% 7.91/1.50  
% 7.91/1.50  fof(f13,axiom,(
% 7.91/1.50    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f52,plain,(
% 7.91/1.50    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f13])).
% 7.91/1.50  
% 7.91/1.50  fof(f15,axiom,(
% 7.91/1.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f61,plain,(
% 7.91/1.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f15])).
% 7.91/1.50  
% 7.91/1.50  fof(f16,axiom,(
% 7.91/1.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f62,plain,(
% 7.91/1.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f16])).
% 7.91/1.50  
% 7.91/1.50  fof(f17,axiom,(
% 7.91/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f63,plain,(
% 7.91/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f17])).
% 7.91/1.50  
% 7.91/1.50  fof(f18,axiom,(
% 7.91/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f64,plain,(
% 7.91/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f18])).
% 7.91/1.50  
% 7.91/1.50  fof(f19,axiom,(
% 7.91/1.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f65,plain,(
% 7.91/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f19])).
% 7.91/1.50  
% 7.91/1.50  fof(f20,axiom,(
% 7.91/1.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f66,plain,(
% 7.91/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f20])).
% 7.91/1.50  
% 7.91/1.50  fof(f21,axiom,(
% 7.91/1.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f67,plain,(
% 7.91/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f21])).
% 7.91/1.50  
% 7.91/1.50  fof(f70,plain,(
% 7.91/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.91/1.50    inference(definition_unfolding,[],[f66,f67])).
% 7.91/1.50  
% 7.91/1.50  fof(f71,plain,(
% 7.91/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.91/1.50    inference(definition_unfolding,[],[f65,f70])).
% 7.91/1.50  
% 7.91/1.50  fof(f72,plain,(
% 7.91/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.91/1.50    inference(definition_unfolding,[],[f64,f71])).
% 7.91/1.50  
% 7.91/1.50  fof(f73,plain,(
% 7.91/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.91/1.50    inference(definition_unfolding,[],[f63,f72])).
% 7.91/1.50  
% 7.91/1.50  fof(f74,plain,(
% 7.91/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.91/1.50    inference(definition_unfolding,[],[f62,f73])).
% 7.91/1.50  
% 7.91/1.50  fof(f75,plain,(
% 7.91/1.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.91/1.50    inference(definition_unfolding,[],[f61,f74])).
% 7.91/1.50  
% 7.91/1.50  fof(f86,plain,(
% 7.91/1.50    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0),
% 7.91/1.50    inference(definition_unfolding,[],[f69,f52,f75])).
% 7.91/1.50  
% 7.91/1.50  fof(f2,axiom,(
% 7.91/1.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f40,plain,(
% 7.91/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f2])).
% 7.91/1.50  
% 7.91/1.50  fof(f10,axiom,(
% 7.91/1.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f49,plain,(
% 7.91/1.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.91/1.50    inference(cnf_transformation,[],[f10])).
% 7.91/1.50  
% 7.91/1.50  fof(f12,axiom,(
% 7.91/1.50    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f51,plain,(
% 7.91/1.50    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.91/1.50    inference(cnf_transformation,[],[f12])).
% 7.91/1.50  
% 7.91/1.50  fof(f9,axiom,(
% 7.91/1.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f48,plain,(
% 7.91/1.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f9])).
% 7.91/1.50  
% 7.91/1.50  fof(f5,axiom,(
% 7.91/1.50    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f44,plain,(
% 7.91/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f5])).
% 7.91/1.50  
% 7.91/1.50  fof(f76,plain,(
% 7.91/1.50    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 7.91/1.50    inference(definition_unfolding,[],[f48,f44])).
% 7.91/1.50  
% 7.91/1.50  fof(f6,axiom,(
% 7.91/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f27,plain,(
% 7.91/1.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.91/1.50    inference(ennf_transformation,[],[f6])).
% 7.91/1.50  
% 7.91/1.50  fof(f45,plain,(
% 7.91/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.91/1.50    inference(cnf_transformation,[],[f27])).
% 7.91/1.50  
% 7.91/1.50  fof(f14,axiom,(
% 7.91/1.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f28,plain,(
% 7.91/1.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.91/1.50    inference(ennf_transformation,[],[f14])).
% 7.91/1.50  
% 7.91/1.50  fof(f32,plain,(
% 7.91/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.91/1.50    inference(nnf_transformation,[],[f28])).
% 7.91/1.50  
% 7.91/1.50  fof(f33,plain,(
% 7.91/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.91/1.50    inference(flattening,[],[f32])).
% 7.91/1.50  
% 7.91/1.50  fof(f34,plain,(
% 7.91/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.91/1.50    inference(rectify,[],[f33])).
% 7.91/1.50  
% 7.91/1.50  fof(f35,plain,(
% 7.91/1.50    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 7.91/1.50    introduced(choice_axiom,[])).
% 7.91/1.50  
% 7.91/1.50  fof(f36,plain,(
% 7.91/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.91/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 7.91/1.50  
% 7.91/1.50  fof(f54,plain,(
% 7.91/1.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.91/1.50    inference(cnf_transformation,[],[f36])).
% 7.91/1.50  
% 7.91/1.50  fof(f83,plain,(
% 7.91/1.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.91/1.50    inference(definition_unfolding,[],[f54,f73])).
% 7.91/1.50  
% 7.91/1.50  fof(f91,plain,(
% 7.91/1.50    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 7.91/1.50    inference(equality_resolution,[],[f83])).
% 7.91/1.50  
% 7.91/1.50  fof(f92,plain,(
% 7.91/1.50    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 7.91/1.50    inference(equality_resolution,[],[f91])).
% 7.91/1.50  
% 7.91/1.50  fof(f3,axiom,(
% 7.91/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f25,plain,(
% 7.91/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.91/1.50    inference(rectify,[],[f3])).
% 7.91/1.50  
% 7.91/1.50  fof(f26,plain,(
% 7.91/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.91/1.50    inference(ennf_transformation,[],[f25])).
% 7.91/1.50  
% 7.91/1.50  fof(f30,plain,(
% 7.91/1.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.91/1.50    introduced(choice_axiom,[])).
% 7.91/1.50  
% 7.91/1.50  fof(f31,plain,(
% 7.91/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.91/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f30])).
% 7.91/1.50  
% 7.91/1.50  fof(f42,plain,(
% 7.91/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.91/1.50    inference(cnf_transformation,[],[f31])).
% 7.91/1.50  
% 7.91/1.50  fof(f4,axiom,(
% 7.91/1.50    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f43,plain,(
% 7.91/1.50    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 7.91/1.50    inference(cnf_transformation,[],[f4])).
% 7.91/1.50  
% 7.91/1.50  fof(f7,axiom,(
% 7.91/1.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.91/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.91/1.50  
% 7.91/1.50  fof(f46,plain,(
% 7.91/1.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.91/1.50    inference(cnf_transformation,[],[f7])).
% 7.91/1.50  
% 7.91/1.50  cnf(c_10,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.91/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_0,plain,
% 7.91/1.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.91/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_21,negated_conjecture,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
% 7.91/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1,plain,
% 7.91/1.50      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.91/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_315,negated_conjecture,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
% 7.91/1.50      inference(theory_normalisation,[status(thm)],[c_21,c_10,c_1]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_928,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k1_xboole_0 ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_0,c_315]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1268,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_928,c_10]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_9,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.91/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1123,plain,
% 7.91/1.50      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1274,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0)) = X0 ),
% 7.91/1.50      inference(light_normalisation,[status(thm)],[c_1268,c_1123]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1446,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0))) = X0 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_10,c_1274]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_11,plain,
% 7.91/1.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.91/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1447,plain,
% 7.91/1.50      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(sK3,k1_xboole_0) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_11,c_1274]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1451,plain,
% 7.91/1.50      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_1447,c_9]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1455,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_1451,c_1274]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1721,plain,
% 7.91/1.50      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(sK3,X0) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1446,c_1455]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1457,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(X0,sK3)) = X0 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1,c_1455]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1463,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X0,X1) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1455,c_10]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1899,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k1_xboole_0) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_11,c_1463]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1919,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = sK3 ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_1899,c_9]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2297,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(X0,sK3),X0) = sK3 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1457,c_1919]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_3731,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X0,X1)) = k5_xboole_0(sK3,X1) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_2297,c_10]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_557,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6314,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(sK3,X1)) = k5_xboole_0(X1,X0) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1455,c_557]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6861,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(sK3,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_557,c_6314]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_15696,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),sK3),k5_xboole_0(X2,k5_xboole_0(X1,X0))) = k5_xboole_0(sK3,k5_xboole_0(sK3,X2)) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_6861,c_3731]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_558,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6304,plain,
% 7.91/1.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_9,c_557]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6759,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(sK3,X0),sK3) = k5_xboole_0(k1_xboole_0,X0) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1455,c_6304]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6819,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(sK3,X0),sK3) = X0 ),
% 7.91/1.50      inference(light_normalisation,[status(thm)],[c_6759,c_1123]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_9130,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),sK3) = k5_xboole_0(X0,X1) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_558,c_6819]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_15778,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X0))) = k5_xboole_0(sK3,k5_xboole_0(sK3,X2)) ),
% 7.91/1.50      inference(light_normalisation,[status(thm)],[c_15696,c_9130]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6853,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(sK3,X1)) = k5_xboole_0(X1,X0) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1,c_6314]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_10491,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(k5_xboole_0(sK3,X1),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_6853,c_10]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1895,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X1,X0) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1,c_1463]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_9055,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1895,c_558]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_556,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4335,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_556,c_1463]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4346,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.91/1.50      inference(light_normalisation,[status(thm)],[c_4335,c_10]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4336,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X0,X1) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_556,c_1455]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4645,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X1,X0) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1,c_4336]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_5262,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK3,X1)),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1895,c_10]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_5291,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.91/1.50      inference(light_normalisation,[status(thm)],[c_5262,c_4346]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_9247,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_9055,c_4346,c_4645,c_5291]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_10536,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_10491,c_9247]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1726,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,sK3))) = k5_xboole_0(X0,X1) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_10,c_1457]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4917,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,sK3),X1)) = k5_xboole_0(X1,X0) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1,c_1726]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4938,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1726,c_10]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4956,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.91/1.50      inference(light_normalisation,[status(thm)],[c_4938,c_10]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_10537,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
% 7.91/1.50      inference(demodulation,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_10536,c_4917,c_4956,c_9247]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_15779,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X0))) = X2 ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_15778,c_1455,c_10537]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_17326,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X0)) = k5_xboole_0(X1,sK3) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_3731,c_15779]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2296,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(sK3,X0),X0) = sK3 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1455,c_1919]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_3037,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(sK3,X1) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_2296,c_10]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_18086,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X1,sK3)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_17326,c_3037]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_18162,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X1,sK3)) = X0 ),
% 7.91/1.50      inference(light_normalisation,[status(thm)],[c_18086,c_1455]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_18397,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),X1) = k5_xboole_0(sK3,X0) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_18162,c_1726]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_24296,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X0)),k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0)) = k5_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1721,c_18397]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1718,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0)) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_11,c_1446]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1732,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_1718,c_9]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1715,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) = X0 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1,c_1446]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_3241,plain,
% 7.91/1.50      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = k5_xboole_0(sK3,X0) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1715,c_1455]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4285,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_11,c_556]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4350,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_4285,c_9]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_17414,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X2,X1) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_15779,c_4350]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_20595,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(sK3,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_3241,c_17414]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_20881,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)) = k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0) ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_20595,c_10537]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_24523,plain,
% 7.91/1.50      ( k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0))) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 7.91/1.50      inference(light_normalisation,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_24296,c_1455,c_1732,c_20881]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_25475,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),X0),k5_xboole_0(sK3,k5_xboole_0(sK3,X0))) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1721,c_24523]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_25676,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)),X0) = k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 7.91/1.50      inference(light_normalisation,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_25475,c_1455,c_20881]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_8,plain,
% 7.91/1.50      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 7.91/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_540,plain,
% 7.91/1.50      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1371,plain,
% 7.91/1.50      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_0,c_540]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_3973,plain,
% 7.91/1.50      ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1451,c_1371]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_5,plain,
% 7.91/1.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.91/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_542,plain,
% 7.91/1.50      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_27858,plain,
% 7.91/1.50      ( k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_3973,c_542]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_27861,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)),X0) = sK3 ),
% 7.91/1.50      inference(light_normalisation,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_25676,c_25676,c_27858]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6377,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,sK3)))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_557,c_4336]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_28009,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k5_xboole_0(X1,sK3)))),k5_xboole_0(X1,X0)) = k5_xboole_0(sK3,sK3) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_27861,c_6377]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_1729,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,sK3),X1)) = k5_xboole_0(X0,X1) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1457,c_10]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_9142,plain,
% 7.91/1.50      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,sK3)))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_558,c_1729]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_24437,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,sK3)))),k5_xboole_0(X2,X1)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_18397,c_6377]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_24442,plain,
% 7.91/1.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X2)) = X1 ),
% 7.91/1.50      inference(light_normalisation,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_24437,c_1455,c_9142]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_28017,plain,
% 7.91/1.50      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 7.91/1.50      inference(demodulation,
% 7.91/1.50                [status(thm)],
% 7.91/1.50                [c_28009,c_11,c_9142,c_10537,c_24442]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_18,plain,
% 7.91/1.50      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 7.91/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_533,plain,
% 7.91/1.50      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_29493,plain,
% 7.91/1.50      ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_28017,c_533]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2,plain,
% 7.91/1.50      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 7.91/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_4,plain,
% 7.91/1.50      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 7.91/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_200,plain,
% 7.91/1.50      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 7.91/1.50      | k5_xboole_0(X3,X4) != X2
% 7.91/1.50      | k3_xboole_0(X3,X4) != X1 ),
% 7.91/1.50      inference(resolution_lifted,[status(thm)],[c_2,c_4]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_201,plain,
% 7.91/1.50      ( ~ r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) ),
% 7.91/1.50      inference(unflattening,[status(thm)],[c_200]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_530,plain,
% 7.91/1.50      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) != iProver_top ),
% 7.91/1.50      inference(predicate_to_equality,[status(thm)],[c_201]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2069,plain,
% 7.91/1.50      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),X1)) != iProver_top ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_1123,c_530]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_6,plain,
% 7.91/1.50      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.91/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_929,plain,
% 7.91/1.50      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.91/1.50      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2075,plain,
% 7.91/1.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.91/1.50      inference(demodulation,[status(thm)],[c_2069,c_929]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(c_2103,plain,
% 7.91/1.50      ( r2_hidden(sK2,k1_xboole_0) != iProver_top ),
% 7.91/1.50      inference(instantiation,[status(thm)],[c_2075]) ).
% 7.91/1.50  
% 7.91/1.50  cnf(contradiction,plain,
% 7.91/1.50      ( $false ),
% 7.91/1.50      inference(minisat,[status(thm)],[c_29493,c_2103]) ).
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.91/1.50  
% 7.91/1.50  ------                               Statistics
% 7.91/1.50  
% 7.91/1.50  ------ General
% 7.91/1.50  
% 7.91/1.50  abstr_ref_over_cycles:                  0
% 7.91/1.50  abstr_ref_under_cycles:                 0
% 7.91/1.50  gc_basic_clause_elim:                   0
% 7.91/1.50  forced_gc_time:                         0
% 7.91/1.50  parsing_time:                           0.008
% 7.91/1.50  unif_index_cands_time:                  0.
% 7.91/1.50  unif_index_add_time:                    0.
% 7.91/1.50  orderings_time:                         0.
% 7.91/1.50  out_proof_time:                         0.009
% 7.91/1.50  total_time:                             0.921
% 7.91/1.50  num_of_symbols:                         43
% 7.91/1.50  num_of_terms:                           41424
% 7.91/1.50  
% 7.91/1.50  ------ Preprocessing
% 7.91/1.50  
% 7.91/1.50  num_of_splits:                          0
% 7.91/1.50  num_of_split_atoms:                     0
% 7.91/1.50  num_of_reused_defs:                     0
% 7.91/1.50  num_eq_ax_congr_red:                    21
% 7.91/1.50  num_of_sem_filtered_clauses:            1
% 7.91/1.50  num_of_subtypes:                        0
% 7.91/1.50  monotx_restored_types:                  0
% 7.91/1.50  sat_num_of_epr_types:                   0
% 7.91/1.50  sat_num_of_non_cyclic_types:            0
% 7.91/1.50  sat_guarded_non_collapsed_types:        0
% 7.91/1.50  num_pure_diseq_elim:                    0
% 7.91/1.50  simp_replaced_by:                       0
% 7.91/1.50  res_preprocessed:                       102
% 7.91/1.50  prep_upred:                             0
% 7.91/1.50  prep_unflattend:                        12
% 7.91/1.50  smt_new_axioms:                         0
% 7.91/1.50  pred_elim_cands:                        2
% 7.91/1.50  pred_elim:                              1
% 7.91/1.50  pred_elim_cl:                           1
% 7.91/1.50  pred_elim_cycles:                       4
% 7.91/1.50  merged_defs:                            0
% 7.91/1.50  merged_defs_ncl:                        0
% 7.91/1.50  bin_hyper_res:                          0
% 7.91/1.50  prep_cycles:                            4
% 7.91/1.50  pred_elim_time:                         0.015
% 7.91/1.50  splitting_time:                         0.
% 7.91/1.50  sem_filter_time:                        0.
% 7.91/1.50  monotx_time:                            0.
% 7.91/1.50  subtype_inf_time:                       0.
% 7.91/1.50  
% 7.91/1.50  ------ Problem properties
% 7.91/1.50  
% 7.91/1.50  clauses:                                21
% 7.91/1.50  conjectures:                            1
% 7.91/1.50  epr:                                    1
% 7.91/1.50  horn:                                   19
% 7.91/1.50  ground:                                 1
% 7.91/1.50  unary:                                  14
% 7.91/1.50  binary:                                 2
% 7.91/1.50  lits:                                   36
% 7.91/1.50  lits_eq:                                22
% 7.91/1.50  fd_pure:                                0
% 7.91/1.50  fd_pseudo:                              0
% 7.91/1.50  fd_cond:                                0
% 7.91/1.50  fd_pseudo_cond:                         4
% 7.91/1.50  ac_symbols:                             1
% 7.91/1.50  
% 7.91/1.50  ------ Propositional Solver
% 7.91/1.50  
% 7.91/1.50  prop_solver_calls:                      31
% 7.91/1.50  prop_fast_solver_calls:                 563
% 7.91/1.50  smt_solver_calls:                       0
% 7.91/1.50  smt_fast_solver_calls:                  0
% 7.91/1.50  prop_num_of_clauses:                    6997
% 7.91/1.50  prop_preprocess_simplified:             13912
% 7.91/1.50  prop_fo_subsumed:                       0
% 7.91/1.50  prop_solver_time:                       0.
% 7.91/1.50  smt_solver_time:                        0.
% 7.91/1.50  smt_fast_solver_time:                   0.
% 7.91/1.50  prop_fast_solver_time:                  0.
% 7.91/1.50  prop_unsat_core_time:                   0.
% 7.91/1.50  
% 7.91/1.50  ------ QBF
% 7.91/1.50  
% 7.91/1.50  qbf_q_res:                              0
% 7.91/1.50  qbf_num_tautologies:                    0
% 7.91/1.50  qbf_prep_cycles:                        0
% 7.91/1.50  
% 7.91/1.50  ------ BMC1
% 7.91/1.50  
% 7.91/1.50  bmc1_current_bound:                     -1
% 7.91/1.50  bmc1_last_solved_bound:                 -1
% 7.91/1.50  bmc1_unsat_core_size:                   -1
% 7.91/1.50  bmc1_unsat_core_parents_size:           -1
% 7.91/1.50  bmc1_merge_next_fun:                    0
% 7.91/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.91/1.50  
% 7.91/1.50  ------ Instantiation
% 7.91/1.50  
% 7.91/1.50  inst_num_of_clauses:                    1977
% 7.91/1.50  inst_num_in_passive:                    1066
% 7.91/1.50  inst_num_in_active:                     535
% 7.91/1.50  inst_num_in_unprocessed:                376
% 7.91/1.50  inst_num_of_loops:                      570
% 7.91/1.50  inst_num_of_learning_restarts:          0
% 7.91/1.50  inst_num_moves_active_passive:          32
% 7.91/1.50  inst_lit_activity:                      0
% 7.91/1.50  inst_lit_activity_moves:                0
% 7.91/1.50  inst_num_tautologies:                   0
% 7.91/1.50  inst_num_prop_implied:                  0
% 7.91/1.50  inst_num_existing_simplified:           0
% 7.91/1.50  inst_num_eq_res_simplified:             0
% 7.91/1.50  inst_num_child_elim:                    0
% 7.91/1.50  inst_num_of_dismatching_blockings:      4101
% 7.91/1.50  inst_num_of_non_proper_insts:           3853
% 7.91/1.50  inst_num_of_duplicates:                 0
% 7.91/1.50  inst_inst_num_from_inst_to_res:         0
% 7.91/1.50  inst_dismatching_checking_time:         0.
% 7.91/1.50  
% 7.91/1.50  ------ Resolution
% 7.91/1.50  
% 7.91/1.50  res_num_of_clauses:                     0
% 7.91/1.50  res_num_in_passive:                     0
% 7.91/1.50  res_num_in_active:                      0
% 7.91/1.50  res_num_of_loops:                       106
% 7.91/1.50  res_forward_subset_subsumed:            613
% 7.91/1.50  res_backward_subset_subsumed:           0
% 7.91/1.50  res_forward_subsumed:                   0
% 7.91/1.50  res_backward_subsumed:                  0
% 7.91/1.50  res_forward_subsumption_resolution:     0
% 7.91/1.50  res_backward_subsumption_resolution:    0
% 7.91/1.50  res_clause_to_clause_subsumption:       15239
% 7.91/1.50  res_orphan_elimination:                 0
% 7.91/1.50  res_tautology_del:                      239
% 7.91/1.50  res_num_eq_res_simplified:              0
% 7.91/1.50  res_num_sel_changes:                    0
% 7.91/1.50  res_moves_from_active_to_pass:          0
% 7.91/1.50  
% 7.91/1.50  ------ Superposition
% 7.91/1.50  
% 7.91/1.50  sup_time_total:                         0.
% 7.91/1.50  sup_time_generating:                    0.
% 7.91/1.50  sup_time_sim_full:                      0.
% 7.91/1.50  sup_time_sim_immed:                     0.
% 7.91/1.50  
% 7.91/1.50  sup_num_of_clauses:                     1063
% 7.91/1.50  sup_num_in_active:                      37
% 7.91/1.50  sup_num_in_passive:                     1026
% 7.91/1.50  sup_num_of_loops:                       113
% 7.91/1.50  sup_fw_superposition:                   4788
% 7.91/1.50  sup_bw_superposition:                   3065
% 7.91/1.50  sup_immediate_simplified:               3394
% 7.91/1.50  sup_given_eliminated:                   6
% 7.91/1.50  comparisons_done:                       0
% 7.91/1.50  comparisons_avoided:                    6
% 7.91/1.50  
% 7.91/1.50  ------ Simplifications
% 7.91/1.50  
% 7.91/1.50  
% 7.91/1.50  sim_fw_subset_subsumed:                 3
% 7.91/1.50  sim_bw_subset_subsumed:                 0
% 7.91/1.50  sim_fw_subsumed:                        264
% 7.91/1.50  sim_bw_subsumed:                        11
% 7.91/1.50  sim_fw_subsumption_res:                 0
% 7.91/1.50  sim_bw_subsumption_res:                 0
% 7.91/1.50  sim_tautology_del:                      0
% 7.91/1.50  sim_eq_tautology_del:                   912
% 7.91/1.50  sim_eq_res_simp:                        0
% 7.91/1.50  sim_fw_demodulated:                     2269
% 7.91/1.50  sim_bw_demodulated:                     97
% 7.91/1.50  sim_light_normalised:                   1273
% 7.91/1.50  sim_joinable_taut:                      424
% 7.91/1.50  sim_joinable_simp:                      0
% 7.91/1.50  sim_ac_normalised:                      0
% 7.91/1.50  sim_smt_subsumption:                    0
% 7.91/1.50  
%------------------------------------------------------------------------------
