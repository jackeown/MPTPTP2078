%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:02 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :  161 (2782 expanded)
%              Number of clauses        :   88 ( 708 expanded)
%              Number of leaves         :   26 ( 813 expanded)
%              Depth                    :   35
%              Number of atoms          :  335 (3191 expanded)
%              Number of equality atoms :  264 (3071 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f21,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f21])).

fof(f26,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f22])).

fof(f34,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f34])).

fof(f64,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f47,f43])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f66])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f68])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f69])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f87,plain,(
    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f64,f65,f71])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

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

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f49,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f49,f69])).

fof(f92,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f84])).

fof(f93,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f92])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f36,f43,f43])).

fof(f3,axiom,(
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
    inference(rectify,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f27])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f76,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f69])).

fof(f94,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f85])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_527,negated_conjecture,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_19,c_8,c_2])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_728,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_527,c_0])).

cnf(c_1585,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_728,c_8])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1009,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_2])).

cnf(c_1595,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1585,c_1009])).

cnf(c_1733,plain,
    ( k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9,c_1595])).

cnf(c_1738,plain,
    ( k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_1733,c_7])).

cnf(c_2504,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(superposition,[status(thm)],[c_1738,c_0])).

cnf(c_2507,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_2504,c_1738])).

cnf(c_742,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_2])).

cnf(c_1741,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1738,c_1595])).

cnf(c_11158,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X1,sK3)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1741,c_742])).

cnf(c_1907,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1741,c_8])).

cnf(c_2195,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9,c_1907])).

cnf(c_2221,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = sK3 ),
    inference(demodulation,[status(thm)],[c_2195,c_7])).

cnf(c_2811,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),X0) = sK3 ),
    inference(superposition,[status(thm)],[c_1741,c_2221])).

cnf(c_3421,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_2811,c_8])).

cnf(c_2191,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_1907])).

cnf(c_3771,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(sK3,X0))) = sK3 ),
    inference(superposition,[status(thm)],[c_2191,c_2811])).

cnf(c_6053,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(sK3,k5_xboole_0(sK3,X1)))) = sK3 ),
    inference(superposition,[status(thm)],[c_3421,c_3771])).

cnf(c_6124,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),X1)) = sK3 ),
    inference(demodulation,[status(thm)],[c_6053,c_1741])).

cnf(c_6241,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X1)),sK3) ),
    inference(superposition,[status(thm)],[c_6124,c_3421])).

cnf(c_6266,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(X1,sK3) ),
    inference(demodulation,[status(thm)],[c_6241,c_1741])).

cnf(c_6911,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(sK3,k5_xboole_0(X1,sK3)) ),
    inference(superposition,[status(thm)],[c_6266,c_1741])).

cnf(c_1901,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,sK3)) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_1741])).

cnf(c_6922,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(demodulation,[status(thm)],[c_6911,c_1901])).

cnf(c_11765,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X1)) = k5_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_11158,c_6922])).

cnf(c_14626,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X0,sK3)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X1)) ),
    inference(superposition,[status(thm)],[c_11765,c_3421])).

cnf(c_14689,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X0,sK3)) = X1 ),
    inference(demodulation,[status(thm)],[c_14626,c_1741,c_11158])).

cnf(c_15362,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(X0,sK3)) = X1 ),
    inference(superposition,[status(thm)],[c_742,c_14689])).

cnf(c_20168,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_2507,c_15362])).

cnf(c_2805,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2,c_2221])).

cnf(c_741,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_2])).

cnf(c_10547,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,sK3) ),
    inference(superposition,[status(thm)],[c_2805,c_741])).

cnf(c_20184,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20168,c_9,c_10547])).

cnf(c_16,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_718,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_28739,plain,
    ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_20184,c_718])).

cnf(c_1282,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1009])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1280,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_1284,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1280,c_7])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1467,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1284,c_1])).

cnf(c_1288,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1284,c_6])).

cnf(c_1479,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1467,c_1282,c_1288])).

cnf(c_1708,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1282,c_1479])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_727,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_22325,plain,
    ( r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r1_xboole_0(k1_xboole_0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1708,c_727])).

cnf(c_22334,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22325,c_1708])).

cnf(c_22342,plain,
    ( r2_hidden(sK2,k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_22334])).

cnf(c_5,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3793,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3794,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3793])).

cnf(c_3796,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)),k5_xboole_0(sK2,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3794])).

cnf(c_534,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_752,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k5_xboole_0(X2,X3))
    | X1 != k5_xboole_0(X2,X3)
    | X0 != k4_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_922,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)),k5_xboole_0(X2,k1_xboole_0))
    | X1 != k5_xboole_0(X2,k1_xboole_0)
    | X0 != k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_752])).

cnf(c_3306,plain,
    ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k1_xboole_0))
    | r1_xboole_0(k1_xboole_0,X1)
    | X1 != k5_xboole_0(X0,k1_xboole_0)
    | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_922])).

cnf(c_3307,plain,
    ( X0 != k5_xboole_0(X1,k1_xboole_0)
    | k1_xboole_0 != k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)),k5_xboole_0(X1,k1_xboole_0)) != iProver_top
    | r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3306])).

cnf(c_3309,plain,
    ( sK2 != k5_xboole_0(sK2,k1_xboole_0)
    | k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0))
    | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)),k5_xboole_0(sK2,k1_xboole_0)) != iProver_top
    | r1_xboole_0(k1_xboole_0,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3307])).

cnf(c_531,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_857,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | k4_xboole_0(X2,k4_xboole_0(X2,X3)) != X1 ),
    inference(instantiation,[status(thm)],[c_531])).

cnf(c_1228,plain,
    ( X0 != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | X0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(c_1683,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | k1_xboole_0 != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1228])).

cnf(c_1684,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | k1_xboole_0 != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1683])).

cnf(c_530,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1019,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_796,plain,
    ( X0 != X1
    | X0 = k5_xboole_0(X2,X3)
    | k5_xboole_0(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_531])).

cnf(c_814,plain,
    ( X0 = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | X0 != k1_xboole_0
    | k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_796])).

cnf(c_919,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_909,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0
    | k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_910,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0
    | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_909])).

cnf(c_819,plain,
    ( X0 != X1
    | X0 = k5_xboole_0(X1,k1_xboole_0)
    | k5_xboole_0(X1,k1_xboole_0) != X1 ),
    inference(instantiation,[status(thm)],[c_796])).

cnf(c_820,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) != sK2
    | sK2 = k5_xboole_0(sK2,k1_xboole_0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_40,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_39,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_25,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_22,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28739,c_22342,c_3796,c_3309,c_1684,c_1019,c_919,c_910,c_820,c_527,c_40,c_39,c_25,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n006.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 12:05:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 7.78/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.78/1.48  
% 7.78/1.48  ------  iProver source info
% 7.78/1.48  
% 7.78/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.78/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.78/1.48  git: non_committed_changes: false
% 7.78/1.48  git: last_make_outside_of_git: false
% 7.78/1.48  
% 7.78/1.48  ------ 
% 7.78/1.48  
% 7.78/1.48  ------ Input Options
% 7.78/1.48  
% 7.78/1.48  --out_options                           all
% 7.78/1.48  --tptp_safe_out                         true
% 7.78/1.48  --problem_path                          ""
% 7.78/1.48  --include_path                          ""
% 7.78/1.48  --clausifier                            res/vclausify_rel
% 7.78/1.48  --clausifier_options                    ""
% 7.78/1.48  --stdin                                 false
% 7.78/1.48  --stats_out                             all
% 7.78/1.48  
% 7.78/1.48  ------ General Options
% 7.78/1.48  
% 7.78/1.48  --fof                                   false
% 7.78/1.48  --time_out_real                         305.
% 7.78/1.48  --time_out_virtual                      -1.
% 7.78/1.48  --symbol_type_check                     false
% 7.78/1.48  --clausify_out                          false
% 7.78/1.48  --sig_cnt_out                           false
% 7.78/1.48  --trig_cnt_out                          false
% 7.78/1.48  --trig_cnt_out_tolerance                1.
% 7.78/1.48  --trig_cnt_out_sk_spl                   false
% 7.78/1.48  --abstr_cl_out                          false
% 7.78/1.48  
% 7.78/1.48  ------ Global Options
% 7.78/1.48  
% 7.78/1.48  --schedule                              default
% 7.78/1.48  --add_important_lit                     false
% 7.78/1.48  --prop_solver_per_cl                    1000
% 7.78/1.48  --min_unsat_core                        false
% 7.78/1.48  --soft_assumptions                      false
% 7.78/1.48  --soft_lemma_size                       3
% 7.78/1.48  --prop_impl_unit_size                   0
% 7.78/1.48  --prop_impl_unit                        []
% 7.78/1.48  --share_sel_clauses                     true
% 7.78/1.48  --reset_solvers                         false
% 7.78/1.48  --bc_imp_inh                            [conj_cone]
% 7.78/1.48  --conj_cone_tolerance                   3.
% 7.78/1.48  --extra_neg_conj                        none
% 7.78/1.48  --large_theory_mode                     true
% 7.78/1.48  --prolific_symb_bound                   200
% 7.78/1.48  --lt_threshold                          2000
% 7.78/1.48  --clause_weak_htbl                      true
% 7.78/1.48  --gc_record_bc_elim                     false
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing Options
% 7.78/1.48  
% 7.78/1.48  --preprocessing_flag                    true
% 7.78/1.48  --time_out_prep_mult                    0.1
% 7.78/1.48  --splitting_mode                        input
% 7.78/1.48  --splitting_grd                         true
% 7.78/1.48  --splitting_cvd                         false
% 7.78/1.48  --splitting_cvd_svl                     false
% 7.78/1.48  --splitting_nvd                         32
% 7.78/1.48  --sub_typing                            true
% 7.78/1.48  --prep_gs_sim                           true
% 7.78/1.48  --prep_unflatten                        true
% 7.78/1.48  --prep_res_sim                          true
% 7.78/1.48  --prep_upred                            true
% 7.78/1.48  --prep_sem_filter                       exhaustive
% 7.78/1.48  --prep_sem_filter_out                   false
% 7.78/1.48  --pred_elim                             true
% 7.78/1.48  --res_sim_input                         true
% 7.78/1.48  --eq_ax_congr_red                       true
% 7.78/1.48  --pure_diseq_elim                       true
% 7.78/1.48  --brand_transform                       false
% 7.78/1.48  --non_eq_to_eq                          false
% 7.78/1.48  --prep_def_merge                        true
% 7.78/1.48  --prep_def_merge_prop_impl              false
% 7.78/1.48  --prep_def_merge_mbd                    true
% 7.78/1.48  --prep_def_merge_tr_red                 false
% 7.78/1.48  --prep_def_merge_tr_cl                  false
% 7.78/1.48  --smt_preprocessing                     true
% 7.78/1.48  --smt_ac_axioms                         fast
% 7.78/1.48  --preprocessed_out                      false
% 7.78/1.48  --preprocessed_stats                    false
% 7.78/1.48  
% 7.78/1.48  ------ Abstraction refinement Options
% 7.78/1.48  
% 7.78/1.48  --abstr_ref                             []
% 7.78/1.48  --abstr_ref_prep                        false
% 7.78/1.48  --abstr_ref_until_sat                   false
% 7.78/1.48  --abstr_ref_sig_restrict                funpre
% 7.78/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.78/1.48  --abstr_ref_under                       []
% 7.78/1.48  
% 7.78/1.48  ------ SAT Options
% 7.78/1.48  
% 7.78/1.48  --sat_mode                              false
% 7.78/1.48  --sat_fm_restart_options                ""
% 7.78/1.48  --sat_gr_def                            false
% 7.78/1.48  --sat_epr_types                         true
% 7.78/1.48  --sat_non_cyclic_types                  false
% 7.78/1.48  --sat_finite_models                     false
% 7.78/1.48  --sat_fm_lemmas                         false
% 7.78/1.48  --sat_fm_prep                           false
% 7.78/1.48  --sat_fm_uc_incr                        true
% 7.78/1.48  --sat_out_model                         small
% 7.78/1.48  --sat_out_clauses                       false
% 7.78/1.48  
% 7.78/1.48  ------ QBF Options
% 7.78/1.48  
% 7.78/1.48  --qbf_mode                              false
% 7.78/1.48  --qbf_elim_univ                         false
% 7.78/1.48  --qbf_dom_inst                          none
% 7.78/1.48  --qbf_dom_pre_inst                      false
% 7.78/1.48  --qbf_sk_in                             false
% 7.78/1.48  --qbf_pred_elim                         true
% 7.78/1.48  --qbf_split                             512
% 7.78/1.48  
% 7.78/1.48  ------ BMC1 Options
% 7.78/1.48  
% 7.78/1.48  --bmc1_incremental                      false
% 7.78/1.48  --bmc1_axioms                           reachable_all
% 7.78/1.48  --bmc1_min_bound                        0
% 7.78/1.48  --bmc1_max_bound                        -1
% 7.78/1.48  --bmc1_max_bound_default                -1
% 7.78/1.48  --bmc1_symbol_reachability              true
% 7.78/1.48  --bmc1_property_lemmas                  false
% 7.78/1.48  --bmc1_k_induction                      false
% 7.78/1.48  --bmc1_non_equiv_states                 false
% 7.78/1.48  --bmc1_deadlock                         false
% 7.78/1.48  --bmc1_ucm                              false
% 7.78/1.48  --bmc1_add_unsat_core                   none
% 7.78/1.48  --bmc1_unsat_core_children              false
% 7.78/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.78/1.48  --bmc1_out_stat                         full
% 7.78/1.48  --bmc1_ground_init                      false
% 7.78/1.48  --bmc1_pre_inst_next_state              false
% 7.78/1.48  --bmc1_pre_inst_state                   false
% 7.78/1.48  --bmc1_pre_inst_reach_state             false
% 7.78/1.48  --bmc1_out_unsat_core                   false
% 7.78/1.48  --bmc1_aig_witness_out                  false
% 7.78/1.48  --bmc1_verbose                          false
% 7.78/1.48  --bmc1_dump_clauses_tptp                false
% 7.78/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.78/1.48  --bmc1_dump_file                        -
% 7.78/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.78/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.78/1.48  --bmc1_ucm_extend_mode                  1
% 7.78/1.48  --bmc1_ucm_init_mode                    2
% 7.78/1.48  --bmc1_ucm_cone_mode                    none
% 7.78/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.78/1.48  --bmc1_ucm_relax_model                  4
% 7.78/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.78/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.78/1.48  --bmc1_ucm_layered_model                none
% 7.78/1.48  --bmc1_ucm_max_lemma_size               10
% 7.78/1.48  
% 7.78/1.48  ------ AIG Options
% 7.78/1.48  
% 7.78/1.48  --aig_mode                              false
% 7.78/1.48  
% 7.78/1.48  ------ Instantiation Options
% 7.78/1.48  
% 7.78/1.48  --instantiation_flag                    true
% 7.78/1.48  --inst_sos_flag                         true
% 7.78/1.48  --inst_sos_phase                        true
% 7.78/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.78/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.78/1.48  --inst_lit_sel_side                     num_symb
% 7.78/1.48  --inst_solver_per_active                1400
% 7.78/1.48  --inst_solver_calls_frac                1.
% 7.78/1.48  --inst_passive_queue_type               priority_queues
% 7.78/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.78/1.48  --inst_passive_queues_freq              [25;2]
% 7.78/1.48  --inst_dismatching                      true
% 7.78/1.48  --inst_eager_unprocessed_to_passive     true
% 7.78/1.48  --inst_prop_sim_given                   true
% 7.78/1.48  --inst_prop_sim_new                     false
% 7.78/1.48  --inst_subs_new                         false
% 7.78/1.48  --inst_eq_res_simp                      false
% 7.78/1.48  --inst_subs_given                       false
% 7.78/1.48  --inst_orphan_elimination               true
% 7.78/1.48  --inst_learning_loop_flag               true
% 7.78/1.48  --inst_learning_start                   3000
% 7.78/1.48  --inst_learning_factor                  2
% 7.78/1.48  --inst_start_prop_sim_after_learn       3
% 7.78/1.48  --inst_sel_renew                        solver
% 7.78/1.48  --inst_lit_activity_flag                true
% 7.78/1.48  --inst_restr_to_given                   false
% 7.78/1.48  --inst_activity_threshold               500
% 7.78/1.48  --inst_out_proof                        true
% 7.78/1.48  
% 7.78/1.48  ------ Resolution Options
% 7.78/1.48  
% 7.78/1.48  --resolution_flag                       true
% 7.78/1.48  --res_lit_sel                           adaptive
% 7.78/1.48  --res_lit_sel_side                      none
% 7.78/1.48  --res_ordering                          kbo
% 7.78/1.48  --res_to_prop_solver                    active
% 7.78/1.48  --res_prop_simpl_new                    false
% 7.78/1.48  --res_prop_simpl_given                  true
% 7.78/1.48  --res_passive_queue_type                priority_queues
% 7.78/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.78/1.48  --res_passive_queues_freq               [15;5]
% 7.78/1.48  --res_forward_subs                      full
% 7.78/1.48  --res_backward_subs                     full
% 7.78/1.48  --res_forward_subs_resolution           true
% 7.78/1.48  --res_backward_subs_resolution          true
% 7.78/1.48  --res_orphan_elimination                true
% 7.78/1.48  --res_time_limit                        2.
% 7.78/1.48  --res_out_proof                         true
% 7.78/1.48  
% 7.78/1.48  ------ Superposition Options
% 7.78/1.48  
% 7.78/1.48  --superposition_flag                    true
% 7.78/1.48  --sup_passive_queue_type                priority_queues
% 7.78/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.78/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.78/1.48  --demod_completeness_check              fast
% 7.78/1.48  --demod_use_ground                      true
% 7.78/1.48  --sup_to_prop_solver                    passive
% 7.78/1.48  --sup_prop_simpl_new                    true
% 7.78/1.48  --sup_prop_simpl_given                  true
% 7.78/1.48  --sup_fun_splitting                     true
% 7.78/1.48  --sup_smt_interval                      50000
% 7.78/1.48  
% 7.78/1.48  ------ Superposition Simplification Setup
% 7.78/1.48  
% 7.78/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.78/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.78/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.78/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.78/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.78/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.78/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.78/1.48  --sup_immed_triv                        [TrivRules]
% 7.78/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.48  --sup_immed_bw_main                     []
% 7.78/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.78/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.78/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.48  --sup_input_bw                          []
% 7.78/1.48  
% 7.78/1.48  ------ Combination Options
% 7.78/1.48  
% 7.78/1.48  --comb_res_mult                         3
% 7.78/1.48  --comb_sup_mult                         2
% 7.78/1.48  --comb_inst_mult                        10
% 7.78/1.48  
% 7.78/1.48  ------ Debug Options
% 7.78/1.48  
% 7.78/1.48  --dbg_backtrace                         false
% 7.78/1.48  --dbg_dump_prop_clauses                 false
% 7.78/1.48  --dbg_dump_prop_clauses_file            -
% 7.78/1.48  --dbg_out_stat                          false
% 7.78/1.48  ------ Parsing...
% 7.78/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.48  ------ Proving...
% 7.78/1.48  ------ Problem Properties 
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  clauses                                 20
% 7.78/1.48  conjectures                             1
% 7.78/1.48  EPR                                     0
% 7.78/1.48  Horn                                    17
% 7.78/1.48  unary                                   13
% 7.78/1.48  binary                                  2
% 7.78/1.48  lits                                    35
% 7.78/1.48  lits eq                                 22
% 7.78/1.48  fd_pure                                 0
% 7.78/1.48  fd_pseudo                               0
% 7.78/1.48  fd_cond                                 0
% 7.78/1.48  fd_pseudo_cond                          4
% 7.78/1.48  AC symbols                              1
% 7.78/1.48  
% 7.78/1.48  ------ Schedule dynamic 5 is on 
% 7.78/1.48  
% 7.78/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  ------ 
% 7.78/1.48  Current options:
% 7.78/1.48  ------ 
% 7.78/1.48  
% 7.78/1.48  ------ Input Options
% 7.78/1.48  
% 7.78/1.48  --out_options                           all
% 7.78/1.48  --tptp_safe_out                         true
% 7.78/1.48  --problem_path                          ""
% 7.78/1.48  --include_path                          ""
% 7.78/1.48  --clausifier                            res/vclausify_rel
% 7.78/1.48  --clausifier_options                    ""
% 7.78/1.48  --stdin                                 false
% 7.78/1.48  --stats_out                             all
% 7.78/1.48  
% 7.78/1.48  ------ General Options
% 7.78/1.48  
% 7.78/1.48  --fof                                   false
% 7.78/1.48  --time_out_real                         305.
% 7.78/1.48  --time_out_virtual                      -1.
% 7.78/1.48  --symbol_type_check                     false
% 7.78/1.48  --clausify_out                          false
% 7.78/1.48  --sig_cnt_out                           false
% 7.78/1.48  --trig_cnt_out                          false
% 7.78/1.48  --trig_cnt_out_tolerance                1.
% 7.78/1.48  --trig_cnt_out_sk_spl                   false
% 7.78/1.48  --abstr_cl_out                          false
% 7.78/1.48  
% 7.78/1.48  ------ Global Options
% 7.78/1.48  
% 7.78/1.48  --schedule                              default
% 7.78/1.48  --add_important_lit                     false
% 7.78/1.48  --prop_solver_per_cl                    1000
% 7.78/1.48  --min_unsat_core                        false
% 7.78/1.48  --soft_assumptions                      false
% 7.78/1.48  --soft_lemma_size                       3
% 7.78/1.48  --prop_impl_unit_size                   0
% 7.78/1.48  --prop_impl_unit                        []
% 7.78/1.48  --share_sel_clauses                     true
% 7.78/1.48  --reset_solvers                         false
% 7.78/1.48  --bc_imp_inh                            [conj_cone]
% 7.78/1.48  --conj_cone_tolerance                   3.
% 7.78/1.48  --extra_neg_conj                        none
% 7.78/1.48  --large_theory_mode                     true
% 7.78/1.48  --prolific_symb_bound                   200
% 7.78/1.48  --lt_threshold                          2000
% 7.78/1.48  --clause_weak_htbl                      true
% 7.78/1.48  --gc_record_bc_elim                     false
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing Options
% 7.78/1.48  
% 7.78/1.48  --preprocessing_flag                    true
% 7.78/1.48  --time_out_prep_mult                    0.1
% 7.78/1.48  --splitting_mode                        input
% 7.78/1.48  --splitting_grd                         true
% 7.78/1.48  --splitting_cvd                         false
% 7.78/1.48  --splitting_cvd_svl                     false
% 7.78/1.48  --splitting_nvd                         32
% 7.78/1.48  --sub_typing                            true
% 7.78/1.48  --prep_gs_sim                           true
% 7.78/1.48  --prep_unflatten                        true
% 7.78/1.48  --prep_res_sim                          true
% 7.78/1.48  --prep_upred                            true
% 7.78/1.48  --prep_sem_filter                       exhaustive
% 7.78/1.48  --prep_sem_filter_out                   false
% 7.78/1.48  --pred_elim                             true
% 7.78/1.48  --res_sim_input                         true
% 7.78/1.48  --eq_ax_congr_red                       true
% 7.78/1.48  --pure_diseq_elim                       true
% 7.78/1.48  --brand_transform                       false
% 7.78/1.48  --non_eq_to_eq                          false
% 7.78/1.48  --prep_def_merge                        true
% 7.78/1.48  --prep_def_merge_prop_impl              false
% 7.78/1.48  --prep_def_merge_mbd                    true
% 7.78/1.48  --prep_def_merge_tr_red                 false
% 7.78/1.48  --prep_def_merge_tr_cl                  false
% 7.78/1.48  --smt_preprocessing                     true
% 7.78/1.48  --smt_ac_axioms                         fast
% 7.78/1.48  --preprocessed_out                      false
% 7.78/1.48  --preprocessed_stats                    false
% 7.78/1.48  
% 7.78/1.48  ------ Abstraction refinement Options
% 7.78/1.48  
% 7.78/1.48  --abstr_ref                             []
% 7.78/1.48  --abstr_ref_prep                        false
% 7.78/1.48  --abstr_ref_until_sat                   false
% 7.78/1.48  --abstr_ref_sig_restrict                funpre
% 7.78/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.78/1.48  --abstr_ref_under                       []
% 7.78/1.48  
% 7.78/1.48  ------ SAT Options
% 7.78/1.48  
% 7.78/1.48  --sat_mode                              false
% 7.78/1.48  --sat_fm_restart_options                ""
% 7.78/1.48  --sat_gr_def                            false
% 7.78/1.48  --sat_epr_types                         true
% 7.78/1.48  --sat_non_cyclic_types                  false
% 7.78/1.48  --sat_finite_models                     false
% 7.78/1.48  --sat_fm_lemmas                         false
% 7.78/1.48  --sat_fm_prep                           false
% 7.78/1.48  --sat_fm_uc_incr                        true
% 7.78/1.48  --sat_out_model                         small
% 7.78/1.48  --sat_out_clauses                       false
% 7.78/1.48  
% 7.78/1.48  ------ QBF Options
% 7.78/1.48  
% 7.78/1.48  --qbf_mode                              false
% 7.78/1.48  --qbf_elim_univ                         false
% 7.78/1.48  --qbf_dom_inst                          none
% 7.78/1.48  --qbf_dom_pre_inst                      false
% 7.78/1.48  --qbf_sk_in                             false
% 7.78/1.48  --qbf_pred_elim                         true
% 7.78/1.48  --qbf_split                             512
% 7.78/1.48  
% 7.78/1.48  ------ BMC1 Options
% 7.78/1.48  
% 7.78/1.48  --bmc1_incremental                      false
% 7.78/1.48  --bmc1_axioms                           reachable_all
% 7.78/1.48  --bmc1_min_bound                        0
% 7.78/1.48  --bmc1_max_bound                        -1
% 7.78/1.48  --bmc1_max_bound_default                -1
% 7.78/1.48  --bmc1_symbol_reachability              true
% 7.78/1.48  --bmc1_property_lemmas                  false
% 7.78/1.48  --bmc1_k_induction                      false
% 7.78/1.48  --bmc1_non_equiv_states                 false
% 7.78/1.48  --bmc1_deadlock                         false
% 7.78/1.48  --bmc1_ucm                              false
% 7.78/1.48  --bmc1_add_unsat_core                   none
% 7.78/1.48  --bmc1_unsat_core_children              false
% 7.78/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.78/1.48  --bmc1_out_stat                         full
% 7.78/1.48  --bmc1_ground_init                      false
% 7.78/1.48  --bmc1_pre_inst_next_state              false
% 7.78/1.48  --bmc1_pre_inst_state                   false
% 7.78/1.48  --bmc1_pre_inst_reach_state             false
% 7.78/1.48  --bmc1_out_unsat_core                   false
% 7.78/1.48  --bmc1_aig_witness_out                  false
% 7.78/1.48  --bmc1_verbose                          false
% 7.78/1.48  --bmc1_dump_clauses_tptp                false
% 7.78/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.78/1.48  --bmc1_dump_file                        -
% 7.78/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.78/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.78/1.48  --bmc1_ucm_extend_mode                  1
% 7.78/1.48  --bmc1_ucm_init_mode                    2
% 7.78/1.48  --bmc1_ucm_cone_mode                    none
% 7.78/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.78/1.48  --bmc1_ucm_relax_model                  4
% 7.78/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.78/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.78/1.48  --bmc1_ucm_layered_model                none
% 7.78/1.48  --bmc1_ucm_max_lemma_size               10
% 7.78/1.48  
% 7.78/1.48  ------ AIG Options
% 7.78/1.48  
% 7.78/1.48  --aig_mode                              false
% 7.78/1.48  
% 7.78/1.48  ------ Instantiation Options
% 7.78/1.48  
% 7.78/1.48  --instantiation_flag                    true
% 7.78/1.48  --inst_sos_flag                         true
% 7.78/1.48  --inst_sos_phase                        true
% 7.78/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.78/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.78/1.48  --inst_lit_sel_side                     none
% 7.78/1.48  --inst_solver_per_active                1400
% 7.78/1.48  --inst_solver_calls_frac                1.
% 7.78/1.48  --inst_passive_queue_type               priority_queues
% 7.78/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.78/1.48  --inst_passive_queues_freq              [25;2]
% 7.78/1.48  --inst_dismatching                      true
% 7.78/1.48  --inst_eager_unprocessed_to_passive     true
% 7.78/1.48  --inst_prop_sim_given                   true
% 7.78/1.48  --inst_prop_sim_new                     false
% 7.78/1.48  --inst_subs_new                         false
% 7.78/1.48  --inst_eq_res_simp                      false
% 7.78/1.48  --inst_subs_given                       false
% 7.78/1.48  --inst_orphan_elimination               true
% 7.78/1.48  --inst_learning_loop_flag               true
% 7.78/1.48  --inst_learning_start                   3000
% 7.78/1.48  --inst_learning_factor                  2
% 7.78/1.48  --inst_start_prop_sim_after_learn       3
% 7.78/1.48  --inst_sel_renew                        solver
% 7.78/1.48  --inst_lit_activity_flag                true
% 7.78/1.48  --inst_restr_to_given                   false
% 7.78/1.48  --inst_activity_threshold               500
% 7.78/1.48  --inst_out_proof                        true
% 7.78/1.48  
% 7.78/1.48  ------ Resolution Options
% 7.78/1.48  
% 7.78/1.48  --resolution_flag                       false
% 7.78/1.48  --res_lit_sel                           adaptive
% 7.78/1.48  --res_lit_sel_side                      none
% 7.78/1.48  --res_ordering                          kbo
% 7.78/1.48  --res_to_prop_solver                    active
% 7.78/1.48  --res_prop_simpl_new                    false
% 7.78/1.48  --res_prop_simpl_given                  true
% 7.78/1.48  --res_passive_queue_type                priority_queues
% 7.78/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.78/1.48  --res_passive_queues_freq               [15;5]
% 7.78/1.48  --res_forward_subs                      full
% 7.78/1.48  --res_backward_subs                     full
% 7.78/1.48  --res_forward_subs_resolution           true
% 7.78/1.48  --res_backward_subs_resolution          true
% 7.78/1.48  --res_orphan_elimination                true
% 7.78/1.48  --res_time_limit                        2.
% 7.78/1.48  --res_out_proof                         true
% 7.78/1.48  
% 7.78/1.48  ------ Superposition Options
% 7.78/1.48  
% 7.78/1.48  --superposition_flag                    true
% 7.78/1.48  --sup_passive_queue_type                priority_queues
% 7.78/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.78/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.78/1.48  --demod_completeness_check              fast
% 7.78/1.48  --demod_use_ground                      true
% 7.78/1.48  --sup_to_prop_solver                    passive
% 7.78/1.48  --sup_prop_simpl_new                    true
% 7.78/1.48  --sup_prop_simpl_given                  true
% 7.78/1.48  --sup_fun_splitting                     true
% 7.78/1.48  --sup_smt_interval                      50000
% 7.78/1.48  
% 7.78/1.48  ------ Superposition Simplification Setup
% 7.78/1.48  
% 7.78/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.78/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.78/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.78/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.78/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.78/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.78/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.78/1.48  --sup_immed_triv                        [TrivRules]
% 7.78/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.48  --sup_immed_bw_main                     []
% 7.78/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.78/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.78/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.48  --sup_input_bw                          []
% 7.78/1.48  
% 7.78/1.48  ------ Combination Options
% 7.78/1.48  
% 7.78/1.48  --comb_res_mult                         3
% 7.78/1.48  --comb_sup_mult                         2
% 7.78/1.48  --comb_inst_mult                        10
% 7.78/1.48  
% 7.78/1.48  ------ Debug Options
% 7.78/1.48  
% 7.78/1.48  --dbg_backtrace                         false
% 7.78/1.48  --dbg_dump_prop_clauses                 false
% 7.78/1.48  --dbg_dump_prop_clauses_file            -
% 7.78/1.48  --dbg_out_stat                          false
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  ------ Proving...
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  % SZS status Theorem for theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  fof(f10,axiom,(
% 7.78/1.48    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f46,plain,(
% 7.78/1.48    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.78/1.48    inference(cnf_transformation,[],[f10])).
% 7.78/1.48  
% 7.78/1.48  fof(f21,conjecture,(
% 7.78/1.48    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f22,negated_conjecture,(
% 7.78/1.48    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 7.78/1.48    inference(negated_conjecture,[],[f21])).
% 7.78/1.48  
% 7.78/1.48  fof(f26,plain,(
% 7.78/1.48    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 7.78/1.48    inference(ennf_transformation,[],[f22])).
% 7.78/1.48  
% 7.78/1.48  fof(f34,plain,(
% 7.78/1.48    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 7.78/1.48    introduced(choice_axiom,[])).
% 7.78/1.48  
% 7.78/1.48  fof(f35,plain,(
% 7.78/1.48    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 7.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f34])).
% 7.78/1.48  
% 7.78/1.48  fof(f64,plain,(
% 7.78/1.48    k1_xboole_0 = k2_xboole_0(k1_tarski(sK2),sK3)),
% 7.78/1.48    inference(cnf_transformation,[],[f35])).
% 7.78/1.48  
% 7.78/1.48  fof(f11,axiom,(
% 7.78/1.48    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f47,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f11])).
% 7.78/1.48  
% 7.78/1.48  fof(f7,axiom,(
% 7.78/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f43,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.78/1.48    inference(cnf_transformation,[],[f7])).
% 7.78/1.48  
% 7.78/1.48  fof(f65,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1)) )),
% 7.78/1.48    inference(definition_unfolding,[],[f47,f43])).
% 7.78/1.48  
% 7.78/1.48  fof(f13,axiom,(
% 7.78/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f56,plain,(
% 7.78/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f13])).
% 7.78/1.48  
% 7.78/1.48  fof(f14,axiom,(
% 7.78/1.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f57,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f14])).
% 7.78/1.48  
% 7.78/1.48  fof(f15,axiom,(
% 7.78/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f58,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f15])).
% 7.78/1.48  
% 7.78/1.48  fof(f16,axiom,(
% 7.78/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f59,plain,(
% 7.78/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f16])).
% 7.78/1.48  
% 7.78/1.48  fof(f17,axiom,(
% 7.78/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f60,plain,(
% 7.78/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f17])).
% 7.78/1.48  
% 7.78/1.48  fof(f18,axiom,(
% 7.78/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f61,plain,(
% 7.78/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f18])).
% 7.78/1.48  
% 7.78/1.48  fof(f19,axiom,(
% 7.78/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f62,plain,(
% 7.78/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f19])).
% 7.78/1.48  
% 7.78/1.48  fof(f66,plain,(
% 7.78/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.78/1.48    inference(definition_unfolding,[],[f61,f62])).
% 7.78/1.48  
% 7.78/1.48  fof(f67,plain,(
% 7.78/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.78/1.48    inference(definition_unfolding,[],[f60,f66])).
% 7.78/1.48  
% 7.78/1.48  fof(f68,plain,(
% 7.78/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.78/1.48    inference(definition_unfolding,[],[f59,f67])).
% 7.78/1.48  
% 7.78/1.48  fof(f69,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.78/1.48    inference(definition_unfolding,[],[f58,f68])).
% 7.78/1.48  
% 7.78/1.48  fof(f70,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.78/1.48    inference(definition_unfolding,[],[f57,f69])).
% 7.78/1.48  
% 7.78/1.48  fof(f71,plain,(
% 7.78/1.48    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.78/1.48    inference(definition_unfolding,[],[f56,f70])).
% 7.78/1.48  
% 7.78/1.48  fof(f87,plain,(
% 7.78/1.48    k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0),
% 7.78/1.48    inference(definition_unfolding,[],[f64,f65,f71])).
% 7.78/1.48  
% 7.78/1.48  fof(f9,axiom,(
% 7.78/1.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f45,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f9])).
% 7.78/1.48  
% 7.78/1.48  fof(f2,axiom,(
% 7.78/1.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f37,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f2])).
% 7.78/1.48  
% 7.78/1.48  fof(f5,axiom,(
% 7.78/1.48    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f41,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f5])).
% 7.78/1.48  
% 7.78/1.48  fof(f72,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1)) )),
% 7.78/1.48    inference(definition_unfolding,[],[f41,f43])).
% 7.78/1.48  
% 7.78/1.48  fof(f8,axiom,(
% 7.78/1.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f44,plain,(
% 7.78/1.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.78/1.48    inference(cnf_transformation,[],[f8])).
% 7.78/1.48  
% 7.78/1.48  fof(f12,axiom,(
% 7.78/1.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f25,plain,(
% 7.78/1.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.78/1.48    inference(ennf_transformation,[],[f12])).
% 7.78/1.48  
% 7.78/1.48  fof(f29,plain,(
% 7.78/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.78/1.48    inference(nnf_transformation,[],[f25])).
% 7.78/1.48  
% 7.78/1.48  fof(f30,plain,(
% 7.78/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.78/1.48    inference(flattening,[],[f29])).
% 7.78/1.48  
% 7.78/1.48  fof(f31,plain,(
% 7.78/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.78/1.48    inference(rectify,[],[f30])).
% 7.78/1.48  
% 7.78/1.48  fof(f32,plain,(
% 7.78/1.48    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 7.78/1.48    introduced(choice_axiom,[])).
% 7.78/1.48  
% 7.78/1.48  fof(f33,plain,(
% 7.78/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 7.78/1.48  
% 7.78/1.48  fof(f49,plain,(
% 7.78/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.78/1.48    inference(cnf_transformation,[],[f33])).
% 7.78/1.48  
% 7.78/1.48  fof(f84,plain,(
% 7.78/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.78/1.48    inference(definition_unfolding,[],[f49,f69])).
% 7.78/1.48  
% 7.78/1.48  fof(f92,plain,(
% 7.78/1.48    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 7.78/1.48    inference(equality_resolution,[],[f84])).
% 7.78/1.48  
% 7.78/1.48  fof(f93,plain,(
% 7.78/1.48    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 7.78/1.48    inference(equality_resolution,[],[f92])).
% 7.78/1.48  
% 7.78/1.48  fof(f6,axiom,(
% 7.78/1.48    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f42,plain,(
% 7.78/1.48    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.78/1.48    inference(cnf_transformation,[],[f6])).
% 7.78/1.48  
% 7.78/1.48  fof(f77,plain,(
% 7.78/1.48    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 7.78/1.48    inference(definition_unfolding,[],[f42,f43])).
% 7.78/1.48  
% 7.78/1.48  fof(f1,axiom,(
% 7.78/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f36,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f1])).
% 7.78/1.48  
% 7.78/1.48  fof(f73,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.78/1.48    inference(definition_unfolding,[],[f36,f43,f43])).
% 7.78/1.48  
% 7.78/1.48  fof(f3,axiom,(
% 7.78/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f23,plain,(
% 7.78/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.78/1.48    inference(rectify,[],[f3])).
% 7.78/1.48  
% 7.78/1.48  fof(f24,plain,(
% 7.78/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.78/1.48    inference(ennf_transformation,[],[f23])).
% 7.78/1.48  
% 7.78/1.48  fof(f27,plain,(
% 7.78/1.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.78/1.48    introduced(choice_axiom,[])).
% 7.78/1.48  
% 7.78/1.48  fof(f28,plain,(
% 7.78/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f27])).
% 7.78/1.48  
% 7.78/1.48  fof(f39,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.78/1.48    inference(cnf_transformation,[],[f28])).
% 7.78/1.48  
% 7.78/1.48  fof(f74,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.78/1.48    inference(definition_unfolding,[],[f39,f43])).
% 7.78/1.48  
% 7.78/1.48  fof(f4,axiom,(
% 7.78/1.48    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f40,plain,(
% 7.78/1.48    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 7.78/1.48    inference(cnf_transformation,[],[f4])).
% 7.78/1.48  
% 7.78/1.48  fof(f76,plain,(
% 7.78/1.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1))) )),
% 7.78/1.48    inference(definition_unfolding,[],[f40,f43])).
% 7.78/1.48  
% 7.78/1.48  fof(f48,plain,(
% 7.78/1.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 7.78/1.48    inference(cnf_transformation,[],[f33])).
% 7.78/1.48  
% 7.78/1.48  fof(f85,plain,(
% 7.78/1.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.78/1.48    inference(definition_unfolding,[],[f48,f69])).
% 7.78/1.48  
% 7.78/1.48  fof(f94,plain,(
% 7.78/1.48    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 7.78/1.48    inference(equality_resolution,[],[f85])).
% 7.78/1.48  
% 7.78/1.48  cnf(c_9,plain,
% 7.78/1.48      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.78/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_19,negated_conjecture,
% 7.78/1.48      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = k1_xboole_0 ),
% 7.78/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_8,plain,
% 7.78/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.78/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2,plain,
% 7.78/1.48      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.78/1.48      inference(cnf_transformation,[],[f37]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_527,negated_conjecture,
% 7.78/1.48      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) = k1_xboole_0 ),
% 7.78/1.48      inference(theory_normalisation,[status(thm)],[c_19,c_8,c_2]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_0,plain,
% 7.78/1.48      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.78/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_728,plain,
% 7.78/1.48      ( k5_xboole_0(sK3,k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
% 7.78/1.48      inference(demodulation,[status(thm)],[c_527,c_0]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1585,plain,
% 7.78/1.48      ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_728,c_8]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_7,plain,
% 7.78/1.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.78/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1009,plain,
% 7.78/1.48      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_7,c_2]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1595,plain,
% 7.78/1.48      ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),X0)) = X0 ),
% 7.78/1.48      inference(light_normalisation,[status(thm)],[c_1585,c_1009]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1733,plain,
% 7.78/1.48      ( k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k5_xboole_0(sK3,k1_xboole_0) ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_9,c_1595]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1738,plain,
% 7.78/1.48      ( k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK3 ),
% 7.78/1.48      inference(demodulation,[status(thm)],[c_1733,c_7]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2504,plain,
% 7.78/1.48      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_1738,c_0]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2507,plain,
% 7.78/1.48      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK3 ),
% 7.78/1.48      inference(demodulation,[status(thm)],[c_2504,c_1738]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_742,plain,
% 7.78/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_8,c_2]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1741,plain,
% 7.78/1.48      ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
% 7.78/1.48      inference(demodulation,[status(thm)],[c_1738,c_1595]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_11158,plain,
% 7.78/1.49      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X1,sK3)) = k5_xboole_0(X1,X0) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1741,c_742]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1907,plain,
% 7.78/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,X0),X1)) = k5_xboole_0(X0,X1) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1741,c_8]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2195,plain,
% 7.78/1.49      ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = k5_xboole_0(sK3,k1_xboole_0) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_9,c_1907]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2221,plain,
% 7.78/1.49      ( k5_xboole_0(X0,k5_xboole_0(sK3,X0)) = sK3 ),
% 7.78/1.49      inference(demodulation,[status(thm)],[c_2195,c_7]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2811,plain,
% 7.78/1.49      ( k5_xboole_0(k5_xboole_0(sK3,X0),X0) = sK3 ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1741,c_2221]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3421,plain,
% 7.78/1.49      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(X0,X1)) = k5_xboole_0(sK3,X1) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_2811,c_8]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2191,plain,
% 7.78/1.49      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,X1))) = k5_xboole_0(X1,X0) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_2,c_1907]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3771,plain,
% 7.78/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(sK3,X0))) = sK3 ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_2191,c_2811]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6053,plain,
% 7.78/1.49      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(sK3,k5_xboole_0(sK3,X1)))) = sK3 ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_3421,c_3771]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6124,plain,
% 7.78/1.49      ( k5_xboole_0(k5_xboole_0(sK3,X0),k5_xboole_0(k5_xboole_0(X1,X0),X1)) = sK3 ),
% 7.78/1.49      inference(demodulation,[status(thm)],[c_6053,c_1741]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6241,plain,
% 7.78/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK3,X1)),sK3) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_6124,c_3421]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6266,plain,
% 7.78/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(X1,sK3) ),
% 7.78/1.49      inference(demodulation,[status(thm)],[c_6241,c_1741]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6911,plain,
% 7.78/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(sK3,k5_xboole_0(X1,sK3)) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_6266,c_1741]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1901,plain,
% 7.78/1.49      ( k5_xboole_0(sK3,k5_xboole_0(X0,sK3)) = X0 ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_2,c_1741]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6922,plain,
% 7.78/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 7.78/1.49      inference(demodulation,[status(thm)],[c_6911,c_1901]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_11765,plain,
% 7.78/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sK3,X1)) = k5_xboole_0(X0,sK3) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_11158,c_6922]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_14626,plain,
% 7.78/1.49      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X0,sK3)) = k5_xboole_0(sK3,k5_xboole_0(sK3,X1)) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_11765,c_3421]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_14689,plain,
% 7.78/1.49      ( k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(X0,X1)),k5_xboole_0(X0,sK3)) = X1 ),
% 7.78/1.49      inference(demodulation,[status(thm)],[c_14626,c_1741,c_11158]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_15362,plain,
% 7.78/1.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK3)),k5_xboole_0(X0,sK3)) = X1 ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_742,c_14689]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_20168,plain,
% 7.78/1.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X0,sK3)) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_2507,c_15362]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_2805,plain,
% 7.78/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,sK3)) = sK3 ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_2,c_2221]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_741,plain,
% 7.78/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_8,c_2]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_10547,plain,
% 7.78/1.49      ( k5_xboole_0(k5_xboole_0(X0,sK3),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,sK3) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_2805,c_741]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_20184,plain,
% 7.78/1.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 7.78/1.49      inference(demodulation,[status(thm)],[c_20168,c_9,c_10547]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_16,plain,
% 7.78/1.49      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 7.78/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_718,plain,
% 7.78/1.49      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_28739,plain,
% 7.78/1.49      ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_20184,c_718]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1282,plain,
% 7.78/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_0,c_1009]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_6,plain,
% 7.78/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.78/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1280,plain,
% 7.78/1.49      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1284,plain,
% 7.78/1.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.78/1.49      inference(light_normalisation,[status(thm)],[c_1280,c_7]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1,plain,
% 7.78/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.78/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1467,plain,
% 7.78/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1284,c_1]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1288,plain,
% 7.78/1.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.78/1.49      inference(demodulation,[status(thm)],[c_1284,c_6]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1479,plain,
% 7.78/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.78/1.49      inference(light_normalisation,[status(thm)],[c_1467,c_1282,c_1288]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1708,plain,
% 7.78/1.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.78/1.49      inference(light_normalisation,[status(thm)],[c_1282,c_1479]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3,plain,
% 7.78/1.49      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 7.78/1.49      | ~ r1_xboole_0(X1,X2) ),
% 7.78/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_727,plain,
% 7.78/1.49      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 7.78/1.49      | r1_xboole_0(X1,X2) != iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_22325,plain,
% 7.78/1.49      ( r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.78/1.49      | r1_xboole_0(k1_xboole_0,X1) != iProver_top ),
% 7.78/1.49      inference(superposition,[status(thm)],[c_1708,c_727]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_22334,plain,
% 7.78/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.78/1.49      | r1_xboole_0(k1_xboole_0,X1) != iProver_top ),
% 7.78/1.49      inference(demodulation,[status(thm)],[c_22325,c_1708]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_22342,plain,
% 7.78/1.49      ( r2_hidden(sK2,k1_xboole_0) != iProver_top
% 7.78/1.49      | r1_xboole_0(k1_xboole_0,sK2) != iProver_top ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_22334]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_5,plain,
% 7.78/1.49      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
% 7.78/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3793,plain,
% 7.78/1.49      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k1_xboole_0)) ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3794,plain,
% 7.78/1.49      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_3793]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3796,plain,
% 7.78/1.49      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)),k5_xboole_0(sK2,k1_xboole_0)) = iProver_top ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_3794]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_534,plain,
% 7.78/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.78/1.49      theory(equality) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_752,plain,
% 7.78/1.49      ( r1_xboole_0(X0,X1)
% 7.78/1.49      | ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k5_xboole_0(X2,X3))
% 7.78/1.49      | X1 != k5_xboole_0(X2,X3)
% 7.78/1.49      | X0 != k4_xboole_0(X2,k4_xboole_0(X2,X3)) ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_534]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_922,plain,
% 7.78/1.49      ( r1_xboole_0(X0,X1)
% 7.78/1.49      | ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)),k5_xboole_0(X2,k1_xboole_0))
% 7.78/1.49      | X1 != k5_xboole_0(X2,k1_xboole_0)
% 7.78/1.49      | X0 != k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)) ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_752]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3306,plain,
% 7.78/1.49      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k1_xboole_0))
% 7.78/1.49      | r1_xboole_0(k1_xboole_0,X1)
% 7.78/1.49      | X1 != k5_xboole_0(X0,k1_xboole_0)
% 7.78/1.49      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_922]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3307,plain,
% 7.78/1.49      ( X0 != k5_xboole_0(X1,k1_xboole_0)
% 7.78/1.49      | k1_xboole_0 != k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))
% 7.78/1.49      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)),k5_xboole_0(X1,k1_xboole_0)) != iProver_top
% 7.78/1.49      | r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 7.78/1.49      inference(predicate_to_equality,[status(thm)],[c_3306]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_3309,plain,
% 7.78/1.49      ( sK2 != k5_xboole_0(sK2,k1_xboole_0)
% 7.78/1.49      | k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0))
% 7.78/1.49      | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)),k5_xboole_0(sK2,k1_xboole_0)) != iProver_top
% 7.78/1.49      | r1_xboole_0(k1_xboole_0,sK2) = iProver_top ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_3307]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_531,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_857,plain,
% 7.78/1.49      ( X0 != X1
% 7.78/1.49      | X0 = k4_xboole_0(X2,k4_xboole_0(X2,X3))
% 7.78/1.49      | k4_xboole_0(X2,k4_xboole_0(X2,X3)) != X1 ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_531]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1228,plain,
% 7.78/1.49      ( X0 != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.78/1.49      | X0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))
% 7.78/1.49      | k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_857]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1683,plain,
% 7.78/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.78/1.49      | k1_xboole_0 != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.78/1.49      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_1228]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1684,plain,
% 7.78/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.78/1.49      | k1_xboole_0 != k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.78/1.49      | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_1683]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_530,plain,( X0 = X0 ),theory(equality) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_1019,plain,
% 7.78/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_530]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_796,plain,
% 7.78/1.49      ( X0 != X1 | X0 = k5_xboole_0(X2,X3) | k5_xboole_0(X2,X3) != X1 ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_531]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_814,plain,
% 7.78/1.49      ( X0 = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.78/1.49      | X0 != k1_xboole_0
% 7.78/1.49      | k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0 ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_796]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_919,plain,
% 7.78/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0
% 7.78/1.49      | k1_xboole_0 = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.78/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_814]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_909,plain,
% 7.78/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0
% 7.78/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.78/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) != k1_xboole_0 ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_814]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_910,plain,
% 7.78/1.49      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != k1_xboole_0
% 7.78/1.49      | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k4_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))))
% 7.78/1.49      | k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) != k1_xboole_0 ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_909]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_819,plain,
% 7.78/1.49      ( X0 != X1
% 7.78/1.49      | X0 = k5_xboole_0(X1,k1_xboole_0)
% 7.78/1.49      | k5_xboole_0(X1,k1_xboole_0) != X1 ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_796]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_820,plain,
% 7.78/1.49      ( k5_xboole_0(sK2,k1_xboole_0) != sK2
% 7.78/1.49      | sK2 = k5_xboole_0(sK2,k1_xboole_0)
% 7.78/1.49      | sK2 != sK2 ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_819]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_40,plain,
% 7.78/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_39,plain,
% 7.78/1.49      ( k5_xboole_0(sK2,k1_xboole_0) = sK2 ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_25,plain,
% 7.78/1.49      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_17,plain,
% 7.78/1.49      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 7.78/1.49      | X0 = X1
% 7.78/1.49      | X0 = X2
% 7.78/1.49      | X0 = X3 ),
% 7.78/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(c_22,plain,
% 7.78/1.49      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 7.78/1.49      | sK2 = sK2 ),
% 7.78/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 7.78/1.49  
% 7.78/1.49  cnf(contradiction,plain,
% 7.78/1.49      ( $false ),
% 7.78/1.49      inference(minisat,
% 7.78/1.49                [status(thm)],
% 7.78/1.49                [c_28739,c_22342,c_3796,c_3309,c_1684,c_1019,c_919,c_910,
% 7.78/1.49                 c_820,c_527,c_40,c_39,c_25,c_22]) ).
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.78/1.49  
% 7.78/1.49  ------                               Statistics
% 7.78/1.49  
% 7.78/1.49  ------ General
% 7.78/1.49  
% 7.78/1.49  abstr_ref_over_cycles:                  0
% 7.78/1.49  abstr_ref_under_cycles:                 0
% 7.78/1.49  gc_basic_clause_elim:                   0
% 7.78/1.49  forced_gc_time:                         0
% 7.78/1.49  parsing_time:                           0.007
% 7.78/1.49  unif_index_cands_time:                  0.
% 7.78/1.49  unif_index_add_time:                    0.
% 7.78/1.49  orderings_time:                         0.
% 7.78/1.49  out_proof_time:                         0.01
% 7.78/1.49  total_time:                             0.868
% 7.78/1.49  num_of_symbols:                         42
% 7.78/1.49  num_of_terms:                           30125
% 7.78/1.49  
% 7.78/1.49  ------ Preprocessing
% 7.78/1.49  
% 7.78/1.49  num_of_splits:                          0
% 7.78/1.49  num_of_split_atoms:                     0
% 7.78/1.49  num_of_reused_defs:                     0
% 7.78/1.49  num_eq_ax_congr_red:                    12
% 7.78/1.49  num_of_sem_filtered_clauses:            1
% 7.78/1.49  num_of_subtypes:                        0
% 7.78/1.49  monotx_restored_types:                  0
% 7.78/1.49  sat_num_of_epr_types:                   0
% 7.78/1.49  sat_num_of_non_cyclic_types:            0
% 7.78/1.49  sat_guarded_non_collapsed_types:        0
% 7.78/1.49  num_pure_diseq_elim:                    0
% 7.78/1.49  simp_replaced_by:                       0
% 7.78/1.49  res_preprocessed:                       77
% 7.78/1.49  prep_upred:                             0
% 7.78/1.49  prep_unflattend:                        28
% 7.78/1.49  smt_new_axioms:                         0
% 7.78/1.49  pred_elim_cands:                        2
% 7.78/1.49  pred_elim:                              0
% 7.78/1.49  pred_elim_cl:                           0
% 7.78/1.49  pred_elim_cycles:                       2
% 7.78/1.49  merged_defs:                            0
% 7.78/1.49  merged_defs_ncl:                        0
% 7.78/1.49  bin_hyper_res:                          0
% 7.78/1.49  prep_cycles:                            3
% 7.78/1.49  pred_elim_time:                         0.006
% 7.78/1.49  splitting_time:                         0.
% 7.78/1.49  sem_filter_time:                        0.
% 7.78/1.49  monotx_time:                            0.
% 7.78/1.49  subtype_inf_time:                       0.
% 7.78/1.49  
% 7.78/1.49  ------ Problem properties
% 7.78/1.49  
% 7.78/1.49  clauses:                                20
% 7.78/1.49  conjectures:                            1
% 7.78/1.49  epr:                                    0
% 7.78/1.49  horn:                                   17
% 7.78/1.49  ground:                                 1
% 7.78/1.49  unary:                                  13
% 7.78/1.49  binary:                                 2
% 7.78/1.49  lits:                                   35
% 7.78/1.49  lits_eq:                                22
% 7.78/1.49  fd_pure:                                0
% 7.78/1.49  fd_pseudo:                              0
% 7.78/1.49  fd_cond:                                0
% 7.78/1.49  fd_pseudo_cond:                         4
% 7.78/1.49  ac_symbols:                             1
% 7.78/1.49  
% 7.78/1.49  ------ Propositional Solver
% 7.78/1.49  
% 7.78/1.49  prop_solver_calls:                      26
% 7.78/1.49  prop_fast_solver_calls:                 680
% 7.78/1.49  smt_solver_calls:                       0
% 7.78/1.49  smt_fast_solver_calls:                  0
% 7.78/1.49  prop_num_of_clauses:                    5700
% 7.78/1.49  prop_preprocess_simplified:             10776
% 7.78/1.49  prop_fo_subsumed:                       1
% 7.78/1.49  prop_solver_time:                       0.
% 7.78/1.49  smt_solver_time:                        0.
% 7.78/1.49  smt_fast_solver_time:                   0.
% 7.78/1.49  prop_fast_solver_time:                  0.
% 7.78/1.49  prop_unsat_core_time:                   0.
% 7.78/1.49  
% 7.78/1.49  ------ QBF
% 7.78/1.49  
% 7.78/1.49  qbf_q_res:                              0
% 7.78/1.49  qbf_num_tautologies:                    0
% 7.78/1.49  qbf_prep_cycles:                        0
% 7.78/1.49  
% 7.78/1.49  ------ BMC1
% 7.78/1.49  
% 7.78/1.49  bmc1_current_bound:                     -1
% 7.78/1.49  bmc1_last_solved_bound:                 -1
% 7.78/1.49  bmc1_unsat_core_size:                   -1
% 7.78/1.49  bmc1_unsat_core_parents_size:           -1
% 7.78/1.49  bmc1_merge_next_fun:                    0
% 7.78/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.78/1.49  
% 7.78/1.49  ------ Instantiation
% 7.78/1.49  
% 7.78/1.49  inst_num_of_clauses:                    1778
% 7.78/1.49  inst_num_in_passive:                    820
% 7.78/1.49  inst_num_in_active:                     551
% 7.78/1.49  inst_num_in_unprocessed:                409
% 7.78/1.49  inst_num_of_loops:                      600
% 7.78/1.49  inst_num_of_learning_restarts:          0
% 7.78/1.49  inst_num_moves_active_passive:          44
% 7.78/1.49  inst_lit_activity:                      0
% 7.78/1.49  inst_lit_activity_moves:                0
% 7.78/1.49  inst_num_tautologies:                   0
% 7.78/1.49  inst_num_prop_implied:                  0
% 7.78/1.49  inst_num_existing_simplified:           0
% 7.78/1.49  inst_num_eq_res_simplified:             0
% 7.78/1.49  inst_num_child_elim:                    0
% 7.78/1.49  inst_num_of_dismatching_blockings:      4739
% 7.78/1.49  inst_num_of_non_proper_insts:           3848
% 7.78/1.49  inst_num_of_duplicates:                 0
% 7.78/1.49  inst_inst_num_from_inst_to_res:         0
% 7.78/1.49  inst_dismatching_checking_time:         0.
% 7.78/1.49  
% 7.78/1.49  ------ Resolution
% 7.78/1.49  
% 7.78/1.49  res_num_of_clauses:                     0
% 7.78/1.49  res_num_in_passive:                     0
% 7.78/1.49  res_num_in_active:                      0
% 7.78/1.49  res_num_of_loops:                       80
% 7.78/1.49  res_forward_subset_subsumed:            1017
% 7.78/1.49  res_backward_subset_subsumed:           10
% 7.78/1.49  res_forward_subsumed:                   0
% 7.78/1.49  res_backward_subsumed:                  0
% 7.78/1.49  res_forward_subsumption_resolution:     1
% 7.78/1.49  res_backward_subsumption_resolution:    0
% 7.78/1.49  res_clause_to_clause_subsumption:       11767
% 7.78/1.49  res_orphan_elimination:                 0
% 7.78/1.49  res_tautology_del:                      512
% 7.78/1.49  res_num_eq_res_simplified:              0
% 7.78/1.49  res_num_sel_changes:                    0
% 7.78/1.49  res_moves_from_active_to_pass:          0
% 7.78/1.49  
% 7.78/1.49  ------ Superposition
% 7.78/1.49  
% 7.78/1.49  sup_time_total:                         0.
% 7.78/1.49  sup_time_generating:                    0.
% 7.78/1.49  sup_time_sim_full:                      0.
% 7.78/1.49  sup_time_sim_immed:                     0.
% 7.78/1.49  
% 7.78/1.49  sup_num_of_clauses:                     913
% 7.78/1.49  sup_num_in_active:                      43
% 7.78/1.49  sup_num_in_passive:                     870
% 7.78/1.49  sup_num_of_loops:                       119
% 7.78/1.49  sup_fw_superposition:                   3879
% 7.78/1.49  sup_bw_superposition:                   2790
% 7.78/1.49  sup_immediate_simplified:               2878
% 7.78/1.49  sup_given_eliminated:                   6
% 7.78/1.49  comparisons_done:                       0
% 7.78/1.49  comparisons_avoided:                    6
% 7.78/1.49  
% 7.78/1.49  ------ Simplifications
% 7.78/1.49  
% 7.78/1.49  
% 7.78/1.49  sim_fw_subset_subsumed:                 6
% 7.78/1.49  sim_bw_subset_subsumed:                 3
% 7.78/1.49  sim_fw_subsumed:                        262
% 7.78/1.49  sim_bw_subsumed:                        17
% 7.78/1.49  sim_fw_subsumption_res:                 0
% 7.78/1.49  sim_bw_subsumption_res:                 0
% 7.78/1.49  sim_tautology_del:                      1
% 7.78/1.49  sim_eq_tautology_del:                   1015
% 7.78/1.49  sim_eq_res_simp:                        0
% 7.78/1.49  sim_fw_demodulated:                     2186
% 7.78/1.49  sim_bw_demodulated:                     128
% 7.78/1.49  sim_light_normalised:                   1270
% 7.78/1.49  sim_joinable_taut:                      171
% 7.78/1.49  sim_joinable_simp:                      0
% 7.78/1.49  sim_ac_normalised:                      0
% 7.78/1.49  sim_smt_subsumption:                    0
% 7.78/1.49  
%------------------------------------------------------------------------------
