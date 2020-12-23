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
% DateTime   : Thu Dec  3 11:35:50 EST 2020

% Result     : Theorem 19.48s
% Output     : CNFRefutation 19.48s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 470 expanded)
%              Number of clauses        :   55 ( 115 expanded)
%              Number of leaves         :   19 ( 136 expanded)
%              Depth                    :   16
%              Number of atoms          :  261 ( 747 expanded)
%              Number of equality atoms :  149 ( 588 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 )
   => ( k1_tarski(sK2) != sK1
      & k1_xboole_0 != sK1
      & k4_xboole_0(sK1,k1_tarski(sK2)) = k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k1_tarski(sK2) != sK1
    & k1_xboole_0 != sK1
    & k4_xboole_0(sK1,k1_tarski(sK2)) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f28])).

fof(f54,plain,(
    k4_xboole_0(sK1,k1_tarski(sK2)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f76,plain,(
    k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f54,f42,f58])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f36,f42,f42])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f47,f42])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f48,f42])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f44,f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f46,f42,f42])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f53,f42,f58])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    k1_tarski(sK2) != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    k2_enumset1(sK2,sK2,sK2,sK2) != sK1 ),
    inference(definition_unfolding,[],[f56,f58])).

fof(f55,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_22,negated_conjecture,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1160,plain,
    ( k2_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),k1_xboole_0) = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_22,c_1])).

cnf(c_17,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1054,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_17,c_0])).

cnf(c_16,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_14,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_702,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_16,c_14])).

cnf(c_1059,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1054,c_702])).

cnf(c_1728,plain,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)) = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_1160,c_1059])).

cnf(c_15,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_691,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2024,plain,
    ( r1_tarski(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1728,c_691])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_693,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2042,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k3_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k2_enumset1(sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2024,c_693])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2127,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k3_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k1_xboole_0)) = k3_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_2042,c_2])).

cnf(c_2130,plain,
    ( k3_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k2_enumset1(sK2,sK2,sK2,sK2)) = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    inference(demodulation,[status(thm)],[c_2127,c_14,c_702])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_690,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_697,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2903,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)) != iProver_top
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1728,c_697])).

cnf(c_3375,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k3_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k2_enumset1(X0,X0,X0,X0))) = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_690,c_2903])).

cnf(c_3435,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k3_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k2_enumset1(X0,X0,X0,X0))) = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(X0,X0,X0,X0))) = sK1 ),
    inference(superposition,[status(thm)],[c_690,c_3375])).

cnf(c_45497,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)) = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = sK1 ),
    inference(superposition,[status(thm)],[c_2130,c_3435])).

cnf(c_1136,plain,
    ( k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_22,c_2])).

cnf(c_1144,plain,
    ( k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1136,c_14,c_702])).

cnf(c_45655,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)) = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | k5_xboole_0(sK1,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_45497,c_1144])).

cnf(c_1137,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14,c_2])).

cnf(c_1143,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1137,c_14,c_702])).

cnf(c_1907,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1143,c_2])).

cnf(c_1910,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1907,c_14,c_702])).

cnf(c_1911,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1910,c_1143])).

cnf(c_45656,plain,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_45655,c_1911])).

cnf(c_13,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_692,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2023,plain,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1) != k1_xboole_0
    | r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1728,c_692])).

cnf(c_828,plain,
    ( r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_767,plain,
    ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_768,plain,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)) = k1_xboole_0
    | r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_767])).

cnf(c_727,plain,
    ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_350,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_725,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_726,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_725])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_717,plain,
    ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_43,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_35,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_29,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_20,negated_conjecture,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_45656,c_2023,c_828,c_768,c_727,c_726,c_717,c_43,c_35,c_29,c_20,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:44:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.48/2.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.48/2.97  
% 19.48/2.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.48/2.97  
% 19.48/2.97  ------  iProver source info
% 19.48/2.97  
% 19.48/2.97  git: date: 2020-06-30 10:37:57 +0100
% 19.48/2.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.48/2.97  git: non_committed_changes: false
% 19.48/2.97  git: last_make_outside_of_git: false
% 19.48/2.97  
% 19.48/2.97  ------ 
% 19.48/2.97  
% 19.48/2.97  ------ Input Options
% 19.48/2.97  
% 19.48/2.97  --out_options                           all
% 19.48/2.97  --tptp_safe_out                         true
% 19.48/2.97  --problem_path                          ""
% 19.48/2.97  --include_path                          ""
% 19.48/2.97  --clausifier                            res/vclausify_rel
% 19.48/2.97  --clausifier_options                    ""
% 19.48/2.97  --stdin                                 false
% 19.48/2.97  --stats_out                             all
% 19.48/2.97  
% 19.48/2.97  ------ General Options
% 19.48/2.97  
% 19.48/2.97  --fof                                   false
% 19.48/2.97  --time_out_real                         305.
% 19.48/2.97  --time_out_virtual                      -1.
% 19.48/2.97  --symbol_type_check                     false
% 19.48/2.97  --clausify_out                          false
% 19.48/2.97  --sig_cnt_out                           false
% 19.48/2.97  --trig_cnt_out                          false
% 19.48/2.97  --trig_cnt_out_tolerance                1.
% 19.48/2.97  --trig_cnt_out_sk_spl                   false
% 19.48/2.97  --abstr_cl_out                          false
% 19.48/2.97  
% 19.48/2.97  ------ Global Options
% 19.48/2.97  
% 19.48/2.97  --schedule                              default
% 19.48/2.97  --add_important_lit                     false
% 19.48/2.97  --prop_solver_per_cl                    1000
% 19.48/2.97  --min_unsat_core                        false
% 19.48/2.97  --soft_assumptions                      false
% 19.48/2.97  --soft_lemma_size                       3
% 19.48/2.97  --prop_impl_unit_size                   0
% 19.48/2.97  --prop_impl_unit                        []
% 19.48/2.97  --share_sel_clauses                     true
% 19.48/2.97  --reset_solvers                         false
% 19.48/2.97  --bc_imp_inh                            [conj_cone]
% 19.48/2.97  --conj_cone_tolerance                   3.
% 19.48/2.97  --extra_neg_conj                        none
% 19.48/2.97  --large_theory_mode                     true
% 19.48/2.97  --prolific_symb_bound                   200
% 19.48/2.97  --lt_threshold                          2000
% 19.48/2.97  --clause_weak_htbl                      true
% 19.48/2.97  --gc_record_bc_elim                     false
% 19.48/2.97  
% 19.48/2.97  ------ Preprocessing Options
% 19.48/2.97  
% 19.48/2.97  --preprocessing_flag                    true
% 19.48/2.97  --time_out_prep_mult                    0.1
% 19.48/2.97  --splitting_mode                        input
% 19.48/2.97  --splitting_grd                         true
% 19.48/2.97  --splitting_cvd                         false
% 19.48/2.97  --splitting_cvd_svl                     false
% 19.48/2.97  --splitting_nvd                         32
% 19.48/2.97  --sub_typing                            true
% 19.48/2.97  --prep_gs_sim                           true
% 19.48/2.97  --prep_unflatten                        true
% 19.48/2.97  --prep_res_sim                          true
% 19.48/2.97  --prep_upred                            true
% 19.48/2.97  --prep_sem_filter                       exhaustive
% 19.48/2.97  --prep_sem_filter_out                   false
% 19.48/2.97  --pred_elim                             true
% 19.48/2.97  --res_sim_input                         true
% 19.48/2.97  --eq_ax_congr_red                       true
% 19.48/2.97  --pure_diseq_elim                       true
% 19.48/2.97  --brand_transform                       false
% 19.48/2.97  --non_eq_to_eq                          false
% 19.48/2.97  --prep_def_merge                        true
% 19.48/2.97  --prep_def_merge_prop_impl              false
% 19.48/2.97  --prep_def_merge_mbd                    true
% 19.48/2.97  --prep_def_merge_tr_red                 false
% 19.48/2.97  --prep_def_merge_tr_cl                  false
% 19.48/2.97  --smt_preprocessing                     true
% 19.48/2.97  --smt_ac_axioms                         fast
% 19.48/2.97  --preprocessed_out                      false
% 19.48/2.97  --preprocessed_stats                    false
% 19.48/2.97  
% 19.48/2.97  ------ Abstraction refinement Options
% 19.48/2.97  
% 19.48/2.97  --abstr_ref                             []
% 19.48/2.97  --abstr_ref_prep                        false
% 19.48/2.97  --abstr_ref_until_sat                   false
% 19.48/2.97  --abstr_ref_sig_restrict                funpre
% 19.48/2.97  --abstr_ref_af_restrict_to_split_sk     false
% 19.48/2.97  --abstr_ref_under                       []
% 19.48/2.97  
% 19.48/2.97  ------ SAT Options
% 19.48/2.97  
% 19.48/2.97  --sat_mode                              false
% 19.48/2.97  --sat_fm_restart_options                ""
% 19.48/2.97  --sat_gr_def                            false
% 19.48/2.97  --sat_epr_types                         true
% 19.48/2.97  --sat_non_cyclic_types                  false
% 19.48/2.97  --sat_finite_models                     false
% 19.48/2.97  --sat_fm_lemmas                         false
% 19.48/2.97  --sat_fm_prep                           false
% 19.48/2.97  --sat_fm_uc_incr                        true
% 19.48/2.97  --sat_out_model                         small
% 19.48/2.97  --sat_out_clauses                       false
% 19.48/2.97  
% 19.48/2.97  ------ QBF Options
% 19.48/2.97  
% 19.48/2.97  --qbf_mode                              false
% 19.48/2.97  --qbf_elim_univ                         false
% 19.48/2.97  --qbf_dom_inst                          none
% 19.48/2.97  --qbf_dom_pre_inst                      false
% 19.48/2.97  --qbf_sk_in                             false
% 19.48/2.97  --qbf_pred_elim                         true
% 19.48/2.97  --qbf_split                             512
% 19.48/2.97  
% 19.48/2.97  ------ BMC1 Options
% 19.48/2.97  
% 19.48/2.97  --bmc1_incremental                      false
% 19.48/2.97  --bmc1_axioms                           reachable_all
% 19.48/2.97  --bmc1_min_bound                        0
% 19.48/2.97  --bmc1_max_bound                        -1
% 19.48/2.97  --bmc1_max_bound_default                -1
% 19.48/2.97  --bmc1_symbol_reachability              true
% 19.48/2.97  --bmc1_property_lemmas                  false
% 19.48/2.97  --bmc1_k_induction                      false
% 19.48/2.97  --bmc1_non_equiv_states                 false
% 19.48/2.97  --bmc1_deadlock                         false
% 19.48/2.97  --bmc1_ucm                              false
% 19.48/2.97  --bmc1_add_unsat_core                   none
% 19.48/2.97  --bmc1_unsat_core_children              false
% 19.48/2.97  --bmc1_unsat_core_extrapolate_axioms    false
% 19.48/2.97  --bmc1_out_stat                         full
% 19.48/2.97  --bmc1_ground_init                      false
% 19.48/2.97  --bmc1_pre_inst_next_state              false
% 19.48/2.97  --bmc1_pre_inst_state                   false
% 19.48/2.97  --bmc1_pre_inst_reach_state             false
% 19.48/2.97  --bmc1_out_unsat_core                   false
% 19.48/2.97  --bmc1_aig_witness_out                  false
% 19.48/2.97  --bmc1_verbose                          false
% 19.48/2.97  --bmc1_dump_clauses_tptp                false
% 19.48/2.97  --bmc1_dump_unsat_core_tptp             false
% 19.48/2.97  --bmc1_dump_file                        -
% 19.48/2.97  --bmc1_ucm_expand_uc_limit              128
% 19.48/2.97  --bmc1_ucm_n_expand_iterations          6
% 19.48/2.97  --bmc1_ucm_extend_mode                  1
% 19.48/2.97  --bmc1_ucm_init_mode                    2
% 19.48/2.97  --bmc1_ucm_cone_mode                    none
% 19.48/2.97  --bmc1_ucm_reduced_relation_type        0
% 19.48/2.97  --bmc1_ucm_relax_model                  4
% 19.48/2.97  --bmc1_ucm_full_tr_after_sat            true
% 19.48/2.97  --bmc1_ucm_expand_neg_assumptions       false
% 19.48/2.97  --bmc1_ucm_layered_model                none
% 19.48/2.97  --bmc1_ucm_max_lemma_size               10
% 19.48/2.97  
% 19.48/2.97  ------ AIG Options
% 19.48/2.97  
% 19.48/2.97  --aig_mode                              false
% 19.48/2.97  
% 19.48/2.97  ------ Instantiation Options
% 19.48/2.97  
% 19.48/2.97  --instantiation_flag                    true
% 19.48/2.97  --inst_sos_flag                         true
% 19.48/2.97  --inst_sos_phase                        true
% 19.48/2.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.48/2.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.48/2.97  --inst_lit_sel_side                     num_symb
% 19.48/2.97  --inst_solver_per_active                1400
% 19.48/2.97  --inst_solver_calls_frac                1.
% 19.48/2.97  --inst_passive_queue_type               priority_queues
% 19.48/2.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.48/2.97  --inst_passive_queues_freq              [25;2]
% 19.48/2.97  --inst_dismatching                      true
% 19.48/2.97  --inst_eager_unprocessed_to_passive     true
% 19.48/2.97  --inst_prop_sim_given                   true
% 19.48/2.97  --inst_prop_sim_new                     false
% 19.48/2.97  --inst_subs_new                         false
% 19.48/2.97  --inst_eq_res_simp                      false
% 19.48/2.97  --inst_subs_given                       false
% 19.48/2.97  --inst_orphan_elimination               true
% 19.48/2.97  --inst_learning_loop_flag               true
% 19.48/2.97  --inst_learning_start                   3000
% 19.48/2.97  --inst_learning_factor                  2
% 19.48/2.97  --inst_start_prop_sim_after_learn       3
% 19.48/2.97  --inst_sel_renew                        solver
% 19.48/2.97  --inst_lit_activity_flag                true
% 19.48/2.97  --inst_restr_to_given                   false
% 19.48/2.97  --inst_activity_threshold               500
% 19.48/2.97  --inst_out_proof                        true
% 19.48/2.97  
% 19.48/2.97  ------ Resolution Options
% 19.48/2.97  
% 19.48/2.97  --resolution_flag                       true
% 19.48/2.97  --res_lit_sel                           adaptive
% 19.48/2.97  --res_lit_sel_side                      none
% 19.48/2.97  --res_ordering                          kbo
% 19.48/2.97  --res_to_prop_solver                    active
% 19.48/2.97  --res_prop_simpl_new                    false
% 19.48/2.97  --res_prop_simpl_given                  true
% 19.48/2.97  --res_passive_queue_type                priority_queues
% 19.48/2.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.48/2.97  --res_passive_queues_freq               [15;5]
% 19.48/2.97  --res_forward_subs                      full
% 19.48/2.97  --res_backward_subs                     full
% 19.48/2.97  --res_forward_subs_resolution           true
% 19.48/2.97  --res_backward_subs_resolution          true
% 19.48/2.97  --res_orphan_elimination                true
% 19.48/2.97  --res_time_limit                        2.
% 19.48/2.97  --res_out_proof                         true
% 19.48/2.97  
% 19.48/2.97  ------ Superposition Options
% 19.48/2.97  
% 19.48/2.97  --superposition_flag                    true
% 19.48/2.97  --sup_passive_queue_type                priority_queues
% 19.48/2.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.48/2.97  --sup_passive_queues_freq               [8;1;4]
% 19.48/2.97  --demod_completeness_check              fast
% 19.48/2.97  --demod_use_ground                      true
% 19.48/2.97  --sup_to_prop_solver                    passive
% 19.48/2.97  --sup_prop_simpl_new                    true
% 19.48/2.97  --sup_prop_simpl_given                  true
% 19.48/2.97  --sup_fun_splitting                     true
% 19.48/2.97  --sup_smt_interval                      50000
% 19.48/2.97  
% 19.48/2.97  ------ Superposition Simplification Setup
% 19.48/2.97  
% 19.48/2.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.48/2.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.48/2.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.48/2.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.48/2.97  --sup_full_triv                         [TrivRules;PropSubs]
% 19.48/2.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.48/2.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.48/2.97  --sup_immed_triv                        [TrivRules]
% 19.48/2.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.48/2.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.48/2.97  --sup_immed_bw_main                     []
% 19.48/2.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.48/2.97  --sup_input_triv                        [Unflattening;TrivRules]
% 19.48/2.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.48/2.97  --sup_input_bw                          []
% 19.48/2.97  
% 19.48/2.97  ------ Combination Options
% 19.48/2.97  
% 19.48/2.97  --comb_res_mult                         3
% 19.48/2.97  --comb_sup_mult                         2
% 19.48/2.97  --comb_inst_mult                        10
% 19.48/2.97  
% 19.48/2.97  ------ Debug Options
% 19.48/2.97  
% 19.48/2.97  --dbg_backtrace                         false
% 19.48/2.97  --dbg_dump_prop_clauses                 false
% 19.48/2.97  --dbg_dump_prop_clauses_file            -
% 19.48/2.97  --dbg_out_stat                          false
% 19.48/2.97  ------ Parsing...
% 19.48/2.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.48/2.97  
% 19.48/2.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.48/2.97  
% 19.48/2.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.48/2.97  
% 19.48/2.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.48/2.97  ------ Proving...
% 19.48/2.97  ------ Problem Properties 
% 19.48/2.97  
% 19.48/2.97  
% 19.48/2.97  clauses                                 22
% 19.48/2.97  conjectures                             3
% 19.48/2.97  EPR                                     3
% 19.48/2.97  Horn                                    17
% 19.48/2.97  unary                                   11
% 19.48/2.97  binary                                  6
% 19.48/2.97  lits                                    39
% 19.48/2.97  lits eq                                 17
% 19.48/2.97  fd_pure                                 0
% 19.48/2.97  fd_pseudo                               0
% 19.48/2.97  fd_cond                                 0
% 19.48/2.97  fd_pseudo_cond                          4
% 19.48/2.97  AC symbols                              0
% 19.48/2.97  
% 19.48/2.97  ------ Schedule dynamic 5 is on 
% 19.48/2.97  
% 19.48/2.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.48/2.97  
% 19.48/2.97  
% 19.48/2.97  ------ 
% 19.48/2.97  Current options:
% 19.48/2.97  ------ 
% 19.48/2.97  
% 19.48/2.97  ------ Input Options
% 19.48/2.97  
% 19.48/2.97  --out_options                           all
% 19.48/2.97  --tptp_safe_out                         true
% 19.48/2.97  --problem_path                          ""
% 19.48/2.97  --include_path                          ""
% 19.48/2.97  --clausifier                            res/vclausify_rel
% 19.48/2.97  --clausifier_options                    ""
% 19.48/2.97  --stdin                                 false
% 19.48/2.97  --stats_out                             all
% 19.48/2.97  
% 19.48/2.97  ------ General Options
% 19.48/2.97  
% 19.48/2.97  --fof                                   false
% 19.48/2.97  --time_out_real                         305.
% 19.48/2.97  --time_out_virtual                      -1.
% 19.48/2.97  --symbol_type_check                     false
% 19.48/2.97  --clausify_out                          false
% 19.48/2.97  --sig_cnt_out                           false
% 19.48/2.97  --trig_cnt_out                          false
% 19.48/2.97  --trig_cnt_out_tolerance                1.
% 19.48/2.97  --trig_cnt_out_sk_spl                   false
% 19.48/2.97  --abstr_cl_out                          false
% 19.48/2.97  
% 19.48/2.97  ------ Global Options
% 19.48/2.97  
% 19.48/2.97  --schedule                              default
% 19.48/2.97  --add_important_lit                     false
% 19.48/2.97  --prop_solver_per_cl                    1000
% 19.48/2.97  --min_unsat_core                        false
% 19.48/2.97  --soft_assumptions                      false
% 19.48/2.97  --soft_lemma_size                       3
% 19.48/2.97  --prop_impl_unit_size                   0
% 19.48/2.97  --prop_impl_unit                        []
% 19.48/2.97  --share_sel_clauses                     true
% 19.48/2.97  --reset_solvers                         false
% 19.48/2.97  --bc_imp_inh                            [conj_cone]
% 19.48/2.97  --conj_cone_tolerance                   3.
% 19.48/2.97  --extra_neg_conj                        none
% 19.48/2.97  --large_theory_mode                     true
% 19.48/2.97  --prolific_symb_bound                   200
% 19.48/2.97  --lt_threshold                          2000
% 19.48/2.97  --clause_weak_htbl                      true
% 19.48/2.97  --gc_record_bc_elim                     false
% 19.48/2.97  
% 19.48/2.97  ------ Preprocessing Options
% 19.48/2.97  
% 19.48/2.97  --preprocessing_flag                    true
% 19.48/2.97  --time_out_prep_mult                    0.1
% 19.48/2.97  --splitting_mode                        input
% 19.48/2.97  --splitting_grd                         true
% 19.48/2.97  --splitting_cvd                         false
% 19.48/2.97  --splitting_cvd_svl                     false
% 19.48/2.97  --splitting_nvd                         32
% 19.48/2.97  --sub_typing                            true
% 19.48/2.97  --prep_gs_sim                           true
% 19.48/2.97  --prep_unflatten                        true
% 19.48/2.97  --prep_res_sim                          true
% 19.48/2.97  --prep_upred                            true
% 19.48/2.97  --prep_sem_filter                       exhaustive
% 19.48/2.97  --prep_sem_filter_out                   false
% 19.48/2.97  --pred_elim                             true
% 19.48/2.97  --res_sim_input                         true
% 19.48/2.97  --eq_ax_congr_red                       true
% 19.48/2.97  --pure_diseq_elim                       true
% 19.48/2.97  --brand_transform                       false
% 19.48/2.97  --non_eq_to_eq                          false
% 19.48/2.97  --prep_def_merge                        true
% 19.48/2.97  --prep_def_merge_prop_impl              false
% 19.48/2.97  --prep_def_merge_mbd                    true
% 19.48/2.97  --prep_def_merge_tr_red                 false
% 19.48/2.97  --prep_def_merge_tr_cl                  false
% 19.48/2.97  --smt_preprocessing                     true
% 19.48/2.97  --smt_ac_axioms                         fast
% 19.48/2.97  --preprocessed_out                      false
% 19.48/2.97  --preprocessed_stats                    false
% 19.48/2.97  
% 19.48/2.97  ------ Abstraction refinement Options
% 19.48/2.97  
% 19.48/2.97  --abstr_ref                             []
% 19.48/2.97  --abstr_ref_prep                        false
% 19.48/2.97  --abstr_ref_until_sat                   false
% 19.48/2.97  --abstr_ref_sig_restrict                funpre
% 19.48/2.97  --abstr_ref_af_restrict_to_split_sk     false
% 19.48/2.97  --abstr_ref_under                       []
% 19.48/2.97  
% 19.48/2.97  ------ SAT Options
% 19.48/2.97  
% 19.48/2.97  --sat_mode                              false
% 19.48/2.97  --sat_fm_restart_options                ""
% 19.48/2.97  --sat_gr_def                            false
% 19.48/2.97  --sat_epr_types                         true
% 19.48/2.97  --sat_non_cyclic_types                  false
% 19.48/2.97  --sat_finite_models                     false
% 19.48/2.97  --sat_fm_lemmas                         false
% 19.48/2.97  --sat_fm_prep                           false
% 19.48/2.97  --sat_fm_uc_incr                        true
% 19.48/2.97  --sat_out_model                         small
% 19.48/2.97  --sat_out_clauses                       false
% 19.48/2.97  
% 19.48/2.97  ------ QBF Options
% 19.48/2.97  
% 19.48/2.97  --qbf_mode                              false
% 19.48/2.97  --qbf_elim_univ                         false
% 19.48/2.97  --qbf_dom_inst                          none
% 19.48/2.97  --qbf_dom_pre_inst                      false
% 19.48/2.97  --qbf_sk_in                             false
% 19.48/2.97  --qbf_pred_elim                         true
% 19.48/2.97  --qbf_split                             512
% 19.48/2.97  
% 19.48/2.97  ------ BMC1 Options
% 19.48/2.97  
% 19.48/2.97  --bmc1_incremental                      false
% 19.48/2.97  --bmc1_axioms                           reachable_all
% 19.48/2.97  --bmc1_min_bound                        0
% 19.48/2.97  --bmc1_max_bound                        -1
% 19.48/2.97  --bmc1_max_bound_default                -1
% 19.48/2.97  --bmc1_symbol_reachability              true
% 19.48/2.97  --bmc1_property_lemmas                  false
% 19.48/2.97  --bmc1_k_induction                      false
% 19.48/2.97  --bmc1_non_equiv_states                 false
% 19.48/2.97  --bmc1_deadlock                         false
% 19.48/2.97  --bmc1_ucm                              false
% 19.48/2.97  --bmc1_add_unsat_core                   none
% 19.48/2.97  --bmc1_unsat_core_children              false
% 19.48/2.97  --bmc1_unsat_core_extrapolate_axioms    false
% 19.48/2.97  --bmc1_out_stat                         full
% 19.48/2.97  --bmc1_ground_init                      false
% 19.48/2.97  --bmc1_pre_inst_next_state              false
% 19.48/2.97  --bmc1_pre_inst_state                   false
% 19.48/2.97  --bmc1_pre_inst_reach_state             false
% 19.48/2.97  --bmc1_out_unsat_core                   false
% 19.48/2.97  --bmc1_aig_witness_out                  false
% 19.48/2.97  --bmc1_verbose                          false
% 19.48/2.97  --bmc1_dump_clauses_tptp                false
% 19.48/2.97  --bmc1_dump_unsat_core_tptp             false
% 19.48/2.97  --bmc1_dump_file                        -
% 19.48/2.97  --bmc1_ucm_expand_uc_limit              128
% 19.48/2.97  --bmc1_ucm_n_expand_iterations          6
% 19.48/2.97  --bmc1_ucm_extend_mode                  1
% 19.48/2.97  --bmc1_ucm_init_mode                    2
% 19.48/2.97  --bmc1_ucm_cone_mode                    none
% 19.48/2.97  --bmc1_ucm_reduced_relation_type        0
% 19.48/2.97  --bmc1_ucm_relax_model                  4
% 19.48/2.97  --bmc1_ucm_full_tr_after_sat            true
% 19.48/2.97  --bmc1_ucm_expand_neg_assumptions       false
% 19.48/2.97  --bmc1_ucm_layered_model                none
% 19.48/2.97  --bmc1_ucm_max_lemma_size               10
% 19.48/2.97  
% 19.48/2.97  ------ AIG Options
% 19.48/2.97  
% 19.48/2.97  --aig_mode                              false
% 19.48/2.97  
% 19.48/2.97  ------ Instantiation Options
% 19.48/2.97  
% 19.48/2.97  --instantiation_flag                    true
% 19.48/2.97  --inst_sos_flag                         true
% 19.48/2.97  --inst_sos_phase                        true
% 19.48/2.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.48/2.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.48/2.97  --inst_lit_sel_side                     none
% 19.48/2.97  --inst_solver_per_active                1400
% 19.48/2.97  --inst_solver_calls_frac                1.
% 19.48/2.97  --inst_passive_queue_type               priority_queues
% 19.48/2.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.48/2.97  --inst_passive_queues_freq              [25;2]
% 19.48/2.97  --inst_dismatching                      true
% 19.48/2.97  --inst_eager_unprocessed_to_passive     true
% 19.48/2.97  --inst_prop_sim_given                   true
% 19.48/2.97  --inst_prop_sim_new                     false
% 19.48/2.97  --inst_subs_new                         false
% 19.48/2.97  --inst_eq_res_simp                      false
% 19.48/2.97  --inst_subs_given                       false
% 19.48/2.97  --inst_orphan_elimination               true
% 19.48/2.97  --inst_learning_loop_flag               true
% 19.48/2.97  --inst_learning_start                   3000
% 19.48/2.97  --inst_learning_factor                  2
% 19.48/2.97  --inst_start_prop_sim_after_learn       3
% 19.48/2.97  --inst_sel_renew                        solver
% 19.48/2.97  --inst_lit_activity_flag                true
% 19.48/2.97  --inst_restr_to_given                   false
% 19.48/2.97  --inst_activity_threshold               500
% 19.48/2.97  --inst_out_proof                        true
% 19.48/2.97  
% 19.48/2.97  ------ Resolution Options
% 19.48/2.97  
% 19.48/2.97  --resolution_flag                       false
% 19.48/2.97  --res_lit_sel                           adaptive
% 19.48/2.97  --res_lit_sel_side                      none
% 19.48/2.97  --res_ordering                          kbo
% 19.48/2.97  --res_to_prop_solver                    active
% 19.48/2.97  --res_prop_simpl_new                    false
% 19.48/2.97  --res_prop_simpl_given                  true
% 19.48/2.97  --res_passive_queue_type                priority_queues
% 19.48/2.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.48/2.97  --res_passive_queues_freq               [15;5]
% 19.48/2.97  --res_forward_subs                      full
% 19.48/2.97  --res_backward_subs                     full
% 19.48/2.97  --res_forward_subs_resolution           true
% 19.48/2.97  --res_backward_subs_resolution          true
% 19.48/2.97  --res_orphan_elimination                true
% 19.48/2.97  --res_time_limit                        2.
% 19.48/2.97  --res_out_proof                         true
% 19.48/2.97  
% 19.48/2.97  ------ Superposition Options
% 19.48/2.97  
% 19.48/2.97  --superposition_flag                    true
% 19.48/2.97  --sup_passive_queue_type                priority_queues
% 19.48/2.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.48/2.97  --sup_passive_queues_freq               [8;1;4]
% 19.48/2.97  --demod_completeness_check              fast
% 19.48/2.97  --demod_use_ground                      true
% 19.48/2.97  --sup_to_prop_solver                    passive
% 19.48/2.97  --sup_prop_simpl_new                    true
% 19.48/2.97  --sup_prop_simpl_given                  true
% 19.48/2.97  --sup_fun_splitting                     true
% 19.48/2.97  --sup_smt_interval                      50000
% 19.48/2.97  
% 19.48/2.97  ------ Superposition Simplification Setup
% 19.48/2.97  
% 19.48/2.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.48/2.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.48/2.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.48/2.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.48/2.97  --sup_full_triv                         [TrivRules;PropSubs]
% 19.48/2.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.48/2.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.48/2.97  --sup_immed_triv                        [TrivRules]
% 19.48/2.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.48/2.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.48/2.97  --sup_immed_bw_main                     []
% 19.48/2.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.48/2.97  --sup_input_triv                        [Unflattening;TrivRules]
% 19.48/2.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.48/2.97  --sup_input_bw                          []
% 19.48/2.97  
% 19.48/2.97  ------ Combination Options
% 19.48/2.97  
% 19.48/2.97  --comb_res_mult                         3
% 19.48/2.97  --comb_sup_mult                         2
% 19.48/2.97  --comb_inst_mult                        10
% 19.48/2.97  
% 19.48/2.97  ------ Debug Options
% 19.48/2.97  
% 19.48/2.97  --dbg_backtrace                         false
% 19.48/2.97  --dbg_dump_prop_clauses                 false
% 19.48/2.97  --dbg_dump_prop_clauses_file            -
% 19.48/2.97  --dbg_out_stat                          false
% 19.48/2.97  
% 19.48/2.97  
% 19.48/2.97  
% 19.48/2.97  
% 19.48/2.97  ------ Proving...
% 19.48/2.97  
% 19.48/2.97  
% 19.48/2.97  % SZS status Theorem for theBenchmark.p
% 19.48/2.97  
% 19.48/2.97  % SZS output start CNFRefutation for theBenchmark.p
% 19.48/2.97  
% 19.48/2.97  fof(f16,conjecture,(
% 19.48/2.97    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 19.48/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.48/2.97  
% 19.48/2.97  fof(f17,negated_conjecture,(
% 19.48/2.97    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 19.48/2.97    inference(negated_conjecture,[],[f16])).
% 19.48/2.97  
% 19.48/2.97  fof(f18,plain,(
% 19.48/2.97    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 19.48/2.97    inference(ennf_transformation,[],[f17])).
% 19.48/2.97  
% 19.48/2.97  fof(f28,plain,(
% 19.48/2.97    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0) => (k1_tarski(sK2) != sK1 & k1_xboole_0 != sK1 & k4_xboole_0(sK1,k1_tarski(sK2)) = k1_xboole_0)),
% 19.48/2.97    introduced(choice_axiom,[])).
% 19.48/2.97  
% 19.48/2.97  fof(f29,plain,(
% 19.48/2.97    k1_tarski(sK2) != sK1 & k1_xboole_0 != sK1 & k4_xboole_0(sK1,k1_tarski(sK2)) = k1_xboole_0),
% 19.48/2.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f28])).
% 19.48/2.97  
% 19.48/2.97  fof(f54,plain,(
% 19.48/2.97    k4_xboole_0(sK1,k1_tarski(sK2)) = k1_xboole_0),
% 19.48/2.97    inference(cnf_transformation,[],[f29])).
% 19.48/2.97  
% 19.48/2.97  fof(f5,axiom,(
% 19.48/2.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 19.48/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.48/2.97  
% 19.48/2.97  fof(f42,plain,(
% 19.48/2.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 19.48/2.97    inference(cnf_transformation,[],[f5])).
% 19.48/2.97  
% 19.48/2.97  fof(f12,axiom,(
% 19.48/2.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.48/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.48/2.97  
% 19.48/2.97  fof(f49,plain,(
% 19.48/2.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.48/2.97    inference(cnf_transformation,[],[f12])).
% 19.48/2.97  
% 19.48/2.97  fof(f13,axiom,(
% 19.48/2.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.48/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.48/2.97  
% 19.48/2.97  fof(f50,plain,(
% 19.48/2.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.48/2.97    inference(cnf_transformation,[],[f13])).
% 19.48/2.97  
% 19.48/2.97  fof(f14,axiom,(
% 19.48/2.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.48/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.48/2.97  
% 19.48/2.97  fof(f51,plain,(
% 19.48/2.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.48/2.97    inference(cnf_transformation,[],[f14])).
% 19.48/2.97  
% 19.48/2.97  fof(f57,plain,(
% 19.48/2.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.48/2.97    inference(definition_unfolding,[],[f50,f51])).
% 19.48/2.97  
% 19.48/2.97  fof(f58,plain,(
% 19.48/2.97    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 19.48/2.97    inference(definition_unfolding,[],[f49,f57])).
% 19.48/2.97  
% 19.48/2.97  fof(f76,plain,(
% 19.48/2.97    k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = k1_xboole_0),
% 19.48/2.97    inference(definition_unfolding,[],[f54,f42,f58])).
% 19.48/2.97  
% 19.48/2.97  fof(f2,axiom,(
% 19.48/2.97    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 19.48/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.48/2.97  
% 19.48/2.97  fof(f36,plain,(
% 19.48/2.97    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 19.48/2.97    inference(cnf_transformation,[],[f2])).
% 19.48/2.97  
% 19.48/2.97  fof(f60,plain,(
% 19.48/2.97    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 19.48/2.97    inference(definition_unfolding,[],[f36,f42,f42])).
% 19.48/2.97  
% 19.48/2.97  fof(f10,axiom,(
% 19.48/2.97    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 19.48/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.48/2.97  
% 19.48/2.97  fof(f47,plain,(
% 19.48/2.97    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 19.48/2.97    inference(cnf_transformation,[],[f10])).
% 19.48/2.97  
% 19.48/2.97  fof(f72,plain,(
% 19.48/2.97    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0) )),
% 19.48/2.97    inference(definition_unfolding,[],[f47,f42])).
% 19.48/2.97  
% 19.48/2.97  fof(f11,axiom,(
% 19.48/2.97    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 19.48/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.48/2.97  
% 19.48/2.97  fof(f48,plain,(
% 19.48/2.97    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 19.48/2.97    inference(cnf_transformation,[],[f11])).
% 19.48/2.97  
% 19.48/2.97  fof(f59,plain,(
% 19.48/2.97    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 19.48/2.97    inference(definition_unfolding,[],[f48,f42])).
% 19.48/2.97  
% 19.48/2.97  fof(f8,axiom,(
% 19.48/2.97    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 19.48/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.48/2.97  
% 19.48/2.97  fof(f45,plain,(
% 19.48/2.97    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.48/2.97    inference(cnf_transformation,[],[f8])).
% 19.48/2.97  
% 19.48/2.97  fof(f71,plain,(
% 19.48/2.97    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 19.48/2.97    inference(definition_unfolding,[],[f45,f42])).
% 19.48/2.97  
% 19.48/2.97  fof(f6,axiom,(
% 19.48/2.97    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 19.48/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.48/2.97  
% 19.48/2.97  fof(f43,plain,(
% 19.48/2.97    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 19.48/2.97    inference(cnf_transformation,[],[f6])).
% 19.48/2.97  
% 19.48/2.97  fof(f7,axiom,(
% 19.48/2.97    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 19.48/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.48/2.97  
% 19.48/2.97  fof(f44,plain,(
% 19.48/2.97    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 19.48/2.97    inference(cnf_transformation,[],[f7])).
% 19.48/2.97  
% 19.48/2.97  fof(f70,plain,(
% 19.48/2.97    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 19.48/2.97    inference(definition_unfolding,[],[f44,f42])).
% 19.48/2.97  
% 19.48/2.97  fof(f4,axiom,(
% 19.48/2.97    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 19.48/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.48/2.97  
% 19.48/2.97  fof(f26,plain,(
% 19.48/2.97    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 19.48/2.97    inference(nnf_transformation,[],[f4])).
% 19.48/2.97  
% 19.48/2.97  fof(f41,plain,(
% 19.48/2.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 19.48/2.97    inference(cnf_transformation,[],[f26])).
% 19.48/2.97  
% 19.48/2.97  fof(f68,plain,(
% 19.48/2.97    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 19.48/2.97    inference(definition_unfolding,[],[f41,f42])).
% 19.48/2.97  
% 19.48/2.97  fof(f9,axiom,(
% 19.48/2.97    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 19.48/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.48/2.97  
% 19.48/2.97  fof(f46,plain,(
% 19.48/2.97    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 19.48/2.97    inference(cnf_transformation,[],[f9])).
% 19.48/2.97  
% 19.48/2.97  fof(f61,plain,(
% 19.48/2.97    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1)) )),
% 19.48/2.97    inference(definition_unfolding,[],[f46,f42,f42])).
% 19.48/2.97  
% 19.48/2.97  fof(f15,axiom,(
% 19.48/2.97    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 19.48/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.48/2.97  
% 19.48/2.97  fof(f27,plain,(
% 19.48/2.97    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 19.48/2.97    inference(nnf_transformation,[],[f15])).
% 19.48/2.97  
% 19.48/2.97  fof(f53,plain,(
% 19.48/2.97    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 19.48/2.97    inference(cnf_transformation,[],[f27])).
% 19.48/2.97  
% 19.48/2.97  fof(f73,plain,(
% 19.48/2.97    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0 | r2_hidden(X1,X0)) )),
% 19.48/2.97    inference(definition_unfolding,[],[f53,f42,f58])).
% 19.48/2.97  
% 19.48/2.97  fof(f1,axiom,(
% 19.48/2.97    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 19.48/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.48/2.97  
% 19.48/2.97  fof(f19,plain,(
% 19.48/2.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.48/2.97    inference(nnf_transformation,[],[f1])).
% 19.48/2.97  
% 19.48/2.97  fof(f20,plain,(
% 19.48/2.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.48/2.97    inference(flattening,[],[f19])).
% 19.48/2.97  
% 19.48/2.97  fof(f21,plain,(
% 19.48/2.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.48/2.97    inference(rectify,[],[f20])).
% 19.48/2.97  
% 19.48/2.97  fof(f22,plain,(
% 19.48/2.97    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 19.48/2.97    introduced(choice_axiom,[])).
% 19.48/2.97  
% 19.48/2.97  fof(f23,plain,(
% 19.48/2.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.48/2.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 19.48/2.97  
% 19.48/2.97  fof(f31,plain,(
% 19.48/2.97    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 19.48/2.97    inference(cnf_transformation,[],[f23])).
% 19.48/2.97  
% 19.48/2.97  fof(f66,plain,(
% 19.48/2.97    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 19.48/2.97    inference(definition_unfolding,[],[f31,f42])).
% 19.48/2.97  
% 19.48/2.97  fof(f78,plain,(
% 19.48/2.97    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 19.48/2.97    inference(equality_resolution,[],[f66])).
% 19.48/2.97  
% 19.48/2.97  fof(f40,plain,(
% 19.48/2.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 19.48/2.97    inference(cnf_transformation,[],[f26])).
% 19.48/2.97  
% 19.48/2.97  fof(f69,plain,(
% 19.48/2.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0) )),
% 19.48/2.97    inference(definition_unfolding,[],[f40,f42])).
% 19.48/2.97  
% 19.48/2.97  fof(f3,axiom,(
% 19.48/2.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.48/2.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.48/2.97  
% 19.48/2.97  fof(f24,plain,(
% 19.48/2.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.48/2.97    inference(nnf_transformation,[],[f3])).
% 19.48/2.97  
% 19.48/2.97  fof(f25,plain,(
% 19.48/2.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.48/2.97    inference(flattening,[],[f24])).
% 19.48/2.97  
% 19.48/2.97  fof(f39,plain,(
% 19.48/2.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.48/2.97    inference(cnf_transformation,[],[f25])).
% 19.48/2.97  
% 19.48/2.97  fof(f56,plain,(
% 19.48/2.97    k1_tarski(sK2) != sK1),
% 19.48/2.97    inference(cnf_transformation,[],[f29])).
% 19.48/2.97  
% 19.48/2.97  fof(f75,plain,(
% 19.48/2.97    k2_enumset1(sK2,sK2,sK2,sK2) != sK1),
% 19.48/2.97    inference(definition_unfolding,[],[f56,f58])).
% 19.48/2.97  
% 19.48/2.97  fof(f55,plain,(
% 19.48/2.97    k1_xboole_0 != sK1),
% 19.48/2.97    inference(cnf_transformation,[],[f29])).
% 19.48/2.97  
% 19.48/2.97  cnf(c_22,negated_conjecture,
% 19.48/2.97      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
% 19.48/2.97      inference(cnf_transformation,[],[f76]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_1,plain,
% 19.48/2.97      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,X1) ),
% 19.48/2.97      inference(cnf_transformation,[],[f60]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_1160,plain,
% 19.48/2.97      ( k2_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),k1_xboole_0) = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
% 19.48/2.97      inference(superposition,[status(thm)],[c_22,c_1]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_17,plain,
% 19.48/2.97      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 19.48/2.97      inference(cnf_transformation,[],[f72]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_0,plain,
% 19.48/2.97      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
% 19.48/2.97      inference(cnf_transformation,[],[f59]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_1054,plain,
% 19.48/2.97      ( k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
% 19.48/2.97      inference(superposition,[status(thm)],[c_17,c_0]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_16,plain,
% 19.48/2.97      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 19.48/2.97      inference(cnf_transformation,[],[f71]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_14,plain,
% 19.48/2.97      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.48/2.97      inference(cnf_transformation,[],[f43]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_702,plain,
% 19.48/2.97      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.48/2.97      inference(light_normalisation,[status(thm)],[c_16,c_14]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_1059,plain,
% 19.48/2.97      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.48/2.97      inference(light_normalisation,[status(thm)],[c_1054,c_702]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_1728,plain,
% 19.48/2.97      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)) = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
% 19.48/2.97      inference(superposition,[status(thm)],[c_1160,c_1059]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_15,plain,
% 19.48/2.97      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 19.48/2.97      inference(cnf_transformation,[],[f70]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_691,plain,
% 19.48/2.97      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 19.48/2.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_2024,plain,
% 19.48/2.97      ( r1_tarski(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 19.48/2.97      inference(superposition,[status(thm)],[c_1728,c_691]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_12,plain,
% 19.48/2.97      ( ~ r1_tarski(X0,X1)
% 19.48/2.97      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 19.48/2.97      inference(cnf_transformation,[],[f68]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_693,plain,
% 19.48/2.97      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 19.48/2.97      | r1_tarski(X0,X1) != iProver_top ),
% 19.48/2.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_2042,plain,
% 19.48/2.97      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k3_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k2_enumset1(sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
% 19.48/2.97      inference(superposition,[status(thm)],[c_2024,c_693]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_2,plain,
% 19.48/2.97      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 19.48/2.97      inference(cnf_transformation,[],[f61]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_2127,plain,
% 19.48/2.97      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k3_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k1_xboole_0)) = k3_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 19.48/2.97      inference(superposition,[status(thm)],[c_2042,c_2]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_2130,plain,
% 19.48/2.97      ( k3_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k2_enumset1(sK2,sK2,sK2,sK2)) = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
% 19.48/2.97      inference(demodulation,[status(thm)],[c_2127,c_14,c_702]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_18,plain,
% 19.48/2.97      ( r2_hidden(X0,X1)
% 19.48/2.97      | k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) = X1 ),
% 19.48/2.97      inference(cnf_transformation,[],[f73]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_690,plain,
% 19.48/2.97      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0
% 19.48/2.97      | r2_hidden(X1,X0) = iProver_top ),
% 19.48/2.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_7,plain,
% 19.48/2.97      ( ~ r2_hidden(X0,X1)
% 19.48/2.97      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 19.48/2.97      inference(cnf_transformation,[],[f78]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_697,plain,
% 19.48/2.97      ( r2_hidden(X0,X1) != iProver_top
% 19.48/2.97      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 19.48/2.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_2903,plain,
% 19.48/2.97      ( r2_hidden(X0,k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)) != iProver_top
% 19.48/2.97      | r2_hidden(X0,sK1) != iProver_top ),
% 19.48/2.97      inference(superposition,[status(thm)],[c_1728,c_697]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_3375,plain,
% 19.48/2.97      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k3_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k2_enumset1(X0,X0,X0,X0))) = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
% 19.48/2.97      | r2_hidden(X0,sK1) != iProver_top ),
% 19.48/2.97      inference(superposition,[status(thm)],[c_690,c_2903]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_3435,plain,
% 19.48/2.97      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k3_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k2_enumset1(X0,X0,X0,X0))) = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
% 19.48/2.97      | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(X0,X0,X0,X0))) = sK1 ),
% 19.48/2.97      inference(superposition,[status(thm)],[c_690,c_3375]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_45497,plain,
% 19.48/2.97      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)) = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
% 19.48/2.97      | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = sK1 ),
% 19.48/2.97      inference(superposition,[status(thm)],[c_2130,c_3435]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_1136,plain,
% 19.48/2.97      ( k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) ),
% 19.48/2.97      inference(superposition,[status(thm)],[c_22,c_2]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_1144,plain,
% 19.48/2.97      ( k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = sK1 ),
% 19.48/2.97      inference(demodulation,[status(thm)],[c_1136,c_14,c_702]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_45655,plain,
% 19.48/2.97      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)) = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
% 19.48/2.97      | k5_xboole_0(sK1,sK1) = sK1 ),
% 19.48/2.97      inference(light_normalisation,[status(thm)],[c_45497,c_1144]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_1137,plain,
% 19.48/2.97      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
% 19.48/2.97      inference(superposition,[status(thm)],[c_14,c_2]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_1143,plain,
% 19.48/2.97      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 19.48/2.97      inference(light_normalisation,[status(thm)],[c_1137,c_14,c_702]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_1907,plain,
% 19.48/2.97      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
% 19.48/2.97      inference(superposition,[status(thm)],[c_1143,c_2]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_1910,plain,
% 19.48/2.97      ( k3_xboole_0(X0,X0) = X0 ),
% 19.48/2.97      inference(light_normalisation,[status(thm)],[c_1907,c_14,c_702]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_1911,plain,
% 19.48/2.97      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.48/2.97      inference(demodulation,[status(thm)],[c_1910,c_1143]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_45656,plain,
% 19.48/2.97      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1) = k1_xboole_0
% 19.48/2.97      | sK1 = k1_xboole_0 ),
% 19.48/2.97      inference(demodulation,[status(thm)],[c_45655,c_1911]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_13,plain,
% 19.48/2.97      ( r1_tarski(X0,X1)
% 19.48/2.97      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 19.48/2.97      inference(cnf_transformation,[],[f69]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_692,plain,
% 19.48/2.97      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 19.48/2.97      | r1_tarski(X0,X1) = iProver_top ),
% 19.48/2.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_2023,plain,
% 19.48/2.97      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1) != k1_xboole_0
% 19.48/2.97      | r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) = iProver_top ),
% 19.48/2.97      inference(superposition,[status(thm)],[c_1728,c_692]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_828,plain,
% 19.48/2.97      ( r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
% 19.48/2.97      | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_xboole_0 ),
% 19.48/2.97      inference(instantiation,[status(thm)],[c_13]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_767,plain,
% 19.48/2.97      ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
% 19.48/2.97      | k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)) = k1_xboole_0 ),
% 19.48/2.97      inference(instantiation,[status(thm)],[c_12]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_768,plain,
% 19.48/2.97      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)) = k1_xboole_0
% 19.48/2.97      | r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) != iProver_top ),
% 19.48/2.97      inference(predicate_to_equality,[status(thm)],[c_767]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_727,plain,
% 19.48/2.97      ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
% 19.48/2.97      | k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)) != k1_xboole_0 ),
% 19.48/2.97      inference(instantiation,[status(thm)],[c_13]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_350,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_725,plain,
% 19.48/2.97      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 19.48/2.97      inference(instantiation,[status(thm)],[c_350]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_726,plain,
% 19.48/2.97      ( sK1 != k1_xboole_0
% 19.48/2.97      | k1_xboole_0 = sK1
% 19.48/2.97      | k1_xboole_0 != k1_xboole_0 ),
% 19.48/2.97      inference(instantiation,[status(thm)],[c_725]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_9,plain,
% 19.48/2.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 19.48/2.97      inference(cnf_transformation,[],[f39]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_717,plain,
% 19.48/2.97      ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
% 19.48/2.97      | ~ r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
% 19.48/2.97      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1 ),
% 19.48/2.97      inference(instantiation,[status(thm)],[c_9]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_43,plain,
% 19.48/2.97      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 19.48/2.97      | k1_xboole_0 = k1_xboole_0 ),
% 19.48/2.97      inference(instantiation,[status(thm)],[c_9]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_35,plain,
% 19.48/2.97      ( r1_tarski(k1_xboole_0,k1_xboole_0)
% 19.48/2.97      | k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
% 19.48/2.97      inference(instantiation,[status(thm)],[c_13]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_29,plain,
% 19.48/2.97      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 19.48/2.97      inference(instantiation,[status(thm)],[c_17]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_20,negated_conjecture,
% 19.48/2.97      ( k2_enumset1(sK2,sK2,sK2,sK2) != sK1 ),
% 19.48/2.97      inference(cnf_transformation,[],[f75]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(c_21,negated_conjecture,
% 19.48/2.97      ( k1_xboole_0 != sK1 ),
% 19.48/2.97      inference(cnf_transformation,[],[f55]) ).
% 19.48/2.97  
% 19.48/2.97  cnf(contradiction,plain,
% 19.48/2.97      ( $false ),
% 19.48/2.97      inference(minisat,
% 19.48/2.97                [status(thm)],
% 19.48/2.97                [c_45656,c_2023,c_828,c_768,c_727,c_726,c_717,c_43,c_35,
% 19.48/2.97                 c_29,c_20,c_21,c_22]) ).
% 19.48/2.97  
% 19.48/2.97  
% 19.48/2.97  % SZS output end CNFRefutation for theBenchmark.p
% 19.48/2.97  
% 19.48/2.97  ------                               Statistics
% 19.48/2.97  
% 19.48/2.97  ------ General
% 19.48/2.97  
% 19.48/2.97  abstr_ref_over_cycles:                  0
% 19.48/2.97  abstr_ref_under_cycles:                 0
% 19.48/2.97  gc_basic_clause_elim:                   0
% 19.48/2.97  forced_gc_time:                         0
% 19.48/2.97  parsing_time:                           0.009
% 19.48/2.97  unif_index_cands_time:                  0.
% 19.48/2.97  unif_index_add_time:                    0.
% 19.48/2.97  orderings_time:                         0.
% 19.48/2.97  out_proof_time:                         0.011
% 19.48/2.97  total_time:                             2.071
% 19.48/2.97  num_of_symbols:                         41
% 19.48/2.97  num_of_terms:                           52432
% 19.48/2.97  
% 19.48/2.97  ------ Preprocessing
% 19.48/2.97  
% 19.48/2.97  num_of_splits:                          0
% 19.48/2.97  num_of_split_atoms:                     0
% 19.48/2.97  num_of_reused_defs:                     0
% 19.48/2.97  num_eq_ax_congr_red:                    12
% 19.48/2.97  num_of_sem_filtered_clauses:            1
% 19.48/2.97  num_of_subtypes:                        0
% 19.48/2.97  monotx_restored_types:                  0
% 19.48/2.97  sat_num_of_epr_types:                   0
% 19.48/2.97  sat_num_of_non_cyclic_types:            0
% 19.48/2.97  sat_guarded_non_collapsed_types:        0
% 19.48/2.97  num_pure_diseq_elim:                    0
% 19.48/2.97  simp_replaced_by:                       0
% 19.48/2.97  res_preprocessed:                       105
% 19.48/2.97  prep_upred:                             0
% 19.48/2.97  prep_unflattend:                        0
% 19.48/2.97  smt_new_axioms:                         0
% 19.48/2.97  pred_elim_cands:                        2
% 19.48/2.97  pred_elim:                              0
% 19.48/2.97  pred_elim_cl:                           0
% 19.48/2.97  pred_elim_cycles:                       2
% 19.48/2.97  merged_defs:                            16
% 19.48/2.97  merged_defs_ncl:                        0
% 19.48/2.97  bin_hyper_res:                          16
% 19.48/2.97  prep_cycles:                            4
% 19.48/2.97  pred_elim_time:                         0.
% 19.48/2.97  splitting_time:                         0.
% 19.48/2.97  sem_filter_time:                        0.
% 19.48/2.97  monotx_time:                            0.001
% 19.48/2.97  subtype_inf_time:                       0.
% 19.48/2.97  
% 19.48/2.97  ------ Problem properties
% 19.48/2.97  
% 19.48/2.97  clauses:                                22
% 19.48/2.97  conjectures:                            3
% 19.48/2.97  epr:                                    3
% 19.48/2.97  horn:                                   17
% 19.48/2.97  ground:                                 3
% 19.48/2.97  unary:                                  11
% 19.48/2.97  binary:                                 6
% 19.48/2.97  lits:                                   39
% 19.48/2.97  lits_eq:                                17
% 19.48/2.97  fd_pure:                                0
% 19.48/2.97  fd_pseudo:                              0
% 19.48/2.97  fd_cond:                                0
% 19.48/2.97  fd_pseudo_cond:                         4
% 19.48/2.97  ac_symbols:                             0
% 19.48/2.97  
% 19.48/2.97  ------ Propositional Solver
% 19.48/2.97  
% 19.48/2.97  prop_solver_calls:                      35
% 19.48/2.97  prop_fast_solver_calls:                 1118
% 19.48/2.97  smt_solver_calls:                       0
% 19.48/2.97  smt_fast_solver_calls:                  0
% 19.48/2.97  prop_num_of_clauses:                    14436
% 19.48/2.97  prop_preprocess_simplified:             27526
% 19.48/2.97  prop_fo_subsumed:                       24
% 19.48/2.97  prop_solver_time:                       0.
% 19.48/2.97  smt_solver_time:                        0.
% 19.48/2.97  smt_fast_solver_time:                   0.
% 19.48/2.97  prop_fast_solver_time:                  0.
% 19.48/2.97  prop_unsat_core_time:                   0.001
% 19.48/2.97  
% 19.48/2.97  ------ QBF
% 19.48/2.97  
% 19.48/2.97  qbf_q_res:                              0
% 19.48/2.97  qbf_num_tautologies:                    0
% 19.48/2.97  qbf_prep_cycles:                        0
% 19.48/2.97  
% 19.48/2.97  ------ BMC1
% 19.48/2.97  
% 19.48/2.97  bmc1_current_bound:                     -1
% 19.48/2.97  bmc1_last_solved_bound:                 -1
% 19.48/2.97  bmc1_unsat_core_size:                   -1
% 19.48/2.97  bmc1_unsat_core_parents_size:           -1
% 19.48/2.97  bmc1_merge_next_fun:                    0
% 19.48/2.97  bmc1_unsat_core_clauses_time:           0.
% 19.48/2.97  
% 19.48/2.97  ------ Instantiation
% 19.48/2.97  
% 19.48/2.97  inst_num_of_clauses:                    3613
% 19.48/2.97  inst_num_in_passive:                    1837
% 19.48/2.97  inst_num_in_active:                     1401
% 19.48/2.97  inst_num_in_unprocessed:                376
% 19.48/2.97  inst_num_of_loops:                      1820
% 19.48/2.97  inst_num_of_learning_restarts:          0
% 19.48/2.97  inst_num_moves_active_passive:          415
% 19.48/2.97  inst_lit_activity:                      0
% 19.48/2.97  inst_lit_activity_moves:                0
% 19.48/2.97  inst_num_tautologies:                   0
% 19.48/2.97  inst_num_prop_implied:                  0
% 19.48/2.97  inst_num_existing_simplified:           0
% 19.48/2.97  inst_num_eq_res_simplified:             0
% 19.48/2.97  inst_num_child_elim:                    0
% 19.48/2.97  inst_num_of_dismatching_blockings:      4970
% 19.48/2.97  inst_num_of_non_proper_insts:           5774
% 19.48/2.97  inst_num_of_duplicates:                 0
% 19.48/2.97  inst_inst_num_from_inst_to_res:         0
% 19.48/2.97  inst_dismatching_checking_time:         0.
% 19.48/2.97  
% 19.48/2.97  ------ Resolution
% 19.48/2.97  
% 19.48/2.97  res_num_of_clauses:                     0
% 19.48/2.97  res_num_in_passive:                     0
% 19.48/2.97  res_num_in_active:                      0
% 19.48/2.97  res_num_of_loops:                       109
% 19.48/2.97  res_forward_subset_subsumed:            909
% 19.48/2.97  res_backward_subset_subsumed:           6
% 19.48/2.97  res_forward_subsumed:                   0
% 19.48/2.97  res_backward_subsumed:                  0
% 19.48/2.97  res_forward_subsumption_resolution:     0
% 19.48/2.97  res_backward_subsumption_resolution:    0
% 19.48/2.97  res_clause_to_clause_subsumption:       12918
% 19.48/2.97  res_orphan_elimination:                 0
% 19.48/2.97  res_tautology_del:                      599
% 19.48/2.97  res_num_eq_res_simplified:              0
% 19.48/2.97  res_num_sel_changes:                    0
% 19.48/2.97  res_moves_from_active_to_pass:          0
% 19.48/2.97  
% 19.48/2.97  ------ Superposition
% 19.48/2.97  
% 19.48/2.97  sup_time_total:                         0.
% 19.48/2.97  sup_time_generating:                    0.
% 19.48/2.97  sup_time_sim_full:                      0.
% 19.48/2.97  sup_time_sim_immed:                     0.
% 19.48/2.97  
% 19.48/2.97  sup_num_of_clauses:                     1849
% 19.48/2.97  sup_num_in_active:                      311
% 19.48/2.97  sup_num_in_passive:                     1538
% 19.48/2.97  sup_num_of_loops:                       363
% 19.48/2.97  sup_fw_superposition:                   4745
% 19.48/2.97  sup_bw_superposition:                   2893
% 19.48/2.97  sup_immediate_simplified:               3960
% 19.48/2.97  sup_given_eliminated:                   29
% 19.48/2.97  comparisons_done:                       0
% 19.48/2.97  comparisons_avoided:                    65
% 19.48/2.97  
% 19.48/2.97  ------ Simplifications
% 19.48/2.97  
% 19.48/2.97  
% 19.48/2.97  sim_fw_subset_subsumed:                 269
% 19.48/2.97  sim_bw_subset_subsumed:                 26
% 19.48/2.97  sim_fw_subsumed:                        872
% 19.48/2.97  sim_bw_subsumed:                        31
% 19.48/2.97  sim_fw_subsumption_res:                 0
% 19.48/2.97  sim_bw_subsumption_res:                 0
% 19.48/2.97  sim_tautology_del:                      147
% 19.48/2.97  sim_eq_tautology_del:                   1451
% 19.48/2.97  sim_eq_res_simp:                        33
% 19.48/2.97  sim_fw_demodulated:                     3192
% 19.48/2.97  sim_bw_demodulated:                     68
% 19.48/2.97  sim_light_normalised:                   1636
% 19.48/2.97  sim_joinable_taut:                      0
% 19.48/2.97  sim_joinable_simp:                      0
% 19.48/2.97  sim_ac_normalised:                      0
% 19.48/2.97  sim_smt_subsumption:                    0
% 19.48/2.97  
%------------------------------------------------------------------------------
