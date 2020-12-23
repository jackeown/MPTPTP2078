%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:17 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 474 expanded)
%              Number of clauses        :   40 (  84 expanded)
%              Number of leaves         :   13 ( 135 expanded)
%              Depth                    :   16
%              Number of atoms          :  242 (1047 expanded)
%              Number of equality atoms :  181 ( 835 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X1
        & r2_hidden(X1,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X1
          & r2_hidden(X1,X2)
          & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r2_hidden(X1,X2)
      & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & r2_hidden(X1,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) )
   => ( sK1 != sK2
      & r2_hidden(sK2,sK3)
      & k3_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( sK1 != sK2
    & r2_hidden(sK2,sK3)
    & k3_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f21])).

fof(f40,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f43])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) = k3_enumset1(X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f44,f44])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f39,plain,(
    k3_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f39,f43,f44])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
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
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f28,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f56,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f49])).

fof(f57,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f56])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) != k3_enumset1(X1,X1,X1,X1,X1) ) ),
    inference(definition_unfolding,[],[f37,f44,f44])).

fof(f25,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f25,f42])).

fof(f62,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f26,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f26,f42])).

fof(f60,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f51])).

fof(f61,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f60])).

fof(f41,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_805,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_806,plain,
    ( k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k3_enumset1(X1,X1,X1,X1,X1)
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2366,plain,
    ( k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_805,c_806])).

cnf(c_1,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_2405,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),X0)) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),X0) ),
    inference(superposition,[status(thm)],[c_2366,c_1])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_829,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_14,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_545,negated_conjecture,
    ( k3_xboole_0(sK3,k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_14,c_1,c_0])).

cnf(c_1231,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),X0)) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0) ),
    inference(superposition,[status(thm)],[c_545,c_1])).

cnf(c_1552,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,k3_enumset1(sK1,sK1,sK1,sK1,sK2)))) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_829,c_1231])).

cnf(c_3165,plain,
    ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(sK3,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_2405,c_1552])).

cnf(c_3170,plain,
    ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_3165,c_2405])).

cnf(c_828,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_1462,plain,
    ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_xboole_0(sK3,X0)) = k3_xboole_0(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_545,c_828])).

cnf(c_1650,plain,
    ( k3_xboole_0(k3_xboole_0(sK3,X0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k3_xboole_0(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_1462,c_0])).

cnf(c_2412,plain,
    ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_2366,c_1650])).

cnf(c_2413,plain,
    ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_2366,c_1462])).

cnf(c_6,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_811,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2363,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X2,X2,X2,X2,X2)) = k3_enumset1(X2,X2,X2,X2,X2) ),
    inference(superposition,[status(thm)],[c_811,c_806])).

cnf(c_2414,plain,
    ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_2413,c_2363])).

cnf(c_2415,plain,
    ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_2412,c_2414])).

cnf(c_3171,plain,
    ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3170,c_2366,c_2415])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) != k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_870,plain,
    ( r2_hidden(sK2,k3_enumset1(X0,X0,X0,X1,X2))
    | k3_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_872,plain,
    ( r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_870])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_837,plain,
    ( ~ r2_hidden(sK2,k3_enumset1(X0,X0,X0,X1,X2))
    | sK2 = X0
    | sK2 = X1
    | sK2 = X2 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_839,plain,
    ( ~ r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | sK2 = sK1 ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_548,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_835,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_836,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_8,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,plain,
    ( r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_23,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_12,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3171,c_872,c_839,c_836,c_26,c_23,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.38/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.00  
% 3.38/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.38/1.00  
% 3.38/1.00  ------  iProver source info
% 3.38/1.00  
% 3.38/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.38/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.38/1.00  git: non_committed_changes: false
% 3.38/1.00  git: last_make_outside_of_git: false
% 3.38/1.00  
% 3.38/1.00  ------ 
% 3.38/1.00  
% 3.38/1.00  ------ Input Options
% 3.38/1.00  
% 3.38/1.00  --out_options                           all
% 3.38/1.00  --tptp_safe_out                         true
% 3.38/1.00  --problem_path                          ""
% 3.38/1.00  --include_path                          ""
% 3.38/1.00  --clausifier                            res/vclausify_rel
% 3.38/1.00  --clausifier_options                    ""
% 3.38/1.00  --stdin                                 false
% 3.38/1.00  --stats_out                             all
% 3.38/1.00  
% 3.38/1.00  ------ General Options
% 3.38/1.00  
% 3.38/1.00  --fof                                   false
% 3.38/1.00  --time_out_real                         305.
% 3.38/1.00  --time_out_virtual                      -1.
% 3.38/1.00  --symbol_type_check                     false
% 3.38/1.00  --clausify_out                          false
% 3.38/1.00  --sig_cnt_out                           false
% 3.38/1.00  --trig_cnt_out                          false
% 3.38/1.00  --trig_cnt_out_tolerance                1.
% 3.38/1.00  --trig_cnt_out_sk_spl                   false
% 3.38/1.00  --abstr_cl_out                          false
% 3.38/1.00  
% 3.38/1.00  ------ Global Options
% 3.38/1.00  
% 3.38/1.00  --schedule                              default
% 3.38/1.00  --add_important_lit                     false
% 3.38/1.00  --prop_solver_per_cl                    1000
% 3.38/1.00  --min_unsat_core                        false
% 3.38/1.00  --soft_assumptions                      false
% 3.38/1.00  --soft_lemma_size                       3
% 3.38/1.00  --prop_impl_unit_size                   0
% 3.38/1.00  --prop_impl_unit                        []
% 3.38/1.00  --share_sel_clauses                     true
% 3.38/1.00  --reset_solvers                         false
% 3.38/1.00  --bc_imp_inh                            [conj_cone]
% 3.38/1.00  --conj_cone_tolerance                   3.
% 3.38/1.00  --extra_neg_conj                        none
% 3.38/1.00  --large_theory_mode                     true
% 3.38/1.00  --prolific_symb_bound                   200
% 3.38/1.00  --lt_threshold                          2000
% 3.38/1.00  --clause_weak_htbl                      true
% 3.38/1.00  --gc_record_bc_elim                     false
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing Options
% 3.38/1.00  
% 3.38/1.00  --preprocessing_flag                    true
% 3.38/1.00  --time_out_prep_mult                    0.1
% 3.38/1.00  --splitting_mode                        input
% 3.38/1.00  --splitting_grd                         true
% 3.38/1.00  --splitting_cvd                         false
% 3.38/1.00  --splitting_cvd_svl                     false
% 3.38/1.00  --splitting_nvd                         32
% 3.38/1.00  --sub_typing                            true
% 3.38/1.00  --prep_gs_sim                           true
% 3.38/1.00  --prep_unflatten                        true
% 3.38/1.00  --prep_res_sim                          true
% 3.38/1.00  --prep_upred                            true
% 3.38/1.00  --prep_sem_filter                       exhaustive
% 3.38/1.00  --prep_sem_filter_out                   false
% 3.38/1.00  --pred_elim                             true
% 3.38/1.00  --res_sim_input                         true
% 3.38/1.00  --eq_ax_congr_red                       true
% 3.38/1.00  --pure_diseq_elim                       true
% 3.38/1.00  --brand_transform                       false
% 3.38/1.00  --non_eq_to_eq                          false
% 3.38/1.00  --prep_def_merge                        true
% 3.38/1.00  --prep_def_merge_prop_impl              false
% 3.38/1.00  --prep_def_merge_mbd                    true
% 3.38/1.00  --prep_def_merge_tr_red                 false
% 3.38/1.00  --prep_def_merge_tr_cl                  false
% 3.38/1.00  --smt_preprocessing                     true
% 3.38/1.00  --smt_ac_axioms                         fast
% 3.38/1.00  --preprocessed_out                      false
% 3.38/1.00  --preprocessed_stats                    false
% 3.38/1.00  
% 3.38/1.00  ------ Abstraction refinement Options
% 3.38/1.00  
% 3.38/1.00  --abstr_ref                             []
% 3.38/1.00  --abstr_ref_prep                        false
% 3.38/1.00  --abstr_ref_until_sat                   false
% 3.38/1.00  --abstr_ref_sig_restrict                funpre
% 3.38/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.38/1.00  --abstr_ref_under                       []
% 3.38/1.00  
% 3.38/1.00  ------ SAT Options
% 3.38/1.00  
% 3.38/1.00  --sat_mode                              false
% 3.38/1.00  --sat_fm_restart_options                ""
% 3.38/1.00  --sat_gr_def                            false
% 3.38/1.00  --sat_epr_types                         true
% 3.38/1.00  --sat_non_cyclic_types                  false
% 3.38/1.00  --sat_finite_models                     false
% 3.38/1.00  --sat_fm_lemmas                         false
% 3.38/1.00  --sat_fm_prep                           false
% 3.38/1.00  --sat_fm_uc_incr                        true
% 3.38/1.00  --sat_out_model                         small
% 3.38/1.00  --sat_out_clauses                       false
% 3.38/1.00  
% 3.38/1.00  ------ QBF Options
% 3.38/1.00  
% 3.38/1.00  --qbf_mode                              false
% 3.38/1.00  --qbf_elim_univ                         false
% 3.38/1.00  --qbf_dom_inst                          none
% 3.38/1.00  --qbf_dom_pre_inst                      false
% 3.38/1.00  --qbf_sk_in                             false
% 3.38/1.00  --qbf_pred_elim                         true
% 3.38/1.00  --qbf_split                             512
% 3.38/1.00  
% 3.38/1.00  ------ BMC1 Options
% 3.38/1.00  
% 3.38/1.00  --bmc1_incremental                      false
% 3.38/1.00  --bmc1_axioms                           reachable_all
% 3.38/1.00  --bmc1_min_bound                        0
% 3.38/1.00  --bmc1_max_bound                        -1
% 3.38/1.00  --bmc1_max_bound_default                -1
% 3.38/1.00  --bmc1_symbol_reachability              true
% 3.38/1.00  --bmc1_property_lemmas                  false
% 3.38/1.00  --bmc1_k_induction                      false
% 3.38/1.00  --bmc1_non_equiv_states                 false
% 3.38/1.00  --bmc1_deadlock                         false
% 3.38/1.00  --bmc1_ucm                              false
% 3.38/1.00  --bmc1_add_unsat_core                   none
% 3.38/1.00  --bmc1_unsat_core_children              false
% 3.38/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.38/1.00  --bmc1_out_stat                         full
% 3.38/1.00  --bmc1_ground_init                      false
% 3.38/1.00  --bmc1_pre_inst_next_state              false
% 3.38/1.00  --bmc1_pre_inst_state                   false
% 3.38/1.00  --bmc1_pre_inst_reach_state             false
% 3.38/1.00  --bmc1_out_unsat_core                   false
% 3.38/1.00  --bmc1_aig_witness_out                  false
% 3.38/1.00  --bmc1_verbose                          false
% 3.38/1.00  --bmc1_dump_clauses_tptp                false
% 3.38/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.38/1.00  --bmc1_dump_file                        -
% 3.38/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.38/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.38/1.00  --bmc1_ucm_extend_mode                  1
% 3.38/1.00  --bmc1_ucm_init_mode                    2
% 3.38/1.00  --bmc1_ucm_cone_mode                    none
% 3.38/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.38/1.00  --bmc1_ucm_relax_model                  4
% 3.38/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.38/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.38/1.00  --bmc1_ucm_layered_model                none
% 3.38/1.00  --bmc1_ucm_max_lemma_size               10
% 3.38/1.00  
% 3.38/1.00  ------ AIG Options
% 3.38/1.00  
% 3.38/1.00  --aig_mode                              false
% 3.38/1.00  
% 3.38/1.00  ------ Instantiation Options
% 3.38/1.00  
% 3.38/1.00  --instantiation_flag                    true
% 3.38/1.00  --inst_sos_flag                         true
% 3.38/1.00  --inst_sos_phase                        true
% 3.38/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.38/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.38/1.00  --inst_lit_sel_side                     num_symb
% 3.38/1.00  --inst_solver_per_active                1400
% 3.38/1.00  --inst_solver_calls_frac                1.
% 3.38/1.00  --inst_passive_queue_type               priority_queues
% 3.38/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.38/1.00  --inst_passive_queues_freq              [25;2]
% 3.38/1.00  --inst_dismatching                      true
% 3.38/1.00  --inst_eager_unprocessed_to_passive     true
% 3.38/1.00  --inst_prop_sim_given                   true
% 3.38/1.00  --inst_prop_sim_new                     false
% 3.38/1.00  --inst_subs_new                         false
% 3.38/1.00  --inst_eq_res_simp                      false
% 3.38/1.00  --inst_subs_given                       false
% 3.38/1.00  --inst_orphan_elimination               true
% 3.38/1.00  --inst_learning_loop_flag               true
% 3.38/1.00  --inst_learning_start                   3000
% 3.38/1.00  --inst_learning_factor                  2
% 3.38/1.00  --inst_start_prop_sim_after_learn       3
% 3.38/1.00  --inst_sel_renew                        solver
% 3.38/1.00  --inst_lit_activity_flag                true
% 3.38/1.00  --inst_restr_to_given                   false
% 3.38/1.00  --inst_activity_threshold               500
% 3.38/1.00  --inst_out_proof                        true
% 3.38/1.00  
% 3.38/1.00  ------ Resolution Options
% 3.38/1.00  
% 3.38/1.00  --resolution_flag                       true
% 3.38/1.00  --res_lit_sel                           adaptive
% 3.38/1.00  --res_lit_sel_side                      none
% 3.38/1.00  --res_ordering                          kbo
% 3.38/1.00  --res_to_prop_solver                    active
% 3.38/1.00  --res_prop_simpl_new                    false
% 3.38/1.00  --res_prop_simpl_given                  true
% 3.38/1.00  --res_passive_queue_type                priority_queues
% 3.38/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.38/1.00  --res_passive_queues_freq               [15;5]
% 3.38/1.00  --res_forward_subs                      full
% 3.38/1.00  --res_backward_subs                     full
% 3.38/1.00  --res_forward_subs_resolution           true
% 3.38/1.00  --res_backward_subs_resolution          true
% 3.38/1.00  --res_orphan_elimination                true
% 3.38/1.00  --res_time_limit                        2.
% 3.38/1.00  --res_out_proof                         true
% 3.38/1.00  
% 3.38/1.00  ------ Superposition Options
% 3.38/1.00  
% 3.38/1.00  --superposition_flag                    true
% 3.38/1.00  --sup_passive_queue_type                priority_queues
% 3.38/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.38/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.38/1.00  --demod_completeness_check              fast
% 3.38/1.00  --demod_use_ground                      true
% 3.38/1.00  --sup_to_prop_solver                    passive
% 3.38/1.00  --sup_prop_simpl_new                    true
% 3.38/1.00  --sup_prop_simpl_given                  true
% 3.38/1.00  --sup_fun_splitting                     true
% 3.38/1.00  --sup_smt_interval                      50000
% 3.38/1.00  
% 3.38/1.00  ------ Superposition Simplification Setup
% 3.38/1.00  
% 3.38/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.38/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.38/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.38/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.38/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.38/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.38/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.38/1.00  --sup_immed_triv                        [TrivRules]
% 3.38/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/1.00  --sup_immed_bw_main                     []
% 3.38/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.38/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.38/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/1.00  --sup_input_bw                          []
% 3.38/1.00  
% 3.38/1.00  ------ Combination Options
% 3.38/1.00  
% 3.38/1.00  --comb_res_mult                         3
% 3.38/1.00  --comb_sup_mult                         2
% 3.38/1.00  --comb_inst_mult                        10
% 3.38/1.00  
% 3.38/1.00  ------ Debug Options
% 3.38/1.00  
% 3.38/1.00  --dbg_backtrace                         false
% 3.38/1.00  --dbg_dump_prop_clauses                 false
% 3.38/1.00  --dbg_dump_prop_clauses_file            -
% 3.38/1.00  --dbg_out_stat                          false
% 3.38/1.00  ------ Parsing...
% 3.38/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.38/1.00  ------ Proving...
% 3.38/1.00  ------ Problem Properties 
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  clauses                                 15
% 3.38/1.00  conjectures                             3
% 3.38/1.00  EPR                                     2
% 3.38/1.00  Horn                                    13
% 3.38/1.00  unary                                   8
% 3.38/1.00  binary                                  2
% 3.38/1.00  lits                                    30
% 3.38/1.00  lits eq                                 19
% 3.38/1.00  fd_pure                                 0
% 3.38/1.00  fd_pseudo                               0
% 3.38/1.00  fd_cond                                 0
% 3.38/1.00  fd_pseudo_cond                          4
% 3.38/1.00  AC symbols                              1
% 3.38/1.00  
% 3.38/1.00  ------ Schedule dynamic 5 is on 
% 3.38/1.00  
% 3.38/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  ------ 
% 3.38/1.00  Current options:
% 3.38/1.00  ------ 
% 3.38/1.00  
% 3.38/1.00  ------ Input Options
% 3.38/1.00  
% 3.38/1.00  --out_options                           all
% 3.38/1.00  --tptp_safe_out                         true
% 3.38/1.00  --problem_path                          ""
% 3.38/1.00  --include_path                          ""
% 3.38/1.00  --clausifier                            res/vclausify_rel
% 3.38/1.00  --clausifier_options                    ""
% 3.38/1.00  --stdin                                 false
% 3.38/1.00  --stats_out                             all
% 3.38/1.00  
% 3.38/1.00  ------ General Options
% 3.38/1.00  
% 3.38/1.00  --fof                                   false
% 3.38/1.00  --time_out_real                         305.
% 3.38/1.00  --time_out_virtual                      -1.
% 3.38/1.00  --symbol_type_check                     false
% 3.38/1.00  --clausify_out                          false
% 3.38/1.00  --sig_cnt_out                           false
% 3.38/1.00  --trig_cnt_out                          false
% 3.38/1.00  --trig_cnt_out_tolerance                1.
% 3.38/1.00  --trig_cnt_out_sk_spl                   false
% 3.38/1.00  --abstr_cl_out                          false
% 3.38/1.00  
% 3.38/1.00  ------ Global Options
% 3.38/1.00  
% 3.38/1.00  --schedule                              default
% 3.38/1.00  --add_important_lit                     false
% 3.38/1.00  --prop_solver_per_cl                    1000
% 3.38/1.00  --min_unsat_core                        false
% 3.38/1.00  --soft_assumptions                      false
% 3.38/1.00  --soft_lemma_size                       3
% 3.38/1.00  --prop_impl_unit_size                   0
% 3.38/1.00  --prop_impl_unit                        []
% 3.38/1.00  --share_sel_clauses                     true
% 3.38/1.00  --reset_solvers                         false
% 3.38/1.00  --bc_imp_inh                            [conj_cone]
% 3.38/1.00  --conj_cone_tolerance                   3.
% 3.38/1.00  --extra_neg_conj                        none
% 3.38/1.00  --large_theory_mode                     true
% 3.38/1.00  --prolific_symb_bound                   200
% 3.38/1.00  --lt_threshold                          2000
% 3.38/1.00  --clause_weak_htbl                      true
% 3.38/1.00  --gc_record_bc_elim                     false
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing Options
% 3.38/1.00  
% 3.38/1.00  --preprocessing_flag                    true
% 3.38/1.00  --time_out_prep_mult                    0.1
% 3.38/1.00  --splitting_mode                        input
% 3.38/1.00  --splitting_grd                         true
% 3.38/1.00  --splitting_cvd                         false
% 3.38/1.00  --splitting_cvd_svl                     false
% 3.38/1.00  --splitting_nvd                         32
% 3.38/1.00  --sub_typing                            true
% 3.38/1.00  --prep_gs_sim                           true
% 3.38/1.00  --prep_unflatten                        true
% 3.38/1.00  --prep_res_sim                          true
% 3.38/1.00  --prep_upred                            true
% 3.38/1.00  --prep_sem_filter                       exhaustive
% 3.38/1.00  --prep_sem_filter_out                   false
% 3.38/1.00  --pred_elim                             true
% 3.38/1.00  --res_sim_input                         true
% 3.38/1.00  --eq_ax_congr_red                       true
% 3.38/1.00  --pure_diseq_elim                       true
% 3.38/1.00  --brand_transform                       false
% 3.38/1.00  --non_eq_to_eq                          false
% 3.38/1.00  --prep_def_merge                        true
% 3.38/1.00  --prep_def_merge_prop_impl              false
% 3.38/1.00  --prep_def_merge_mbd                    true
% 3.38/1.00  --prep_def_merge_tr_red                 false
% 3.38/1.00  --prep_def_merge_tr_cl                  false
% 3.38/1.00  --smt_preprocessing                     true
% 3.38/1.00  --smt_ac_axioms                         fast
% 3.38/1.00  --preprocessed_out                      false
% 3.38/1.00  --preprocessed_stats                    false
% 3.38/1.00  
% 3.38/1.00  ------ Abstraction refinement Options
% 3.38/1.00  
% 3.38/1.00  --abstr_ref                             []
% 3.38/1.00  --abstr_ref_prep                        false
% 3.38/1.00  --abstr_ref_until_sat                   false
% 3.38/1.00  --abstr_ref_sig_restrict                funpre
% 3.38/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.38/1.00  --abstr_ref_under                       []
% 3.38/1.00  
% 3.38/1.00  ------ SAT Options
% 3.38/1.00  
% 3.38/1.00  --sat_mode                              false
% 3.38/1.00  --sat_fm_restart_options                ""
% 3.38/1.00  --sat_gr_def                            false
% 3.38/1.00  --sat_epr_types                         true
% 3.38/1.00  --sat_non_cyclic_types                  false
% 3.38/1.00  --sat_finite_models                     false
% 3.38/1.00  --sat_fm_lemmas                         false
% 3.38/1.00  --sat_fm_prep                           false
% 3.38/1.00  --sat_fm_uc_incr                        true
% 3.38/1.00  --sat_out_model                         small
% 3.38/1.00  --sat_out_clauses                       false
% 3.38/1.00  
% 3.38/1.00  ------ QBF Options
% 3.38/1.00  
% 3.38/1.00  --qbf_mode                              false
% 3.38/1.00  --qbf_elim_univ                         false
% 3.38/1.00  --qbf_dom_inst                          none
% 3.38/1.00  --qbf_dom_pre_inst                      false
% 3.38/1.00  --qbf_sk_in                             false
% 3.38/1.00  --qbf_pred_elim                         true
% 3.38/1.00  --qbf_split                             512
% 3.38/1.00  
% 3.38/1.00  ------ BMC1 Options
% 3.38/1.00  
% 3.38/1.00  --bmc1_incremental                      false
% 3.38/1.00  --bmc1_axioms                           reachable_all
% 3.38/1.00  --bmc1_min_bound                        0
% 3.38/1.00  --bmc1_max_bound                        -1
% 3.38/1.00  --bmc1_max_bound_default                -1
% 3.38/1.00  --bmc1_symbol_reachability              true
% 3.38/1.00  --bmc1_property_lemmas                  false
% 3.38/1.00  --bmc1_k_induction                      false
% 3.38/1.00  --bmc1_non_equiv_states                 false
% 3.38/1.00  --bmc1_deadlock                         false
% 3.38/1.00  --bmc1_ucm                              false
% 3.38/1.00  --bmc1_add_unsat_core                   none
% 3.38/1.00  --bmc1_unsat_core_children              false
% 3.38/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.38/1.00  --bmc1_out_stat                         full
% 3.38/1.00  --bmc1_ground_init                      false
% 3.38/1.00  --bmc1_pre_inst_next_state              false
% 3.38/1.00  --bmc1_pre_inst_state                   false
% 3.38/1.00  --bmc1_pre_inst_reach_state             false
% 3.38/1.00  --bmc1_out_unsat_core                   false
% 3.38/1.00  --bmc1_aig_witness_out                  false
% 3.38/1.00  --bmc1_verbose                          false
% 3.38/1.00  --bmc1_dump_clauses_tptp                false
% 3.38/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.38/1.00  --bmc1_dump_file                        -
% 3.38/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.38/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.38/1.00  --bmc1_ucm_extend_mode                  1
% 3.38/1.00  --bmc1_ucm_init_mode                    2
% 3.38/1.00  --bmc1_ucm_cone_mode                    none
% 3.38/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.38/1.00  --bmc1_ucm_relax_model                  4
% 3.38/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.38/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.38/1.00  --bmc1_ucm_layered_model                none
% 3.38/1.00  --bmc1_ucm_max_lemma_size               10
% 3.38/1.00  
% 3.38/1.00  ------ AIG Options
% 3.38/1.00  
% 3.38/1.00  --aig_mode                              false
% 3.38/1.00  
% 3.38/1.00  ------ Instantiation Options
% 3.38/1.00  
% 3.38/1.00  --instantiation_flag                    true
% 3.38/1.00  --inst_sos_flag                         true
% 3.38/1.00  --inst_sos_phase                        true
% 3.38/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.38/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.38/1.00  --inst_lit_sel_side                     none
% 3.38/1.00  --inst_solver_per_active                1400
% 3.38/1.00  --inst_solver_calls_frac                1.
% 3.38/1.00  --inst_passive_queue_type               priority_queues
% 3.38/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.38/1.00  --inst_passive_queues_freq              [25;2]
% 3.38/1.00  --inst_dismatching                      true
% 3.38/1.00  --inst_eager_unprocessed_to_passive     true
% 3.38/1.00  --inst_prop_sim_given                   true
% 3.38/1.00  --inst_prop_sim_new                     false
% 3.38/1.00  --inst_subs_new                         false
% 3.38/1.00  --inst_eq_res_simp                      false
% 3.38/1.00  --inst_subs_given                       false
% 3.38/1.00  --inst_orphan_elimination               true
% 3.38/1.00  --inst_learning_loop_flag               true
% 3.38/1.00  --inst_learning_start                   3000
% 3.38/1.00  --inst_learning_factor                  2
% 3.38/1.00  --inst_start_prop_sim_after_learn       3
% 3.38/1.00  --inst_sel_renew                        solver
% 3.38/1.00  --inst_lit_activity_flag                true
% 3.38/1.00  --inst_restr_to_given                   false
% 3.38/1.00  --inst_activity_threshold               500
% 3.38/1.00  --inst_out_proof                        true
% 3.38/1.00  
% 3.38/1.00  ------ Resolution Options
% 3.38/1.00  
% 3.38/1.00  --resolution_flag                       false
% 3.38/1.00  --res_lit_sel                           adaptive
% 3.38/1.00  --res_lit_sel_side                      none
% 3.38/1.00  --res_ordering                          kbo
% 3.38/1.00  --res_to_prop_solver                    active
% 3.38/1.00  --res_prop_simpl_new                    false
% 3.38/1.00  --res_prop_simpl_given                  true
% 3.38/1.00  --res_passive_queue_type                priority_queues
% 3.38/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.38/1.00  --res_passive_queues_freq               [15;5]
% 3.38/1.00  --res_forward_subs                      full
% 3.38/1.00  --res_backward_subs                     full
% 3.38/1.00  --res_forward_subs_resolution           true
% 3.38/1.00  --res_backward_subs_resolution          true
% 3.38/1.00  --res_orphan_elimination                true
% 3.38/1.00  --res_time_limit                        2.
% 3.38/1.00  --res_out_proof                         true
% 3.38/1.00  
% 3.38/1.00  ------ Superposition Options
% 3.38/1.00  
% 3.38/1.00  --superposition_flag                    true
% 3.38/1.00  --sup_passive_queue_type                priority_queues
% 3.38/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.38/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.38/1.00  --demod_completeness_check              fast
% 3.38/1.00  --demod_use_ground                      true
% 3.38/1.00  --sup_to_prop_solver                    passive
% 3.38/1.00  --sup_prop_simpl_new                    true
% 3.38/1.00  --sup_prop_simpl_given                  true
% 3.38/1.00  --sup_fun_splitting                     true
% 3.38/1.00  --sup_smt_interval                      50000
% 3.38/1.00  
% 3.38/1.00  ------ Superposition Simplification Setup
% 3.38/1.00  
% 3.38/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.38/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.38/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.38/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.38/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.38/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.38/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.38/1.00  --sup_immed_triv                        [TrivRules]
% 3.38/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/1.00  --sup_immed_bw_main                     []
% 3.38/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.38/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.38/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/1.00  --sup_input_bw                          []
% 3.38/1.00  
% 3.38/1.00  ------ Combination Options
% 3.38/1.00  
% 3.38/1.00  --comb_res_mult                         3
% 3.38/1.00  --comb_sup_mult                         2
% 3.38/1.00  --comb_inst_mult                        10
% 3.38/1.00  
% 3.38/1.00  ------ Debug Options
% 3.38/1.00  
% 3.38/1.00  --dbg_backtrace                         false
% 3.38/1.00  --dbg_dump_prop_clauses                 false
% 3.38/1.00  --dbg_dump_prop_clauses_file            -
% 3.38/1.00  --dbg_out_stat                          false
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  ------ Proving...
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  % SZS status Theorem for theBenchmark.p
% 3.38/1.00  
% 3.38/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.38/1.00  
% 3.38/1.00  fof(f10,conjecture,(
% 3.38/1.00    ! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0))),
% 3.38/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f11,negated_conjecture,(
% 3.38/1.00    ~! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0))),
% 3.38/1.00    inference(negated_conjecture,[],[f10])).
% 3.38/1.00  
% 3.38/1.00  fof(f15,plain,(
% 3.38/1.00    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0))),
% 3.38/1.00    inference(ennf_transformation,[],[f11])).
% 3.38/1.00  
% 3.38/1.00  fof(f21,plain,(
% 3.38/1.00    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)) => (sK1 != sK2 & r2_hidden(sK2,sK3) & k3_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_tarski(sK1))),
% 3.38/1.00    introduced(choice_axiom,[])).
% 3.38/1.00  
% 3.38/1.00  fof(f22,plain,(
% 3.38/1.00    sK1 != sK2 & r2_hidden(sK2,sK3) & k3_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_tarski(sK1)),
% 3.38/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f21])).
% 3.38/1.00  
% 3.38/1.00  fof(f40,plain,(
% 3.38/1.00    r2_hidden(sK2,sK3)),
% 3.38/1.00    inference(cnf_transformation,[],[f22])).
% 3.38/1.00  
% 3.38/1.00  fof(f9,axiom,(
% 3.38/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0))),
% 3.38/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f14,plain,(
% 3.38/1.00    ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1))),
% 3.38/1.00    inference(ennf_transformation,[],[f9])).
% 3.38/1.00  
% 3.38/1.00  fof(f38,plain,(
% 3.38/1.00    ( ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f14])).
% 3.38/1.00  
% 3.38/1.00  fof(f4,axiom,(
% 3.38/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.38/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f33,plain,(
% 3.38/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f4])).
% 3.38/1.00  
% 3.38/1.00  fof(f5,axiom,(
% 3.38/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.38/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f34,plain,(
% 3.38/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f5])).
% 3.38/1.00  
% 3.38/1.00  fof(f6,axiom,(
% 3.38/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.38/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f35,plain,(
% 3.38/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f6])).
% 3.38/1.00  
% 3.38/1.00  fof(f7,axiom,(
% 3.38/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.38/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f36,plain,(
% 3.38/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f7])).
% 3.38/1.00  
% 3.38/1.00  fof(f42,plain,(
% 3.38/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.38/1.00    inference(definition_unfolding,[],[f35,f36])).
% 3.38/1.00  
% 3.38/1.00  fof(f43,plain,(
% 3.38/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.38/1.00    inference(definition_unfolding,[],[f34,f42])).
% 3.38/1.00  
% 3.38/1.00  fof(f44,plain,(
% 3.38/1.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.38/1.00    inference(definition_unfolding,[],[f33,f43])).
% 3.38/1.00  
% 3.38/1.00  fof(f54,plain,(
% 3.38/1.00    ( ! [X0,X1] : (k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) = k3_enumset1(X0,X0,X0,X0,X0) | ~r2_hidden(X0,X1)) )),
% 3.38/1.00    inference(definition_unfolding,[],[f38,f44,f44])).
% 3.38/1.00  
% 3.38/1.00  fof(f2,axiom,(
% 3.38/1.00    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.38/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f24,plain,(
% 3.38/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f2])).
% 3.38/1.00  
% 3.38/1.00  fof(f1,axiom,(
% 3.38/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.38/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f23,plain,(
% 3.38/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f1])).
% 3.38/1.00  
% 3.38/1.00  fof(f39,plain,(
% 3.38/1.00    k3_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_tarski(sK1)),
% 3.38/1.00    inference(cnf_transformation,[],[f22])).
% 3.38/1.00  
% 3.38/1.00  fof(f55,plain,(
% 3.38/1.00    k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 3.38/1.00    inference(definition_unfolding,[],[f39,f43,f44])).
% 3.38/1.00  
% 3.38/1.00  fof(f3,axiom,(
% 3.38/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.38/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f12,plain,(
% 3.38/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.38/1.00    inference(ennf_transformation,[],[f3])).
% 3.38/1.00  
% 3.38/1.00  fof(f16,plain,(
% 3.38/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.38/1.00    inference(nnf_transformation,[],[f12])).
% 3.38/1.00  
% 3.38/1.00  fof(f17,plain,(
% 3.38/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.38/1.00    inference(flattening,[],[f16])).
% 3.38/1.00  
% 3.38/1.00  fof(f18,plain,(
% 3.38/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.38/1.00    inference(rectify,[],[f17])).
% 3.38/1.00  
% 3.38/1.00  fof(f19,plain,(
% 3.38/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.38/1.00    introduced(choice_axiom,[])).
% 3.38/1.00  
% 3.38/1.00  fof(f20,plain,(
% 3.38/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.38/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 3.38/1.00  
% 3.38/1.00  fof(f28,plain,(
% 3.38/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.38/1.00    inference(cnf_transformation,[],[f20])).
% 3.38/1.00  
% 3.38/1.00  fof(f49,plain,(
% 3.38/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.38/1.00    inference(definition_unfolding,[],[f28,f42])).
% 3.38/1.00  
% 3.38/1.00  fof(f56,plain,(
% 3.38/1.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 3.38/1.00    inference(equality_resolution,[],[f49])).
% 3.38/1.00  
% 3.38/1.00  fof(f57,plain,(
% 3.38/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 3.38/1.00    inference(equality_resolution,[],[f56])).
% 3.38/1.00  
% 3.38/1.00  fof(f8,axiom,(
% 3.38/1.00    ! [X0,X1] : (k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1) => r2_hidden(X1,X0))),
% 3.38/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/1.00  
% 3.38/1.00  fof(f13,plain,(
% 3.38/1.00    ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1))),
% 3.38/1.00    inference(ennf_transformation,[],[f8])).
% 3.38/1.00  
% 3.38/1.00  fof(f37,plain,(
% 3.38/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1)) )),
% 3.38/1.00    inference(cnf_transformation,[],[f13])).
% 3.38/1.00  
% 3.38/1.00  fof(f53,plain,(
% 3.38/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) != k3_enumset1(X1,X1,X1,X1,X1)) )),
% 3.38/1.00    inference(definition_unfolding,[],[f37,f44,f44])).
% 3.38/1.00  
% 3.38/1.00  fof(f25,plain,(
% 3.38/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.38/1.00    inference(cnf_transformation,[],[f20])).
% 3.38/1.00  
% 3.38/1.00  fof(f52,plain,(
% 3.38/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.38/1.00    inference(definition_unfolding,[],[f25,f42])).
% 3.38/1.00  
% 3.38/1.00  fof(f62,plain,(
% 3.38/1.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 3.38/1.00    inference(equality_resolution,[],[f52])).
% 3.38/1.00  
% 3.38/1.00  fof(f26,plain,(
% 3.38/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.38/1.00    inference(cnf_transformation,[],[f20])).
% 3.38/1.00  
% 3.38/1.00  fof(f51,plain,(
% 3.38/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.38/1.00    inference(definition_unfolding,[],[f26,f42])).
% 3.38/1.00  
% 3.38/1.00  fof(f60,plain,(
% 3.38/1.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 3.38/1.00    inference(equality_resolution,[],[f51])).
% 3.38/1.00  
% 3.38/1.00  fof(f61,plain,(
% 3.38/1.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 3.38/1.00    inference(equality_resolution,[],[f60])).
% 3.38/1.00  
% 3.38/1.00  fof(f41,plain,(
% 3.38/1.00    sK1 != sK2),
% 3.38/1.00    inference(cnf_transformation,[],[f22])).
% 3.38/1.00  
% 3.38/1.00  cnf(c_13,negated_conjecture,
% 3.38/1.00      ( r2_hidden(sK2,sK3) ),
% 3.38/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_805,plain,
% 3.38/1.00      ( r2_hidden(sK2,sK3) = iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_11,plain,
% 3.38/1.00      ( ~ r2_hidden(X0,X1)
% 3.38/1.00      | k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) = k3_enumset1(X0,X0,X0,X0,X0) ),
% 3.38/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_806,plain,
% 3.38/1.00      ( k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k3_enumset1(X1,X1,X1,X1,X1)
% 3.38/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_2366,plain,
% 3.38/1.00      ( k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_805,c_806]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1,plain,
% 3.38/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 3.38/1.00      inference(cnf_transformation,[],[f24]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_2405,plain,
% 3.38/1.00      ( k3_xboole_0(sK3,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),X0)) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),X0) ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_2366,c_1]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_0,plain,
% 3.38/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.38/1.00      inference(cnf_transformation,[],[f23]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_829,plain,
% 3.38/1.00      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_14,negated_conjecture,
% 3.38/1.00      ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),sK3) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
% 3.38/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_545,negated_conjecture,
% 3.38/1.00      ( k3_xboole_0(sK3,k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
% 3.38/1.00      inference(theory_normalisation,[status(thm)],[c_14,c_1,c_0]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1231,plain,
% 3.38/1.00      ( k3_xboole_0(sK3,k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),X0)) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0) ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_545,c_1]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1552,plain,
% 3.38/1.00      ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,k3_enumset1(sK1,sK1,sK1,sK1,sK2)))) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(X0,X1)) ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_829,c_1231]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_3165,plain,
% 3.38/1.00      ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(sK3,k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2))) ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_2405,c_1552]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_3170,plain,
% 3.38/1.00      ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
% 3.38/1.00      inference(demodulation,[status(thm)],[c_3165,c_2405]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_828,plain,
% 3.38/1.00      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1462,plain,
% 3.38/1.00      ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_xboole_0(sK3,X0)) = k3_xboole_0(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_545,c_828]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_1650,plain,
% 3.38/1.00      ( k3_xboole_0(k3_xboole_0(sK3,X0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k3_xboole_0(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_1462,c_0]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_2412,plain,
% 3.38/1.00      ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_2366,c_1650]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_2413,plain,
% 3.38/1.00      ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_2366,c_1462]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_6,plain,
% 3.38/1.00      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
% 3.38/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_811,plain,
% 3.38/1.00      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) = iProver_top ),
% 3.38/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_2363,plain,
% 3.38/1.00      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X2,X2,X2,X2,X2)) = k3_enumset1(X2,X2,X2,X2,X2) ),
% 3.38/1.00      inference(superposition,[status(thm)],[c_811,c_806]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_2414,plain,
% 3.38/1.00      ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 3.38/1.00      inference(demodulation,[status(thm)],[c_2413,c_2363]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_2415,plain,
% 3.38/1.00      ( k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 3.38/1.00      inference(demodulation,[status(thm)],[c_2412,c_2414]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_3171,plain,
% 3.38/1.00      ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 3.38/1.00      inference(light_normalisation,[status(thm)],[c_3170,c_2366,c_2415]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_10,plain,
% 3.38/1.00      ( r2_hidden(X0,X1)
% 3.38/1.00      | k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) != k3_enumset1(X0,X0,X0,X0,X0) ),
% 3.38/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_870,plain,
% 3.38/1.00      ( r2_hidden(sK2,k3_enumset1(X0,X0,X0,X1,X2))
% 3.38/1.00      | k3_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_872,plain,
% 3.38/1.00      ( r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
% 3.38/1.00      | k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_870]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_9,plain,
% 3.38/1.00      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 3.38/1.00      | X0 = X1
% 3.38/1.00      | X0 = X2
% 3.38/1.00      | X0 = X3 ),
% 3.38/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_837,plain,
% 3.38/1.00      ( ~ r2_hidden(sK2,k3_enumset1(X0,X0,X0,X1,X2))
% 3.38/1.00      | sK2 = X0
% 3.38/1.00      | sK2 = X1
% 3.38/1.00      | sK2 = X2 ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_839,plain,
% 3.38/1.00      ( ~ r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | sK2 = sK1 ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_837]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_548,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_835,plain,
% 3.38/1.00      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_548]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_836,plain,
% 3.38/1.00      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_835]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_8,plain,
% 3.38/1.00      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 3.38/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_26,plain,
% 3.38/1.00      ( r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_23,plain,
% 3.38/1.00      ( ~ r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | sK1 = sK1 ),
% 3.38/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(c_12,negated_conjecture,
% 3.38/1.00      ( sK1 != sK2 ),
% 3.38/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.38/1.00  
% 3.38/1.00  cnf(contradiction,plain,
% 3.38/1.00      ( $false ),
% 3.38/1.00      inference(minisat,
% 3.38/1.00                [status(thm)],
% 3.38/1.00                [c_3171,c_872,c_839,c_836,c_26,c_23,c_12]) ).
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.38/1.00  
% 3.38/1.00  ------                               Statistics
% 3.38/1.00  
% 3.38/1.00  ------ General
% 3.38/1.00  
% 3.38/1.00  abstr_ref_over_cycles:                  0
% 3.38/1.00  abstr_ref_under_cycles:                 0
% 3.38/1.00  gc_basic_clause_elim:                   0
% 3.38/1.00  forced_gc_time:                         0
% 3.38/1.00  parsing_time:                           0.013
% 3.38/1.00  unif_index_cands_time:                  0.
% 3.38/1.00  unif_index_add_time:                    0.
% 3.38/1.00  orderings_time:                         0.
% 3.38/1.00  out_proof_time:                         0.008
% 3.38/1.00  total_time:                             0.16
% 3.38/1.00  num_of_symbols:                         38
% 3.38/1.00  num_of_terms:                           4239
% 3.38/1.00  
% 3.38/1.00  ------ Preprocessing
% 3.38/1.00  
% 3.38/1.00  num_of_splits:                          0
% 3.38/1.00  num_of_split_atoms:                     0
% 3.38/1.00  num_of_reused_defs:                     0
% 3.38/1.00  num_eq_ax_congr_red:                    8
% 3.38/1.00  num_of_sem_filtered_clauses:            1
% 3.38/1.00  num_of_subtypes:                        0
% 3.38/1.00  monotx_restored_types:                  0
% 3.38/1.00  sat_num_of_epr_types:                   0
% 3.38/1.00  sat_num_of_non_cyclic_types:            0
% 3.38/1.00  sat_guarded_non_collapsed_types:        0
% 3.38/1.00  num_pure_diseq_elim:                    0
% 3.38/1.00  simp_replaced_by:                       0
% 3.38/1.00  res_preprocessed:                       56
% 3.38/1.00  prep_upred:                             0
% 3.38/1.00  prep_unflattend:                        36
% 3.38/1.00  smt_new_axioms:                         0
% 3.38/1.00  pred_elim_cands:                        1
% 3.38/1.00  pred_elim:                              0
% 3.38/1.00  pred_elim_cl:                           0
% 3.38/1.00  pred_elim_cycles:                       1
% 3.38/1.00  merged_defs:                            6
% 3.38/1.00  merged_defs_ncl:                        0
% 3.38/1.00  bin_hyper_res:                          6
% 3.38/1.00  prep_cycles:                            3
% 3.38/1.00  pred_elim_time:                         0.006
% 3.38/1.00  splitting_time:                         0.
% 3.38/1.00  sem_filter_time:                        0.
% 3.38/1.00  monotx_time:                            0.
% 3.38/1.00  subtype_inf_time:                       0.
% 3.38/1.00  
% 3.38/1.00  ------ Problem properties
% 3.38/1.00  
% 3.38/1.00  clauses:                                15
% 3.38/1.00  conjectures:                            3
% 3.38/1.00  epr:                                    2
% 3.38/1.00  horn:                                   13
% 3.38/1.00  ground:                                 3
% 3.38/1.00  unary:                                  8
% 3.38/1.00  binary:                                 2
% 3.38/1.00  lits:                                   30
% 3.38/1.00  lits_eq:                                19
% 3.38/1.00  fd_pure:                                0
% 3.38/1.00  fd_pseudo:                              0
% 3.38/1.00  fd_cond:                                0
% 3.38/1.00  fd_pseudo_cond:                         4
% 3.38/1.00  ac_symbols:                             1
% 3.38/1.00  
% 3.38/1.00  ------ Propositional Solver
% 3.38/1.00  
% 3.38/1.00  prop_solver_calls:                      27
% 3.38/1.00  prop_fast_solver_calls:                 377
% 3.38/1.00  smt_solver_calls:                       0
% 3.38/1.00  smt_fast_solver_calls:                  0
% 3.38/1.00  prop_num_of_clauses:                    1096
% 3.38/1.00  prop_preprocess_simplified:             2668
% 3.38/1.00  prop_fo_subsumed:                       0
% 3.38/1.00  prop_solver_time:                       0.
% 3.38/1.00  smt_solver_time:                        0.
% 3.38/1.00  smt_fast_solver_time:                   0.
% 3.38/1.00  prop_fast_solver_time:                  0.
% 3.38/1.00  prop_unsat_core_time:                   0.
% 3.38/1.00  
% 3.38/1.00  ------ QBF
% 3.38/1.00  
% 3.38/1.00  qbf_q_res:                              0
% 3.38/1.00  qbf_num_tautologies:                    0
% 3.38/1.00  qbf_prep_cycles:                        0
% 3.38/1.00  
% 3.38/1.00  ------ BMC1
% 3.38/1.00  
% 3.38/1.00  bmc1_current_bound:                     -1
% 3.38/1.00  bmc1_last_solved_bound:                 -1
% 3.38/1.00  bmc1_unsat_core_size:                   -1
% 3.38/1.00  bmc1_unsat_core_parents_size:           -1
% 3.38/1.00  bmc1_merge_next_fun:                    0
% 3.38/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.38/1.00  
% 3.38/1.00  ------ Instantiation
% 3.38/1.00  
% 3.38/1.00  inst_num_of_clauses:                    297
% 3.38/1.00  inst_num_in_passive:                    31
% 3.38/1.00  inst_num_in_active:                     136
% 3.38/1.00  inst_num_in_unprocessed:                130
% 3.38/1.00  inst_num_of_loops:                      170
% 3.38/1.00  inst_num_of_learning_restarts:          0
% 3.38/1.00  inst_num_moves_active_passive:          30
% 3.38/1.00  inst_lit_activity:                      0
% 3.38/1.00  inst_lit_activity_moves:                0
% 3.38/1.00  inst_num_tautologies:                   0
% 3.38/1.00  inst_num_prop_implied:                  0
% 3.38/1.00  inst_num_existing_simplified:           0
% 3.38/1.00  inst_num_eq_res_simplified:             0
% 3.38/1.00  inst_num_child_elim:                    0
% 3.38/1.00  inst_num_of_dismatching_blockings:      101
% 3.38/1.00  inst_num_of_non_proper_insts:           358
% 3.38/1.00  inst_num_of_duplicates:                 0
% 3.38/1.00  inst_inst_num_from_inst_to_res:         0
% 3.38/1.00  inst_dismatching_checking_time:         0.
% 3.38/1.00  
% 3.38/1.00  ------ Resolution
% 3.38/1.00  
% 3.38/1.00  res_num_of_clauses:                     0
% 3.38/1.00  res_num_in_passive:                     0
% 3.38/1.00  res_num_in_active:                      0
% 3.38/1.00  res_num_of_loops:                       59
% 3.38/1.00  res_forward_subset_subsumed:            88
% 3.38/1.00  res_backward_subset_subsumed:           0
% 3.38/1.00  res_forward_subsumed:                   0
% 3.38/1.00  res_backward_subsumed:                  0
% 3.38/1.00  res_forward_subsumption_resolution:     0
% 3.38/1.00  res_backward_subsumption_resolution:    0
% 3.38/1.00  res_clause_to_clause_subsumption:       1234
% 3.38/1.00  res_orphan_elimination:                 0
% 3.38/1.00  res_tautology_del:                      27
% 3.38/1.00  res_num_eq_res_simplified:              0
% 3.38/1.00  res_num_sel_changes:                    0
% 3.38/1.00  res_moves_from_active_to_pass:          0
% 3.38/1.00  
% 3.38/1.00  ------ Superposition
% 3.38/1.00  
% 3.38/1.00  sup_time_total:                         0.
% 3.38/1.00  sup_time_generating:                    0.
% 3.38/1.00  sup_time_sim_full:                      0.
% 3.38/1.00  sup_time_sim_immed:                     0.
% 3.38/1.00  
% 3.38/1.00  sup_num_of_clauses:                     157
% 3.38/1.00  sup_num_in_active:                      34
% 3.38/1.00  sup_num_in_passive:                     123
% 3.38/1.00  sup_num_of_loops:                       33
% 3.38/1.00  sup_fw_superposition:                   350
% 3.38/1.00  sup_bw_superposition:                   301
% 3.38/1.00  sup_immediate_simplified:               174
% 3.38/1.00  sup_given_eliminated:                   0
% 3.38/1.00  comparisons_done:                       0
% 3.38/1.00  comparisons_avoided:                    6
% 3.38/1.00  
% 3.38/1.00  ------ Simplifications
% 3.38/1.00  
% 3.38/1.00  
% 3.38/1.00  sim_fw_subset_subsumed:                 0
% 3.38/1.00  sim_bw_subset_subsumed:                 0
% 3.38/1.00  sim_fw_subsumed:                        16
% 3.38/1.00  sim_bw_subsumed:                        0
% 3.38/1.00  sim_fw_subsumption_res:                 0
% 3.38/1.00  sim_bw_subsumption_res:                 0
% 3.38/1.00  sim_tautology_del:                      0
% 3.38/1.00  sim_eq_tautology_del:                   8
% 3.38/1.00  sim_eq_res_simp:                        0
% 3.38/1.00  sim_fw_demodulated:                     57
% 3.38/1.00  sim_bw_demodulated:                     4
% 3.38/1.00  sim_light_normalised:                   21
% 3.38/1.00  sim_joinable_taut:                      92
% 3.38/1.00  sim_joinable_simp:                      0
% 3.38/1.00  sim_ac_normalised:                      0
% 3.38/1.00  sim_smt_subsumption:                    0
% 3.38/1.00  
%------------------------------------------------------------------------------
