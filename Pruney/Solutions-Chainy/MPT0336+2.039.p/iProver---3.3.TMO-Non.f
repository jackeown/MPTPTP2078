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
% DateTime   : Thu Dec  3 11:38:40 EST 2020

% Result     : Timeout 59.68s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  118 ( 245 expanded)
%              Number of clauses        :   55 (  68 expanded)
%              Number of leaves         :   18 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  284 ( 616 expanded)
%              Number of equality atoms :  142 ( 282 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f20])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
      & r1_xboole_0(sK4,sK3)
      & r2_hidden(sK5,sK4)
      & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f31])).

fof(f56,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f29])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f58])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f50,f60,f60])).

fof(f54,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f54,f60])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f44,f60])).

fof(f71,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f64])).

fof(f72,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f71])).

fof(f55,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f23])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f58])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f43,f60])).

fof(f73,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f57,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) ),
    inference(definition_unfolding,[],[f57,f59])).

cnf(c_18,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_756,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_768,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1560,plain,
    ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_756,c_768])).

cnf(c_7,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_785,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_1568,plain,
    ( k3_xboole_0(sK4,k3_xboole_0(X0,sK3)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1560,c_785])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_763,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1559,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_763,c_768])).

cnf(c_1572,plain,
    ( k3_xboole_0(sK4,k3_xboole_0(X0,sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1568,c_1559])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_769,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1783,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_769])).

cnf(c_2306,plain,
    ( r1_xboole_0(k3_xboole_0(X0,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1572,c_1783])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_254,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k2_enumset1(X0,X0,X0,X0) != k2_enumset1(sK5,sK5,sK5,sK5)
    | k3_xboole_0(sK2,sK3) != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_255,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k2_enumset1(sK5,sK5,sK5,sK5)
    | k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(sK2,sK3)
    | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_1017,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k3_xboole_0(sK2,sK3)
    | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_255])).

cnf(c_12,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_759,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1316,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0
    | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1017,c_759])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_755,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_766,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3000,plain,
    ( r2_hidden(sK5,X0) != iProver_top
    | r1_xboole_0(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_755,c_766])).

cnf(c_3108,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0
    | r1_xboole_0(k3_xboole_0(sK2,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_3000])).

cnf(c_73052,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2306,c_3108])).

cnf(c_1033,plain,
    ( r1_xboole_0(X0,sK3)
    | k3_xboole_0(X0,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_11560,plain,
    ( r1_xboole_0(sK2,sK3)
    | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1033])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1073,plain,
    ( ~ r1_xboole_0(X0,sK3)
    | r1_xboole_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6679,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1073])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k3_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2972,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) = k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_410,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1499,plain,
    ( k3_xboole_0(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k3_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_410])).

cnf(c_2942,plain,
    ( k3_xboole_0(sK3,sK4) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1499])).

cnf(c_2943,plain,
    ( k3_xboole_0(sK3,sK4) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK3,sK4)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2942])).

cnf(c_767,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1451,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_756,c_767])).

cnf(c_1562,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1451,c_768])).

cnf(c_949,plain,
    ( k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) != X0
    | k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_410])).

cnf(c_1187,plain,
    ( k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) != k3_xboole_0(sK3,sK4)
    | k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_949])).

cnf(c_855,plain,
    ( r1_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)))
    | k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_801,plain,
    ( r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3)
    | ~ r1_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_38,plain,
    ( r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_35,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_17,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73052,c_11560,c_6679,c_2972,c_2943,c_1562,c_1187,c_855,c_801,c_38,c_35,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:13:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 59.68/7.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 59.68/7.99  
% 59.68/7.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.68/7.99  
% 59.68/7.99  ------  iProver source info
% 59.68/7.99  
% 59.68/7.99  git: date: 2020-06-30 10:37:57 +0100
% 59.68/7.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.68/7.99  git: non_committed_changes: false
% 59.68/7.99  git: last_make_outside_of_git: false
% 59.68/7.99  
% 59.68/7.99  ------ 
% 59.68/7.99  
% 59.68/7.99  ------ Input Options
% 59.68/7.99  
% 59.68/7.99  --out_options                           all
% 59.68/7.99  --tptp_safe_out                         true
% 59.68/7.99  --problem_path                          ""
% 59.68/7.99  --include_path                          ""
% 59.68/7.99  --clausifier                            res/vclausify_rel
% 59.68/7.99  --clausifier_options                    ""
% 59.68/7.99  --stdin                                 false
% 59.68/7.99  --stats_out                             all
% 59.68/7.99  
% 59.68/7.99  ------ General Options
% 59.68/7.99  
% 59.68/7.99  --fof                                   false
% 59.68/7.99  --time_out_real                         305.
% 59.68/7.99  --time_out_virtual                      -1.
% 59.68/7.99  --symbol_type_check                     false
% 59.68/7.99  --clausify_out                          false
% 59.68/7.99  --sig_cnt_out                           false
% 59.68/7.99  --trig_cnt_out                          false
% 59.68/7.99  --trig_cnt_out_tolerance                1.
% 59.68/7.99  --trig_cnt_out_sk_spl                   false
% 59.68/7.99  --abstr_cl_out                          false
% 59.68/7.99  
% 59.68/7.99  ------ Global Options
% 59.68/7.99  
% 59.68/7.99  --schedule                              default
% 59.68/7.99  --add_important_lit                     false
% 59.68/7.99  --prop_solver_per_cl                    1000
% 59.68/7.99  --min_unsat_core                        false
% 59.68/7.99  --soft_assumptions                      false
% 59.68/7.99  --soft_lemma_size                       3
% 59.68/7.99  --prop_impl_unit_size                   0
% 59.68/7.99  --prop_impl_unit                        []
% 59.68/7.99  --share_sel_clauses                     true
% 59.68/7.99  --reset_solvers                         false
% 59.68/7.99  --bc_imp_inh                            [conj_cone]
% 59.68/7.99  --conj_cone_tolerance                   3.
% 59.68/7.99  --extra_neg_conj                        none
% 59.68/7.99  --large_theory_mode                     true
% 59.68/7.99  --prolific_symb_bound                   200
% 59.68/7.99  --lt_threshold                          2000
% 59.68/7.99  --clause_weak_htbl                      true
% 59.68/7.99  --gc_record_bc_elim                     false
% 59.68/7.99  
% 59.68/7.99  ------ Preprocessing Options
% 59.68/7.99  
% 59.68/7.99  --preprocessing_flag                    true
% 59.68/7.99  --time_out_prep_mult                    0.1
% 59.68/7.99  --splitting_mode                        input
% 59.68/7.99  --splitting_grd                         true
% 59.68/7.99  --splitting_cvd                         false
% 59.68/7.99  --splitting_cvd_svl                     false
% 59.68/7.99  --splitting_nvd                         32
% 59.68/7.99  --sub_typing                            true
% 59.68/7.99  --prep_gs_sim                           true
% 59.68/7.99  --prep_unflatten                        true
% 59.68/7.99  --prep_res_sim                          true
% 59.68/7.99  --prep_upred                            true
% 59.68/7.99  --prep_sem_filter                       exhaustive
% 59.68/7.99  --prep_sem_filter_out                   false
% 59.68/7.99  --pred_elim                             true
% 59.68/7.99  --res_sim_input                         true
% 59.68/7.99  --eq_ax_congr_red                       true
% 59.68/7.99  --pure_diseq_elim                       true
% 59.68/7.99  --brand_transform                       false
% 59.68/7.99  --non_eq_to_eq                          false
% 59.68/7.99  --prep_def_merge                        true
% 59.68/7.99  --prep_def_merge_prop_impl              false
% 59.68/7.99  --prep_def_merge_mbd                    true
% 59.68/7.99  --prep_def_merge_tr_red                 false
% 59.68/7.99  --prep_def_merge_tr_cl                  false
% 59.68/7.99  --smt_preprocessing                     true
% 59.68/7.99  --smt_ac_axioms                         fast
% 59.68/7.99  --preprocessed_out                      false
% 59.68/7.99  --preprocessed_stats                    false
% 59.68/7.99  
% 59.68/7.99  ------ Abstraction refinement Options
% 59.68/7.99  
% 59.68/7.99  --abstr_ref                             []
% 59.68/7.99  --abstr_ref_prep                        false
% 59.68/7.99  --abstr_ref_until_sat                   false
% 59.68/7.99  --abstr_ref_sig_restrict                funpre
% 59.68/7.99  --abstr_ref_af_restrict_to_split_sk     false
% 59.68/7.99  --abstr_ref_under                       []
% 59.68/7.99  
% 59.68/7.99  ------ SAT Options
% 59.68/7.99  
% 59.68/7.99  --sat_mode                              false
% 59.68/7.99  --sat_fm_restart_options                ""
% 59.68/7.99  --sat_gr_def                            false
% 59.68/7.99  --sat_epr_types                         true
% 59.68/7.99  --sat_non_cyclic_types                  false
% 59.68/7.99  --sat_finite_models                     false
% 59.68/7.99  --sat_fm_lemmas                         false
% 59.68/7.99  --sat_fm_prep                           false
% 59.68/7.99  --sat_fm_uc_incr                        true
% 59.68/7.99  --sat_out_model                         small
% 59.68/7.99  --sat_out_clauses                       false
% 59.68/7.99  
% 59.68/7.99  ------ QBF Options
% 59.68/7.99  
% 59.68/7.99  --qbf_mode                              false
% 59.68/7.99  --qbf_elim_univ                         false
% 59.68/7.99  --qbf_dom_inst                          none
% 59.68/7.99  --qbf_dom_pre_inst                      false
% 59.68/7.99  --qbf_sk_in                             false
% 59.68/7.99  --qbf_pred_elim                         true
% 59.68/7.99  --qbf_split                             512
% 59.68/7.99  
% 59.68/7.99  ------ BMC1 Options
% 59.68/7.99  
% 59.68/7.99  --bmc1_incremental                      false
% 59.68/7.99  --bmc1_axioms                           reachable_all
% 59.68/7.99  --bmc1_min_bound                        0
% 59.68/7.99  --bmc1_max_bound                        -1
% 59.68/7.99  --bmc1_max_bound_default                -1
% 59.68/7.99  --bmc1_symbol_reachability              true
% 59.68/7.99  --bmc1_property_lemmas                  false
% 59.68/7.99  --bmc1_k_induction                      false
% 59.68/7.99  --bmc1_non_equiv_states                 false
% 59.68/7.99  --bmc1_deadlock                         false
% 59.68/7.99  --bmc1_ucm                              false
% 59.68/7.99  --bmc1_add_unsat_core                   none
% 59.68/7.99  --bmc1_unsat_core_children              false
% 59.68/7.99  --bmc1_unsat_core_extrapolate_axioms    false
% 59.68/7.99  --bmc1_out_stat                         full
% 59.68/7.99  --bmc1_ground_init                      false
% 59.68/7.99  --bmc1_pre_inst_next_state              false
% 59.68/7.99  --bmc1_pre_inst_state                   false
% 59.68/7.99  --bmc1_pre_inst_reach_state             false
% 59.68/7.99  --bmc1_out_unsat_core                   false
% 59.68/7.99  --bmc1_aig_witness_out                  false
% 59.68/7.99  --bmc1_verbose                          false
% 59.68/7.99  --bmc1_dump_clauses_tptp                false
% 59.68/7.99  --bmc1_dump_unsat_core_tptp             false
% 59.68/7.99  --bmc1_dump_file                        -
% 59.68/7.99  --bmc1_ucm_expand_uc_limit              128
% 59.68/7.99  --bmc1_ucm_n_expand_iterations          6
% 59.68/7.99  --bmc1_ucm_extend_mode                  1
% 59.68/7.99  --bmc1_ucm_init_mode                    2
% 59.68/7.99  --bmc1_ucm_cone_mode                    none
% 59.68/7.99  --bmc1_ucm_reduced_relation_type        0
% 59.68/7.99  --bmc1_ucm_relax_model                  4
% 59.68/7.99  --bmc1_ucm_full_tr_after_sat            true
% 59.68/7.99  --bmc1_ucm_expand_neg_assumptions       false
% 59.68/7.99  --bmc1_ucm_layered_model                none
% 59.68/7.99  --bmc1_ucm_max_lemma_size               10
% 59.68/7.99  
% 59.68/7.99  ------ AIG Options
% 59.68/7.99  
% 59.68/7.99  --aig_mode                              false
% 59.68/7.99  
% 59.68/7.99  ------ Instantiation Options
% 59.68/7.99  
% 59.68/7.99  --instantiation_flag                    true
% 59.68/7.99  --inst_sos_flag                         true
% 59.68/7.99  --inst_sos_phase                        true
% 59.68/7.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.68/7.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.68/7.99  --inst_lit_sel_side                     num_symb
% 59.68/7.99  --inst_solver_per_active                1400
% 59.68/7.99  --inst_solver_calls_frac                1.
% 59.68/7.99  --inst_passive_queue_type               priority_queues
% 59.68/7.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.68/7.99  --inst_passive_queues_freq              [25;2]
% 59.68/7.99  --inst_dismatching                      true
% 59.68/7.99  --inst_eager_unprocessed_to_passive     true
% 59.68/7.99  --inst_prop_sim_given                   true
% 59.68/7.99  --inst_prop_sim_new                     false
% 59.68/7.99  --inst_subs_new                         false
% 59.68/7.99  --inst_eq_res_simp                      false
% 59.68/7.99  --inst_subs_given                       false
% 59.68/7.99  --inst_orphan_elimination               true
% 59.68/7.99  --inst_learning_loop_flag               true
% 59.68/7.99  --inst_learning_start                   3000
% 59.68/7.99  --inst_learning_factor                  2
% 59.68/7.99  --inst_start_prop_sim_after_learn       3
% 59.68/7.99  --inst_sel_renew                        solver
% 59.68/7.99  --inst_lit_activity_flag                true
% 59.68/7.99  --inst_restr_to_given                   false
% 59.68/7.99  --inst_activity_threshold               500
% 59.68/7.99  --inst_out_proof                        true
% 59.68/7.99  
% 59.68/7.99  ------ Resolution Options
% 59.68/7.99  
% 59.68/7.99  --resolution_flag                       true
% 59.68/7.99  --res_lit_sel                           adaptive
% 59.68/7.99  --res_lit_sel_side                      none
% 59.68/7.99  --res_ordering                          kbo
% 59.68/7.99  --res_to_prop_solver                    active
% 59.68/7.99  --res_prop_simpl_new                    false
% 59.68/7.99  --res_prop_simpl_given                  true
% 59.68/7.99  --res_passive_queue_type                priority_queues
% 59.68/7.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.68/7.99  --res_passive_queues_freq               [15;5]
% 59.68/7.99  --res_forward_subs                      full
% 59.68/7.99  --res_backward_subs                     full
% 59.68/7.99  --res_forward_subs_resolution           true
% 59.68/7.99  --res_backward_subs_resolution          true
% 59.68/7.99  --res_orphan_elimination                true
% 59.68/7.99  --res_time_limit                        2.
% 59.68/7.99  --res_out_proof                         true
% 59.68/7.99  
% 59.68/7.99  ------ Superposition Options
% 59.68/7.99  
% 59.68/7.99  --superposition_flag                    true
% 59.68/7.99  --sup_passive_queue_type                priority_queues
% 59.68/7.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.68/7.99  --sup_passive_queues_freq               [8;1;4]
% 59.68/7.99  --demod_completeness_check              fast
% 59.68/7.99  --demod_use_ground                      true
% 59.68/7.99  --sup_to_prop_solver                    passive
% 59.68/7.99  --sup_prop_simpl_new                    true
% 59.68/7.99  --sup_prop_simpl_given                  true
% 59.68/7.99  --sup_fun_splitting                     true
% 59.68/7.99  --sup_smt_interval                      50000
% 59.68/7.99  
% 59.68/7.99  ------ Superposition Simplification Setup
% 59.68/7.99  
% 59.68/7.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 59.68/7.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 59.68/7.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 59.68/7.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 59.68/7.99  --sup_full_triv                         [TrivRules;PropSubs]
% 59.68/7.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 59.68/7.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 59.68/7.99  --sup_immed_triv                        [TrivRules]
% 59.68/7.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.68/7.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.68/7.99  --sup_immed_bw_main                     []
% 59.68/7.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 59.68/7.99  --sup_input_triv                        [Unflattening;TrivRules]
% 59.68/7.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.68/7.99  --sup_input_bw                          []
% 59.68/7.99  
% 59.68/7.99  ------ Combination Options
% 59.68/7.99  
% 59.68/7.99  --comb_res_mult                         3
% 59.68/7.99  --comb_sup_mult                         2
% 59.68/7.99  --comb_inst_mult                        10
% 59.68/7.99  
% 59.68/7.99  ------ Debug Options
% 59.68/7.99  
% 59.68/7.99  --dbg_backtrace                         false
% 59.68/7.99  --dbg_dump_prop_clauses                 false
% 59.68/7.99  --dbg_dump_prop_clauses_file            -
% 59.68/7.99  --dbg_out_stat                          false
% 59.68/7.99  ------ Parsing...
% 59.68/7.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.68/7.99  
% 59.68/7.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 59.68/7.99  
% 59.68/7.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.68/7.99  
% 59.68/7.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.68/7.99  ------ Proving...
% 59.68/7.99  ------ Problem Properties 
% 59.68/7.99  
% 59.68/7.99  
% 59.68/7.99  clauses                                 18
% 59.68/7.99  conjectures                             3
% 59.68/7.99  EPR                                     5
% 59.68/7.99  Horn                                    14
% 59.68/7.99  unary                                   7
% 59.68/7.99  binary                                  7
% 59.68/7.99  lits                                    33
% 59.68/7.99  lits eq                                 13
% 59.68/7.99  fd_pure                                 0
% 59.68/7.99  fd_pseudo                               0
% 59.68/7.99  fd_cond                                 0
% 59.68/7.99  fd_pseudo_cond                          2
% 59.68/7.99  AC symbols                              1
% 59.68/7.99  
% 59.68/7.99  ------ Schedule dynamic 5 is on 
% 59.68/7.99  
% 59.68/7.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 59.68/7.99  
% 59.68/7.99  
% 59.68/7.99  ------ 
% 59.68/7.99  Current options:
% 59.68/7.99  ------ 
% 59.68/7.99  
% 59.68/7.99  ------ Input Options
% 59.68/7.99  
% 59.68/7.99  --out_options                           all
% 59.68/7.99  --tptp_safe_out                         true
% 59.68/7.99  --problem_path                          ""
% 59.68/7.99  --include_path                          ""
% 59.68/7.99  --clausifier                            res/vclausify_rel
% 59.68/7.99  --clausifier_options                    ""
% 59.68/7.99  --stdin                                 false
% 59.68/7.99  --stats_out                             all
% 59.68/7.99  
% 59.68/7.99  ------ General Options
% 59.68/7.99  
% 59.68/7.99  --fof                                   false
% 59.68/7.99  --time_out_real                         305.
% 59.68/7.99  --time_out_virtual                      -1.
% 59.68/7.99  --symbol_type_check                     false
% 59.68/7.99  --clausify_out                          false
% 59.68/7.99  --sig_cnt_out                           false
% 59.68/7.99  --trig_cnt_out                          false
% 59.68/7.99  --trig_cnt_out_tolerance                1.
% 59.68/7.99  --trig_cnt_out_sk_spl                   false
% 59.68/7.99  --abstr_cl_out                          false
% 59.68/7.99  
% 59.68/7.99  ------ Global Options
% 59.68/7.99  
% 59.68/7.99  --schedule                              default
% 59.68/7.99  --add_important_lit                     false
% 59.68/7.99  --prop_solver_per_cl                    1000
% 59.68/7.99  --min_unsat_core                        false
% 59.68/7.99  --soft_assumptions                      false
% 59.68/7.99  --soft_lemma_size                       3
% 59.68/7.99  --prop_impl_unit_size                   0
% 59.68/7.99  --prop_impl_unit                        []
% 59.68/7.99  --share_sel_clauses                     true
% 59.68/7.99  --reset_solvers                         false
% 59.68/7.99  --bc_imp_inh                            [conj_cone]
% 59.68/7.99  --conj_cone_tolerance                   3.
% 59.68/7.99  --extra_neg_conj                        none
% 59.68/7.99  --large_theory_mode                     true
% 59.68/7.99  --prolific_symb_bound                   200
% 59.68/7.99  --lt_threshold                          2000
% 59.68/7.99  --clause_weak_htbl                      true
% 59.68/7.99  --gc_record_bc_elim                     false
% 59.68/7.99  
% 59.68/7.99  ------ Preprocessing Options
% 59.68/7.99  
% 59.68/7.99  --preprocessing_flag                    true
% 59.68/7.99  --time_out_prep_mult                    0.1
% 59.68/7.99  --splitting_mode                        input
% 59.68/7.99  --splitting_grd                         true
% 59.68/7.99  --splitting_cvd                         false
% 59.68/7.99  --splitting_cvd_svl                     false
% 59.68/7.99  --splitting_nvd                         32
% 59.68/7.99  --sub_typing                            true
% 59.68/7.99  --prep_gs_sim                           true
% 59.68/7.99  --prep_unflatten                        true
% 59.68/7.99  --prep_res_sim                          true
% 59.68/7.99  --prep_upred                            true
% 59.68/7.99  --prep_sem_filter                       exhaustive
% 59.68/7.99  --prep_sem_filter_out                   false
% 59.68/7.99  --pred_elim                             true
% 59.68/7.99  --res_sim_input                         true
% 59.68/7.99  --eq_ax_congr_red                       true
% 59.68/7.99  --pure_diseq_elim                       true
% 59.68/7.99  --brand_transform                       false
% 59.68/7.99  --non_eq_to_eq                          false
% 59.68/7.99  --prep_def_merge                        true
% 59.68/7.99  --prep_def_merge_prop_impl              false
% 59.68/7.99  --prep_def_merge_mbd                    true
% 59.68/7.99  --prep_def_merge_tr_red                 false
% 59.68/7.99  --prep_def_merge_tr_cl                  false
% 59.68/7.99  --smt_preprocessing                     true
% 59.68/7.99  --smt_ac_axioms                         fast
% 59.68/7.99  --preprocessed_out                      false
% 59.68/7.99  --preprocessed_stats                    false
% 59.68/7.99  
% 59.68/7.99  ------ Abstraction refinement Options
% 59.68/7.99  
% 59.68/7.99  --abstr_ref                             []
% 59.68/7.99  --abstr_ref_prep                        false
% 59.68/7.99  --abstr_ref_until_sat                   false
% 59.68/7.99  --abstr_ref_sig_restrict                funpre
% 59.68/7.99  --abstr_ref_af_restrict_to_split_sk     false
% 59.68/7.99  --abstr_ref_under                       []
% 59.68/7.99  
% 59.68/7.99  ------ SAT Options
% 59.68/7.99  
% 59.68/7.99  --sat_mode                              false
% 59.68/7.99  --sat_fm_restart_options                ""
% 59.68/7.99  --sat_gr_def                            false
% 59.68/7.99  --sat_epr_types                         true
% 59.68/7.99  --sat_non_cyclic_types                  false
% 59.68/7.99  --sat_finite_models                     false
% 59.68/7.99  --sat_fm_lemmas                         false
% 59.68/7.99  --sat_fm_prep                           false
% 59.68/7.99  --sat_fm_uc_incr                        true
% 59.68/7.99  --sat_out_model                         small
% 59.68/7.99  --sat_out_clauses                       false
% 59.68/7.99  
% 59.68/7.99  ------ QBF Options
% 59.68/7.99  
% 59.68/7.99  --qbf_mode                              false
% 59.68/7.99  --qbf_elim_univ                         false
% 59.68/7.99  --qbf_dom_inst                          none
% 59.68/7.99  --qbf_dom_pre_inst                      false
% 59.68/7.99  --qbf_sk_in                             false
% 59.68/7.99  --qbf_pred_elim                         true
% 59.68/7.99  --qbf_split                             512
% 59.68/7.99  
% 59.68/7.99  ------ BMC1 Options
% 59.68/7.99  
% 59.68/7.99  --bmc1_incremental                      false
% 59.68/7.99  --bmc1_axioms                           reachable_all
% 59.68/7.99  --bmc1_min_bound                        0
% 59.68/7.99  --bmc1_max_bound                        -1
% 59.68/7.99  --bmc1_max_bound_default                -1
% 59.68/7.99  --bmc1_symbol_reachability              true
% 59.68/7.99  --bmc1_property_lemmas                  false
% 59.68/7.99  --bmc1_k_induction                      false
% 59.68/7.99  --bmc1_non_equiv_states                 false
% 59.68/7.99  --bmc1_deadlock                         false
% 59.68/7.99  --bmc1_ucm                              false
% 59.68/7.99  --bmc1_add_unsat_core                   none
% 59.68/7.99  --bmc1_unsat_core_children              false
% 59.68/7.99  --bmc1_unsat_core_extrapolate_axioms    false
% 59.68/7.99  --bmc1_out_stat                         full
% 59.68/7.99  --bmc1_ground_init                      false
% 59.68/7.99  --bmc1_pre_inst_next_state              false
% 59.68/7.99  --bmc1_pre_inst_state                   false
% 59.68/7.99  --bmc1_pre_inst_reach_state             false
% 59.68/7.99  --bmc1_out_unsat_core                   false
% 59.68/7.99  --bmc1_aig_witness_out                  false
% 59.68/7.99  --bmc1_verbose                          false
% 59.68/7.99  --bmc1_dump_clauses_tptp                false
% 59.68/7.99  --bmc1_dump_unsat_core_tptp             false
% 59.68/7.99  --bmc1_dump_file                        -
% 59.68/7.99  --bmc1_ucm_expand_uc_limit              128
% 59.68/7.99  --bmc1_ucm_n_expand_iterations          6
% 59.68/7.99  --bmc1_ucm_extend_mode                  1
% 59.68/7.99  --bmc1_ucm_init_mode                    2
% 59.68/7.99  --bmc1_ucm_cone_mode                    none
% 59.68/7.99  --bmc1_ucm_reduced_relation_type        0
% 59.68/7.99  --bmc1_ucm_relax_model                  4
% 59.68/7.99  --bmc1_ucm_full_tr_after_sat            true
% 59.68/7.99  --bmc1_ucm_expand_neg_assumptions       false
% 59.68/7.99  --bmc1_ucm_layered_model                none
% 59.68/7.99  --bmc1_ucm_max_lemma_size               10
% 59.68/7.99  
% 59.68/7.99  ------ AIG Options
% 59.68/7.99  
% 59.68/7.99  --aig_mode                              false
% 59.68/7.99  
% 59.68/7.99  ------ Instantiation Options
% 59.68/7.99  
% 59.68/7.99  --instantiation_flag                    true
% 59.68/7.99  --inst_sos_flag                         true
% 59.68/7.99  --inst_sos_phase                        true
% 59.68/7.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.68/7.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.68/7.99  --inst_lit_sel_side                     none
% 59.68/7.99  --inst_solver_per_active                1400
% 59.68/7.99  --inst_solver_calls_frac                1.
% 59.68/7.99  --inst_passive_queue_type               priority_queues
% 59.68/7.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.68/7.99  --inst_passive_queues_freq              [25;2]
% 59.68/7.99  --inst_dismatching                      true
% 59.68/7.99  --inst_eager_unprocessed_to_passive     true
% 59.68/7.99  --inst_prop_sim_given                   true
% 59.68/7.99  --inst_prop_sim_new                     false
% 59.68/7.99  --inst_subs_new                         false
% 59.68/7.99  --inst_eq_res_simp                      false
% 59.68/7.99  --inst_subs_given                       false
% 59.68/7.99  --inst_orphan_elimination               true
% 59.68/7.99  --inst_learning_loop_flag               true
% 59.68/7.99  --inst_learning_start                   3000
% 59.68/7.99  --inst_learning_factor                  2
% 59.68/7.99  --inst_start_prop_sim_after_learn       3
% 59.68/7.99  --inst_sel_renew                        solver
% 59.68/7.99  --inst_lit_activity_flag                true
% 59.68/7.99  --inst_restr_to_given                   false
% 59.68/7.99  --inst_activity_threshold               500
% 59.68/7.99  --inst_out_proof                        true
% 59.68/7.99  
% 59.68/7.99  ------ Resolution Options
% 59.68/7.99  
% 59.68/7.99  --resolution_flag                       false
% 59.68/7.99  --res_lit_sel                           adaptive
% 59.68/7.99  --res_lit_sel_side                      none
% 59.68/7.99  --res_ordering                          kbo
% 59.68/7.99  --res_to_prop_solver                    active
% 59.68/7.99  --res_prop_simpl_new                    false
% 59.68/7.99  --res_prop_simpl_given                  true
% 59.68/7.99  --res_passive_queue_type                priority_queues
% 59.68/7.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.68/7.99  --res_passive_queues_freq               [15;5]
% 59.68/7.99  --res_forward_subs                      full
% 59.68/7.99  --res_backward_subs                     full
% 59.68/7.99  --res_forward_subs_resolution           true
% 59.68/7.99  --res_backward_subs_resolution          true
% 59.68/7.99  --res_orphan_elimination                true
% 59.68/7.99  --res_time_limit                        2.
% 59.68/7.99  --res_out_proof                         true
% 59.68/7.99  
% 59.68/7.99  ------ Superposition Options
% 59.68/7.99  
% 59.68/7.99  --superposition_flag                    true
% 59.68/7.99  --sup_passive_queue_type                priority_queues
% 59.68/7.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.68/7.99  --sup_passive_queues_freq               [8;1;4]
% 59.68/7.99  --demod_completeness_check              fast
% 59.68/7.99  --demod_use_ground                      true
% 59.68/7.99  --sup_to_prop_solver                    passive
% 59.68/7.99  --sup_prop_simpl_new                    true
% 59.68/7.99  --sup_prop_simpl_given                  true
% 59.68/7.99  --sup_fun_splitting                     true
% 59.68/7.99  --sup_smt_interval                      50000
% 59.68/7.99  
% 59.68/7.99  ------ Superposition Simplification Setup
% 59.68/7.99  
% 59.68/7.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 59.68/7.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 59.68/7.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 59.68/7.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 59.68/7.99  --sup_full_triv                         [TrivRules;PropSubs]
% 59.68/7.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 59.68/7.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 59.68/7.99  --sup_immed_triv                        [TrivRules]
% 59.68/7.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.68/7.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.68/7.99  --sup_immed_bw_main                     []
% 59.68/7.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 59.68/7.99  --sup_input_triv                        [Unflattening;TrivRules]
% 59.68/7.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.68/7.99  --sup_input_bw                          []
% 59.68/7.99  
% 59.68/7.99  ------ Combination Options
% 59.68/7.99  
% 59.68/7.99  --comb_res_mult                         3
% 59.68/7.99  --comb_sup_mult                         2
% 59.68/7.99  --comb_inst_mult                        10
% 59.68/7.99  
% 59.68/7.99  ------ Debug Options
% 59.68/7.99  
% 59.68/7.99  --dbg_backtrace                         false
% 59.68/7.99  --dbg_dump_prop_clauses                 false
% 59.68/7.99  --dbg_dump_prop_clauses_file            -
% 59.68/7.99  --dbg_out_stat                          false
% 59.68/7.99  
% 59.68/7.99  
% 59.68/7.99  
% 59.68/7.99  
% 59.68/7.99  ------ Proving...
% 59.68/7.99  
% 59.68/7.99  
% 59.68/7.99  % SZS status Theorem for theBenchmark.p
% 59.68/7.99  
% 59.68/7.99  % SZS output start CNFRefutation for theBenchmark.p
% 59.68/7.99  
% 59.68/7.99  fof(f14,conjecture,(
% 59.68/7.99    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 59.68/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/7.99  
% 59.68/7.99  fof(f15,negated_conjecture,(
% 59.68/7.99    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 59.68/7.99    inference(negated_conjecture,[],[f14])).
% 59.68/7.99  
% 59.68/7.99  fof(f20,plain,(
% 59.68/7.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 59.68/7.99    inference(ennf_transformation,[],[f15])).
% 59.68/7.99  
% 59.68/7.99  fof(f21,plain,(
% 59.68/7.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 59.68/7.99    inference(flattening,[],[f20])).
% 59.68/7.99  
% 59.68/7.99  fof(f31,plain,(
% 59.68/7.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 59.68/7.99    introduced(choice_axiom,[])).
% 59.68/7.99  
% 59.68/7.99  fof(f32,plain,(
% 59.68/7.99    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 59.68/7.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f31])).
% 59.68/7.99  
% 59.68/7.99  fof(f56,plain,(
% 59.68/7.99    r1_xboole_0(sK4,sK3)),
% 59.68/7.99    inference(cnf_transformation,[],[f32])).
% 59.68/7.99  
% 59.68/7.99  fof(f2,axiom,(
% 59.68/7.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 59.68/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/7.99  
% 59.68/7.99  fof(f22,plain,(
% 59.68/7.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 59.68/7.99    inference(nnf_transformation,[],[f2])).
% 59.68/7.99  
% 59.68/7.99  fof(f34,plain,(
% 59.68/7.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 59.68/7.99    inference(cnf_transformation,[],[f22])).
% 59.68/7.99  
% 59.68/7.99  fof(f5,axiom,(
% 59.68/7.99    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 59.68/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/7.99  
% 59.68/7.99  fof(f40,plain,(
% 59.68/7.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 59.68/7.99    inference(cnf_transformation,[],[f5])).
% 59.68/7.99  
% 59.68/7.99  fof(f1,axiom,(
% 59.68/7.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 59.68/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/7.99  
% 59.68/7.99  fof(f33,plain,(
% 59.68/7.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 59.68/7.99    inference(cnf_transformation,[],[f1])).
% 59.68/7.99  
% 59.68/7.99  fof(f6,axiom,(
% 59.68/7.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 59.68/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/7.99  
% 59.68/7.99  fof(f41,plain,(
% 59.68/7.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 59.68/7.99    inference(cnf_transformation,[],[f6])).
% 59.68/7.99  
% 59.68/7.99  fof(f35,plain,(
% 59.68/7.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 59.68/7.99    inference(cnf_transformation,[],[f22])).
% 59.68/7.99  
% 59.68/7.99  fof(f12,axiom,(
% 59.68/7.99    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 59.68/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/7.99  
% 59.68/7.99  fof(f29,plain,(
% 59.68/7.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 59.68/7.99    inference(nnf_transformation,[],[f12])).
% 59.68/7.99  
% 59.68/7.99  fof(f30,plain,(
% 59.68/7.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 59.68/7.99    inference(flattening,[],[f29])).
% 59.68/7.99  
% 59.68/7.99  fof(f50,plain,(
% 59.68/7.99    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 59.68/7.99    inference(cnf_transformation,[],[f30])).
% 59.68/7.99  
% 59.68/7.99  fof(f9,axiom,(
% 59.68/7.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 59.68/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/7.99  
% 59.68/7.99  fof(f47,plain,(
% 59.68/7.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 59.68/7.99    inference(cnf_transformation,[],[f9])).
% 59.68/7.99  
% 59.68/7.99  fof(f10,axiom,(
% 59.68/7.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 59.68/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/7.99  
% 59.68/7.99  fof(f48,plain,(
% 59.68/7.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 59.68/7.99    inference(cnf_transformation,[],[f10])).
% 59.68/7.99  
% 59.68/7.99  fof(f11,axiom,(
% 59.68/7.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 59.68/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/7.99  
% 59.68/7.99  fof(f49,plain,(
% 59.68/7.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 59.68/7.99    inference(cnf_transformation,[],[f11])).
% 59.68/7.99  
% 59.68/7.99  fof(f58,plain,(
% 59.68/7.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 59.68/7.99    inference(definition_unfolding,[],[f48,f49])).
% 59.68/7.99  
% 59.68/7.99  fof(f60,plain,(
% 59.68/7.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 59.68/7.99    inference(definition_unfolding,[],[f47,f58])).
% 59.68/7.99  
% 59.68/7.99  fof(f68,plain,(
% 59.68/7.99    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 59.68/7.99    inference(definition_unfolding,[],[f50,f60,f60])).
% 59.68/7.99  
% 59.68/7.99  fof(f54,plain,(
% 59.68/7.99    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 59.68/7.99    inference(cnf_transformation,[],[f32])).
% 59.68/7.99  
% 59.68/7.99  fof(f70,plain,(
% 59.68/7.99    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))),
% 59.68/7.99    inference(definition_unfolding,[],[f54,f60])).
% 59.68/7.99  
% 59.68/7.99  fof(f8,axiom,(
% 59.68/7.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 59.68/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/7.99  
% 59.68/7.99  fof(f25,plain,(
% 59.68/7.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 59.68/7.99    inference(nnf_transformation,[],[f8])).
% 59.68/7.99  
% 59.68/7.99  fof(f26,plain,(
% 59.68/7.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 59.68/7.99    inference(rectify,[],[f25])).
% 59.68/7.99  
% 59.68/7.99  fof(f27,plain,(
% 59.68/7.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 59.68/7.99    introduced(choice_axiom,[])).
% 59.68/7.99  
% 59.68/7.99  fof(f28,plain,(
% 59.68/7.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 59.68/7.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 59.68/7.99  
% 59.68/7.99  fof(f44,plain,(
% 59.68/7.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 59.68/7.99    inference(cnf_transformation,[],[f28])).
% 59.68/7.99  
% 59.68/7.99  fof(f64,plain,(
% 59.68/7.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 59.68/7.99    inference(definition_unfolding,[],[f44,f60])).
% 59.68/7.99  
% 59.68/7.99  fof(f71,plain,(
% 59.68/7.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 59.68/7.99    inference(equality_resolution,[],[f64])).
% 59.68/7.99  
% 59.68/7.99  fof(f72,plain,(
% 59.68/7.99    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 59.68/7.99    inference(equality_resolution,[],[f71])).
% 59.68/7.99  
% 59.68/7.99  fof(f55,plain,(
% 59.68/7.99    r2_hidden(sK5,sK4)),
% 59.68/7.99    inference(cnf_transformation,[],[f32])).
% 59.68/7.99  
% 59.68/7.99  fof(f4,axiom,(
% 59.68/7.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 59.68/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/7.99  
% 59.68/7.99  fof(f16,plain,(
% 59.68/7.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 59.68/7.99    inference(rectify,[],[f4])).
% 59.68/7.99  
% 59.68/7.99  fof(f18,plain,(
% 59.68/7.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 59.68/7.99    inference(ennf_transformation,[],[f16])).
% 59.68/7.99  
% 59.68/7.99  fof(f23,plain,(
% 59.68/7.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 59.68/7.99    introduced(choice_axiom,[])).
% 59.68/7.99  
% 59.68/7.99  fof(f24,plain,(
% 59.68/7.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 59.68/7.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f23])).
% 59.68/7.99  
% 59.68/7.99  fof(f39,plain,(
% 59.68/7.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 59.68/7.99    inference(cnf_transformation,[],[f24])).
% 59.68/7.99  
% 59.68/7.99  fof(f3,axiom,(
% 59.68/7.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 59.68/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/7.99  
% 59.68/7.99  fof(f17,plain,(
% 59.68/7.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 59.68/7.99    inference(ennf_transformation,[],[f3])).
% 59.68/7.99  
% 59.68/7.99  fof(f36,plain,(
% 59.68/7.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 59.68/7.99    inference(cnf_transformation,[],[f17])).
% 59.68/7.99  
% 59.68/7.99  fof(f7,axiom,(
% 59.68/7.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 59.68/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/7.99  
% 59.68/7.99  fof(f19,plain,(
% 59.68/7.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 59.68/7.99    inference(ennf_transformation,[],[f7])).
% 59.68/7.99  
% 59.68/7.99  fof(f42,plain,(
% 59.68/7.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 59.68/7.99    inference(cnf_transformation,[],[f19])).
% 59.68/7.99  
% 59.68/7.99  fof(f13,axiom,(
% 59.68/7.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 59.68/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/7.99  
% 59.68/7.99  fof(f53,plain,(
% 59.68/7.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 59.68/7.99    inference(cnf_transformation,[],[f13])).
% 59.68/7.99  
% 59.68/7.99  fof(f59,plain,(
% 59.68/7.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 59.68/7.99    inference(definition_unfolding,[],[f53,f58])).
% 59.68/7.99  
% 59.68/7.99  fof(f61,plain,(
% 59.68/7.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~r1_xboole_0(X0,X1)) )),
% 59.68/7.99    inference(definition_unfolding,[],[f42,f59])).
% 59.68/7.99  
% 59.68/7.99  fof(f43,plain,(
% 59.68/7.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 59.68/7.99    inference(cnf_transformation,[],[f28])).
% 59.68/7.99  
% 59.68/7.99  fof(f65,plain,(
% 59.68/7.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 59.68/7.99    inference(definition_unfolding,[],[f43,f60])).
% 59.68/7.99  
% 59.68/7.99  fof(f73,plain,(
% 59.68/7.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 59.68/7.99    inference(equality_resolution,[],[f65])).
% 59.68/7.99  
% 59.68/7.99  fof(f57,plain,(
% 59.68/7.99    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 59.68/7.99    inference(cnf_transformation,[],[f32])).
% 59.68/7.99  
% 59.68/7.99  fof(f69,plain,(
% 59.68/7.99    ~r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3)),
% 59.68/7.99    inference(definition_unfolding,[],[f57,f59])).
% 59.68/7.99  
% 59.68/7.99  cnf(c_18,negated_conjecture,
% 59.68/7.99      ( r1_xboole_0(sK4,sK3) ),
% 59.68/7.99      inference(cnf_transformation,[],[f56]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_756,plain,
% 59.68/7.99      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 59.68/7.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_2,plain,
% 59.68/7.99      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 59.68/7.99      inference(cnf_transformation,[],[f34]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_768,plain,
% 59.68/7.99      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 59.68/7.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 59.68/7.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_1560,plain,
% 59.68/7.99      ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
% 59.68/7.99      inference(superposition,[status(thm)],[c_756,c_768]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_7,plain,
% 59.68/7.99      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 59.68/7.99      inference(cnf_transformation,[],[f40]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_0,plain,
% 59.68/7.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 59.68/7.99      inference(cnf_transformation,[],[f33]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_785,plain,
% 59.68/7.99      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 59.68/7.99      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_1568,plain,
% 59.68/7.99      ( k3_xboole_0(sK4,k3_xboole_0(X0,sK3)) = k3_xboole_0(X0,k1_xboole_0) ),
% 59.68/7.99      inference(superposition,[status(thm)],[c_1560,c_785]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_8,plain,
% 59.68/7.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 59.68/7.99      inference(cnf_transformation,[],[f41]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_763,plain,
% 59.68/7.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 59.68/7.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_1559,plain,
% 59.68/7.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 59.68/7.99      inference(superposition,[status(thm)],[c_763,c_768]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_1572,plain,
% 59.68/7.99      ( k3_xboole_0(sK4,k3_xboole_0(X0,sK3)) = k1_xboole_0 ),
% 59.68/7.99      inference(light_normalisation,[status(thm)],[c_1568,c_1559]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_1,plain,
% 59.68/7.99      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 59.68/7.99      inference(cnf_transformation,[],[f35]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_769,plain,
% 59.68/7.99      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 59.68/7.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 59.68/7.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_1783,plain,
% 59.68/7.99      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 59.68/7.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 59.68/7.99      inference(superposition,[status(thm)],[c_0,c_769]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_2306,plain,
% 59.68/7.99      ( r1_xboole_0(k3_xboole_0(X0,sK3),sK4) = iProver_top ),
% 59.68/7.99      inference(superposition,[status(thm)],[c_1572,c_1783]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_16,plain,
% 59.68/7.99      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 59.68/7.99      | k2_enumset1(X1,X1,X1,X1) = X0
% 59.68/7.99      | k1_xboole_0 = X0 ),
% 59.68/7.99      inference(cnf_transformation,[],[f68]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_20,negated_conjecture,
% 59.68/7.99      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 59.68/7.99      inference(cnf_transformation,[],[f70]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_254,plain,
% 59.68/7.99      ( k2_enumset1(X0,X0,X0,X0) = X1
% 59.68/7.99      | k2_enumset1(X0,X0,X0,X0) != k2_enumset1(sK5,sK5,sK5,sK5)
% 59.68/7.99      | k3_xboole_0(sK2,sK3) != X1
% 59.68/7.99      | k1_xboole_0 = X1 ),
% 59.68/7.99      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_255,plain,
% 59.68/7.99      ( k2_enumset1(X0,X0,X0,X0) != k2_enumset1(sK5,sK5,sK5,sK5)
% 59.68/7.99      | k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(sK2,sK3)
% 59.68/7.99      | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
% 59.68/7.99      inference(unflattening,[status(thm)],[c_254]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_1017,plain,
% 59.68/7.99      ( k2_enumset1(sK5,sK5,sK5,sK5) = k3_xboole_0(sK2,sK3)
% 59.68/7.99      | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 59.68/7.99      inference(equality_resolution,[status(thm)],[c_255]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_12,plain,
% 59.68/7.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 59.68/7.99      inference(cnf_transformation,[],[f72]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_759,plain,
% 59.68/7.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 59.68/7.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_1316,plain,
% 59.68/7.99      ( k3_xboole_0(sK2,sK3) = k1_xboole_0
% 59.68/7.99      | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) = iProver_top ),
% 59.68/7.99      inference(superposition,[status(thm)],[c_1017,c_759]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_19,negated_conjecture,
% 59.68/7.99      ( r2_hidden(sK5,sK4) ),
% 59.68/7.99      inference(cnf_transformation,[],[f55]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_755,plain,
% 59.68/7.99      ( r2_hidden(sK5,sK4) = iProver_top ),
% 59.68/7.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_4,plain,
% 59.68/7.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 59.68/7.99      inference(cnf_transformation,[],[f39]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_766,plain,
% 59.68/7.99      ( r2_hidden(X0,X1) != iProver_top
% 59.68/7.99      | r2_hidden(X0,X2) != iProver_top
% 59.68/7.99      | r1_xboole_0(X2,X1) != iProver_top ),
% 59.68/7.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_3000,plain,
% 59.68/7.99      ( r2_hidden(sK5,X0) != iProver_top
% 59.68/7.99      | r1_xboole_0(X0,sK4) != iProver_top ),
% 59.68/7.99      inference(superposition,[status(thm)],[c_755,c_766]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_3108,plain,
% 59.68/7.99      ( k3_xboole_0(sK2,sK3) = k1_xboole_0
% 59.68/7.99      | r1_xboole_0(k3_xboole_0(sK2,sK3),sK4) != iProver_top ),
% 59.68/7.99      inference(superposition,[status(thm)],[c_1316,c_3000]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_73052,plain,
% 59.68/7.99      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 59.68/7.99      inference(superposition,[status(thm)],[c_2306,c_3108]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_1033,plain,
% 59.68/7.99      ( r1_xboole_0(X0,sK3) | k3_xboole_0(X0,sK3) != k1_xboole_0 ),
% 59.68/7.99      inference(instantiation,[status(thm)],[c_1]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_11560,plain,
% 59.68/7.99      ( r1_xboole_0(sK2,sK3) | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
% 59.68/7.99      inference(instantiation,[status(thm)],[c_1033]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_3,plain,
% 59.68/7.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 59.68/7.99      inference(cnf_transformation,[],[f36]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_1073,plain,
% 59.68/7.99      ( ~ r1_xboole_0(X0,sK3) | r1_xboole_0(sK3,X0) ),
% 59.68/7.99      inference(instantiation,[status(thm)],[c_3]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_6679,plain,
% 59.68/7.99      ( r1_xboole_0(sK3,sK2) | ~ r1_xboole_0(sK2,sK3) ),
% 59.68/7.99      inference(instantiation,[status(thm)],[c_1073]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_9,plain,
% 59.68/7.99      ( ~ r1_xboole_0(X0,X1)
% 59.68/7.99      | k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k3_xboole_0(X0,X2) ),
% 59.68/7.99      inference(cnf_transformation,[],[f61]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_2972,plain,
% 59.68/7.99      ( ~ r1_xboole_0(sK3,sK2)
% 59.68/7.99      | k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) = k3_xboole_0(sK3,sK4) ),
% 59.68/7.99      inference(instantiation,[status(thm)],[c_9]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_410,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_1499,plain,
% 59.68/7.99      ( k3_xboole_0(X0,X1) != X2
% 59.68/7.99      | k1_xboole_0 != X2
% 59.68/7.99      | k1_xboole_0 = k3_xboole_0(X0,X1) ),
% 59.68/7.99      inference(instantiation,[status(thm)],[c_410]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_2942,plain,
% 59.68/7.99      ( k3_xboole_0(sK3,sK4) != X0
% 59.68/7.99      | k1_xboole_0 != X0
% 59.68/7.99      | k1_xboole_0 = k3_xboole_0(sK3,sK4) ),
% 59.68/7.99      inference(instantiation,[status(thm)],[c_1499]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_2943,plain,
% 59.68/7.99      ( k3_xboole_0(sK3,sK4) != k1_xboole_0
% 59.68/7.99      | k1_xboole_0 = k3_xboole_0(sK3,sK4)
% 59.68/7.99      | k1_xboole_0 != k1_xboole_0 ),
% 59.68/7.99      inference(instantiation,[status(thm)],[c_2942]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_767,plain,
% 59.68/7.99      ( r1_xboole_0(X0,X1) != iProver_top
% 59.68/7.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 59.68/7.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_1451,plain,
% 59.68/7.99      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 59.68/7.99      inference(superposition,[status(thm)],[c_756,c_767]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_1562,plain,
% 59.68/7.99      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 59.68/7.99      inference(superposition,[status(thm)],[c_1451,c_768]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_949,plain,
% 59.68/7.99      ( k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) != X0
% 59.68/7.99      | k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) = k1_xboole_0
% 59.68/7.99      | k1_xboole_0 != X0 ),
% 59.68/7.99      inference(instantiation,[status(thm)],[c_410]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_1187,plain,
% 59.68/7.99      ( k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) != k3_xboole_0(sK3,sK4)
% 59.68/7.99      | k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) = k1_xboole_0
% 59.68/7.99      | k1_xboole_0 != k3_xboole_0(sK3,sK4) ),
% 59.68/7.99      inference(instantiation,[status(thm)],[c_949]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_855,plain,
% 59.68/7.99      ( r1_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)))
% 59.68/7.99      | k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) != k1_xboole_0 ),
% 59.68/7.99      inference(instantiation,[status(thm)],[c_1]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_801,plain,
% 59.68/7.99      ( r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3)
% 59.68/7.99      | ~ r1_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) ),
% 59.68/7.99      inference(instantiation,[status(thm)],[c_3]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_38,plain,
% 59.68/7.99      ( r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 59.68/7.99      inference(instantiation,[status(thm)],[c_12]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_13,plain,
% 59.68/7.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 59.68/7.99      inference(cnf_transformation,[],[f73]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_35,plain,
% 59.68/7.99      ( ~ r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 59.68/7.99      | k1_xboole_0 = k1_xboole_0 ),
% 59.68/7.99      inference(instantiation,[status(thm)],[c_13]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(c_17,negated_conjecture,
% 59.68/7.99      ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) ),
% 59.68/7.99      inference(cnf_transformation,[],[f69]) ).
% 59.68/7.99  
% 59.68/7.99  cnf(contradiction,plain,
% 59.68/7.99      ( $false ),
% 59.68/7.99      inference(minisat,
% 59.68/7.99                [status(thm)],
% 59.68/7.99                [c_73052,c_11560,c_6679,c_2972,c_2943,c_1562,c_1187,
% 59.68/7.99                 c_855,c_801,c_38,c_35,c_17]) ).
% 59.68/7.99  
% 59.68/7.99  
% 59.68/7.99  % SZS output end CNFRefutation for theBenchmark.p
% 59.68/7.99  
% 59.68/7.99  ------                               Statistics
% 59.68/7.99  
% 59.68/7.99  ------ General
% 59.68/7.99  
% 59.68/7.99  abstr_ref_over_cycles:                  0
% 59.68/7.99  abstr_ref_under_cycles:                 0
% 59.68/7.99  gc_basic_clause_elim:                   0
% 59.68/7.99  forced_gc_time:                         0
% 59.68/7.99  parsing_time:                           0.008
% 59.68/7.99  unif_index_cands_time:                  0.
% 59.68/7.99  unif_index_add_time:                    0.
% 59.68/7.99  orderings_time:                         0.
% 59.68/7.99  out_proof_time:                         0.018
% 59.68/7.99  total_time:                             7.377
% 59.68/7.99  num_of_symbols:                         44
% 59.68/7.99  num_of_terms:                           85562
% 59.68/7.99  
% 59.68/7.99  ------ Preprocessing
% 59.68/7.99  
% 59.68/7.99  num_of_splits:                          0
% 59.68/7.99  num_of_split_atoms:                     0
% 59.68/7.99  num_of_reused_defs:                     0
% 59.68/7.99  num_eq_ax_congr_red:                    12
% 59.68/7.99  num_of_sem_filtered_clauses:            1
% 59.68/7.99  num_of_subtypes:                        0
% 59.68/7.99  monotx_restored_types:                  0
% 59.68/7.99  sat_num_of_epr_types:                   0
% 59.68/7.99  sat_num_of_non_cyclic_types:            0
% 59.68/7.99  sat_guarded_non_collapsed_types:        0
% 59.68/7.99  num_pure_diseq_elim:                    0
% 59.68/7.99  simp_replaced_by:                       0
% 59.68/7.99  res_preprocessed:                       90
% 59.68/7.99  prep_upred:                             0
% 59.68/7.99  prep_unflattend:                        3
% 59.68/7.99  smt_new_axioms:                         0
% 59.68/7.99  pred_elim_cands:                        2
% 59.68/7.99  pred_elim:                              1
% 59.68/7.99  pred_elim_cl:                           3
% 59.68/7.99  pred_elim_cycles:                       3
% 59.68/7.99  merged_defs:                            8
% 59.68/7.99  merged_defs_ncl:                        0
% 59.68/7.99  bin_hyper_res:                          8
% 59.68/7.99  prep_cycles:                            4
% 59.68/7.99  pred_elim_time:                         0.
% 59.68/7.99  splitting_time:                         0.
% 59.68/7.99  sem_filter_time:                        0.
% 59.68/7.99  monotx_time:                            0.
% 59.68/7.99  subtype_inf_time:                       0.
% 59.68/7.99  
% 59.68/7.99  ------ Problem properties
% 59.68/7.99  
% 59.68/7.99  clauses:                                18
% 59.68/7.99  conjectures:                            3
% 59.68/7.99  epr:                                    5
% 59.68/7.99  horn:                                   14
% 59.68/7.99  ground:                                 3
% 59.68/7.99  unary:                                  7
% 59.68/7.99  binary:                                 7
% 59.68/7.99  lits:                                   33
% 59.68/7.99  lits_eq:                                13
% 59.68/7.99  fd_pure:                                0
% 59.68/7.99  fd_pseudo:                              0
% 59.68/7.99  fd_cond:                                0
% 59.68/7.99  fd_pseudo_cond:                         2
% 59.68/7.99  ac_symbols:                             1
% 59.68/7.99  
% 59.68/7.99  ------ Propositional Solver
% 59.68/7.99  
% 59.68/7.99  prop_solver_calls:                      34
% 59.68/7.99  prop_fast_solver_calls:                 857
% 59.68/7.99  smt_solver_calls:                       0
% 59.68/7.99  smt_fast_solver_calls:                  0
% 59.68/7.99  prop_num_of_clauses:                    33722
% 59.68/7.99  prop_preprocess_simplified:             13521
% 59.68/7.99  prop_fo_subsumed:                       1
% 59.68/7.99  prop_solver_time:                       0.
% 59.68/7.99  smt_solver_time:                        0.
% 59.68/7.99  smt_fast_solver_time:                   0.
% 59.68/7.99  prop_fast_solver_time:                  0.
% 59.68/7.99  prop_unsat_core_time:                   0.005
% 59.68/7.99  
% 59.68/7.99  ------ QBF
% 59.68/7.99  
% 59.68/7.99  qbf_q_res:                              0
% 59.68/7.99  qbf_num_tautologies:                    0
% 59.68/7.99  qbf_prep_cycles:                        0
% 59.68/7.99  
% 59.68/7.99  ------ BMC1
% 59.68/7.99  
% 59.68/7.99  bmc1_current_bound:                     -1
% 59.68/7.99  bmc1_last_solved_bound:                 -1
% 59.68/7.99  bmc1_unsat_core_size:                   -1
% 59.68/7.99  bmc1_unsat_core_parents_size:           -1
% 59.68/7.99  bmc1_merge_next_fun:                    0
% 59.68/7.99  bmc1_unsat_core_clauses_time:           0.
% 59.68/7.99  
% 59.68/7.99  ------ Instantiation
% 59.68/7.99  
% 59.68/7.99  inst_num_of_clauses:                    2996
% 59.68/7.99  inst_num_in_passive:                    233
% 59.68/7.99  inst_num_in_active:                     1328
% 59.68/7.99  inst_num_in_unprocessed:                1435
% 59.68/7.99  inst_num_of_loops:                      1590
% 59.68/7.99  inst_num_of_learning_restarts:          0
% 59.68/7.99  inst_num_moves_active_passive:          258
% 59.68/7.99  inst_lit_activity:                      0
% 59.68/7.99  inst_lit_activity_moves:                0
% 59.68/7.99  inst_num_tautologies:                   0
% 59.68/7.99  inst_num_prop_implied:                  0
% 59.68/7.99  inst_num_existing_simplified:           0
% 59.68/7.99  inst_num_eq_res_simplified:             0
% 59.68/7.99  inst_num_child_elim:                    0
% 59.68/7.99  inst_num_of_dismatching_blockings:      1833
% 59.68/7.99  inst_num_of_non_proper_insts:           3988
% 59.68/7.99  inst_num_of_duplicates:                 0
% 59.68/7.99  inst_inst_num_from_inst_to_res:         0
% 59.68/7.99  inst_dismatching_checking_time:         0.
% 59.68/7.99  
% 59.68/7.99  ------ Resolution
% 59.68/7.99  
% 59.68/7.99  res_num_of_clauses:                     0
% 59.68/7.99  res_num_in_passive:                     0
% 59.68/7.99  res_num_in_active:                      0
% 59.68/7.99  res_num_of_loops:                       94
% 59.68/7.99  res_forward_subset_subsumed:            292
% 59.68/7.99  res_backward_subset_subsumed:           0
% 59.68/7.99  res_forward_subsumed:                   0
% 59.68/7.99  res_backward_subsumed:                  0
% 59.68/7.99  res_forward_subsumption_resolution:     0
% 59.68/7.99  res_backward_subsumption_resolution:    0
% 59.68/7.99  res_clause_to_clause_subsumption:       71779
% 59.68/7.99  res_orphan_elimination:                 0
% 59.68/7.99  res_tautology_del:                      289
% 59.68/7.99  res_num_eq_res_simplified:              0
% 59.68/7.99  res_num_sel_changes:                    0
% 59.68/7.99  res_moves_from_active_to_pass:          0
% 59.68/7.99  
% 59.68/7.99  ------ Superposition
% 59.68/7.99  
% 59.68/7.99  sup_time_total:                         0.
% 59.68/7.99  sup_time_generating:                    0.
% 59.68/7.99  sup_time_sim_full:                      0.
% 59.68/7.99  sup_time_sim_immed:                     0.
% 59.68/7.99  
% 59.68/7.99  sup_num_of_clauses:                     7348
% 59.68/7.99  sup_num_in_active:                      309
% 59.68/7.99  sup_num_in_passive:                     7039
% 59.68/7.99  sup_num_of_loops:                       316
% 59.68/7.99  sup_fw_superposition:                   17398
% 59.68/7.99  sup_bw_superposition:                   8593
% 59.68/7.99  sup_immediate_simplified:               8355
% 59.68/7.99  sup_given_eliminated:                   0
% 59.68/7.99  comparisons_done:                       0
% 59.68/7.99  comparisons_avoided:                    5
% 59.68/7.99  
% 59.68/7.99  ------ Simplifications
% 59.68/7.99  
% 59.68/7.99  
% 59.68/7.99  sim_fw_subset_subsumed:                 55
% 59.68/7.99  sim_bw_subset_subsumed:                 4
% 59.68/7.99  sim_fw_subsumed:                        3927
% 59.68/7.99  sim_bw_subsumed:                        203
% 59.68/7.99  sim_fw_subsumption_res:                 0
% 59.68/7.99  sim_bw_subsumption_res:                 0
% 59.68/7.99  sim_tautology_del:                      1
% 59.68/7.99  sim_eq_tautology_del:                   329
% 59.68/7.99  sim_eq_res_simp:                        3107
% 59.68/7.99  sim_fw_demodulated:                     3158
% 59.68/7.99  sim_bw_demodulated:                     59
% 59.68/7.99  sim_light_normalised:                   3908
% 59.68/7.99  sim_joinable_taut:                      18
% 59.68/7.99  sim_joinable_simp:                      0
% 59.68/7.99  sim_ac_normalised:                      0
% 59.68/7.99  sim_smt_subsumption:                    0
% 59.68/7.99  
%------------------------------------------------------------------------------
