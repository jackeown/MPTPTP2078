%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:00 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 245 expanded)
%              Number of clauses        :   38 (  47 expanded)
%              Number of leaves         :   18 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  254 ( 546 expanded)
%              Number of equality atoms :  161 ( 373 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f71])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f55,f72])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK3 != sK5
      & sK3 != sK4
      & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( sK3 != sK5
    & sK3 != sK4
    & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f26,f38])).

fof(f67,plain,(
    r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f61,f72])).

fof(f83,plain,(
    r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f67,f73,f72])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f30])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f57,f72])).

fof(f84,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k3_enumset1(X0,X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f78])).

fof(f85,plain,(
    ! [X4,X0] : r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f84])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f48,f73])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f54,f48])).

fof(f74,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f51,f48,f70])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) ) ),
    inference(definition_unfolding,[],[f65,f48,f73])).

fof(f69,plain,(
    sK3 != sK5 ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2042,plain,
    ( ~ r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,X1))
    | X0 = X1
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3546,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK5))
    | sK3 = sK4
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_2042])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_256,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK5) != X0
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != X1
    | k3_xboole_0(X1,X0) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_257,plain,
    ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1188,plain,
    ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2986,plain,
    ( r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_257,c_1188])).

cnf(c_16,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1487,plain,
    ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1488,plain,
    ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1487])).

cnf(c_778,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1319,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k3_enumset1(X3,X3,X3,X3,X2))
    | X0 != X2
    | X1 != k3_enumset1(X3,X3,X3,X3,X2) ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_1447,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)))
    | ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | X0 != sK3
    | k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1319])).

cnf(c_1966,plain,
    ( r2_hidden(k3_xboole_0(sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)))
    | ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | k3_xboole_0(sK3,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_1447])).

cnf(c_1968,plain,
    ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | k3_xboole_0(sK3,sK3) != sK3
    | r2_hidden(k3_xboole_0(sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5))) = iProver_top
    | r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1966])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1967,plain,
    ( k3_xboole_0(sK3,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2871,plain,
    ( ~ r2_hidden(k3_xboole_0(sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)))
    | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2872,plain,
    ( r2_hidden(k3_xboole_0(sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5))) != iProver_top
    | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2871])).

cnf(c_3242,plain,
    ( r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2986,c_257,c_1488,c_1968,c_1967,c_2872])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1180,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) = k1_xboole_0
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3247,plain,
    ( k5_xboole_0(k3_enumset1(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5))),k3_xboole_0(k3_enumset1(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3242,c_1180])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3249,plain,
    ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3247,c_10])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3252,plain,
    ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3249,c_2,c_11])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1179,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) != k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1519,plain,
    ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != k1_xboole_0
    | r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_257,c_1179])).

cnf(c_1531,plain,
    ( r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK5))
    | k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1519])).

cnf(c_21,negated_conjecture,
    ( sK3 != sK5 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_22,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f68])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3546,c_3252,c_1531,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:07:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.49/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.01  
% 2.49/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.49/1.01  
% 2.49/1.01  ------  iProver source info
% 2.49/1.01  
% 2.49/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.49/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.49/1.01  git: non_committed_changes: false
% 2.49/1.01  git: last_make_outside_of_git: false
% 2.49/1.01  
% 2.49/1.01  ------ 
% 2.49/1.01  
% 2.49/1.01  ------ Input Options
% 2.49/1.01  
% 2.49/1.01  --out_options                           all
% 2.49/1.01  --tptp_safe_out                         true
% 2.49/1.01  --problem_path                          ""
% 2.49/1.01  --include_path                          ""
% 2.49/1.01  --clausifier                            res/vclausify_rel
% 2.49/1.01  --clausifier_options                    --mode clausify
% 2.49/1.01  --stdin                                 false
% 2.49/1.01  --stats_out                             all
% 2.49/1.01  
% 2.49/1.01  ------ General Options
% 2.49/1.01  
% 2.49/1.01  --fof                                   false
% 2.49/1.01  --time_out_real                         305.
% 2.49/1.01  --time_out_virtual                      -1.
% 2.49/1.01  --symbol_type_check                     false
% 2.49/1.01  --clausify_out                          false
% 2.49/1.01  --sig_cnt_out                           false
% 2.49/1.01  --trig_cnt_out                          false
% 2.49/1.01  --trig_cnt_out_tolerance                1.
% 2.49/1.01  --trig_cnt_out_sk_spl                   false
% 2.49/1.01  --abstr_cl_out                          false
% 2.49/1.01  
% 2.49/1.01  ------ Global Options
% 2.49/1.01  
% 2.49/1.01  --schedule                              default
% 2.49/1.01  --add_important_lit                     false
% 2.49/1.01  --prop_solver_per_cl                    1000
% 2.49/1.01  --min_unsat_core                        false
% 2.49/1.01  --soft_assumptions                      false
% 2.49/1.01  --soft_lemma_size                       3
% 2.49/1.01  --prop_impl_unit_size                   0
% 2.49/1.01  --prop_impl_unit                        []
% 2.49/1.01  --share_sel_clauses                     true
% 2.49/1.01  --reset_solvers                         false
% 2.49/1.01  --bc_imp_inh                            [conj_cone]
% 2.49/1.01  --conj_cone_tolerance                   3.
% 2.49/1.01  --extra_neg_conj                        none
% 2.49/1.01  --large_theory_mode                     true
% 2.49/1.01  --prolific_symb_bound                   200
% 2.49/1.01  --lt_threshold                          2000
% 2.49/1.01  --clause_weak_htbl                      true
% 2.49/1.01  --gc_record_bc_elim                     false
% 2.49/1.01  
% 2.49/1.01  ------ Preprocessing Options
% 2.49/1.01  
% 2.49/1.01  --preprocessing_flag                    true
% 2.49/1.01  --time_out_prep_mult                    0.1
% 2.49/1.01  --splitting_mode                        input
% 2.49/1.01  --splitting_grd                         true
% 2.49/1.01  --splitting_cvd                         false
% 2.49/1.01  --splitting_cvd_svl                     false
% 2.49/1.01  --splitting_nvd                         32
% 2.49/1.01  --sub_typing                            true
% 2.49/1.01  --prep_gs_sim                           true
% 2.49/1.01  --prep_unflatten                        true
% 2.49/1.01  --prep_res_sim                          true
% 2.49/1.01  --prep_upred                            true
% 2.49/1.01  --prep_sem_filter                       exhaustive
% 2.49/1.01  --prep_sem_filter_out                   false
% 2.49/1.01  --pred_elim                             true
% 2.49/1.01  --res_sim_input                         true
% 2.49/1.01  --eq_ax_congr_red                       true
% 2.49/1.01  --pure_diseq_elim                       true
% 2.49/1.01  --brand_transform                       false
% 2.49/1.01  --non_eq_to_eq                          false
% 2.49/1.01  --prep_def_merge                        true
% 2.49/1.01  --prep_def_merge_prop_impl              false
% 2.49/1.01  --prep_def_merge_mbd                    true
% 2.49/1.01  --prep_def_merge_tr_red                 false
% 2.49/1.01  --prep_def_merge_tr_cl                  false
% 2.49/1.01  --smt_preprocessing                     true
% 2.49/1.01  --smt_ac_axioms                         fast
% 2.49/1.01  --preprocessed_out                      false
% 2.49/1.01  --preprocessed_stats                    false
% 2.49/1.01  
% 2.49/1.01  ------ Abstraction refinement Options
% 2.49/1.01  
% 2.49/1.01  --abstr_ref                             []
% 2.49/1.01  --abstr_ref_prep                        false
% 2.49/1.01  --abstr_ref_until_sat                   false
% 2.49/1.01  --abstr_ref_sig_restrict                funpre
% 2.49/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/1.01  --abstr_ref_under                       []
% 2.49/1.01  
% 2.49/1.01  ------ SAT Options
% 2.49/1.01  
% 2.49/1.01  --sat_mode                              false
% 2.49/1.01  --sat_fm_restart_options                ""
% 2.49/1.01  --sat_gr_def                            false
% 2.49/1.01  --sat_epr_types                         true
% 2.49/1.01  --sat_non_cyclic_types                  false
% 2.49/1.01  --sat_finite_models                     false
% 2.49/1.01  --sat_fm_lemmas                         false
% 2.49/1.01  --sat_fm_prep                           false
% 2.49/1.01  --sat_fm_uc_incr                        true
% 2.49/1.01  --sat_out_model                         small
% 2.49/1.01  --sat_out_clauses                       false
% 2.49/1.01  
% 2.49/1.01  ------ QBF Options
% 2.49/1.01  
% 2.49/1.01  --qbf_mode                              false
% 2.49/1.01  --qbf_elim_univ                         false
% 2.49/1.01  --qbf_dom_inst                          none
% 2.49/1.01  --qbf_dom_pre_inst                      false
% 2.49/1.01  --qbf_sk_in                             false
% 2.49/1.01  --qbf_pred_elim                         true
% 2.49/1.01  --qbf_split                             512
% 2.49/1.01  
% 2.49/1.01  ------ BMC1 Options
% 2.49/1.01  
% 2.49/1.01  --bmc1_incremental                      false
% 2.49/1.01  --bmc1_axioms                           reachable_all
% 2.49/1.01  --bmc1_min_bound                        0
% 2.49/1.01  --bmc1_max_bound                        -1
% 2.49/1.01  --bmc1_max_bound_default                -1
% 2.49/1.01  --bmc1_symbol_reachability              true
% 2.49/1.01  --bmc1_property_lemmas                  false
% 2.49/1.01  --bmc1_k_induction                      false
% 2.49/1.01  --bmc1_non_equiv_states                 false
% 2.49/1.01  --bmc1_deadlock                         false
% 2.49/1.01  --bmc1_ucm                              false
% 2.49/1.01  --bmc1_add_unsat_core                   none
% 2.49/1.01  --bmc1_unsat_core_children              false
% 2.49/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/1.01  --bmc1_out_stat                         full
% 2.49/1.01  --bmc1_ground_init                      false
% 2.49/1.01  --bmc1_pre_inst_next_state              false
% 2.49/1.01  --bmc1_pre_inst_state                   false
% 2.49/1.01  --bmc1_pre_inst_reach_state             false
% 2.49/1.01  --bmc1_out_unsat_core                   false
% 2.49/1.01  --bmc1_aig_witness_out                  false
% 2.49/1.01  --bmc1_verbose                          false
% 2.49/1.01  --bmc1_dump_clauses_tptp                false
% 2.49/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.49/1.01  --bmc1_dump_file                        -
% 2.49/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.49/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.49/1.01  --bmc1_ucm_extend_mode                  1
% 2.49/1.01  --bmc1_ucm_init_mode                    2
% 2.49/1.01  --bmc1_ucm_cone_mode                    none
% 2.49/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.49/1.01  --bmc1_ucm_relax_model                  4
% 2.49/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.49/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/1.01  --bmc1_ucm_layered_model                none
% 2.49/1.01  --bmc1_ucm_max_lemma_size               10
% 2.49/1.01  
% 2.49/1.01  ------ AIG Options
% 2.49/1.01  
% 2.49/1.01  --aig_mode                              false
% 2.49/1.01  
% 2.49/1.01  ------ Instantiation Options
% 2.49/1.01  
% 2.49/1.01  --instantiation_flag                    true
% 2.49/1.01  --inst_sos_flag                         false
% 2.49/1.01  --inst_sos_phase                        true
% 2.49/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/1.01  --inst_lit_sel_side                     num_symb
% 2.49/1.01  --inst_solver_per_active                1400
% 2.49/1.01  --inst_solver_calls_frac                1.
% 2.49/1.01  --inst_passive_queue_type               priority_queues
% 2.49/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/1.01  --inst_passive_queues_freq              [25;2]
% 2.49/1.01  --inst_dismatching                      true
% 2.49/1.01  --inst_eager_unprocessed_to_passive     true
% 2.49/1.01  --inst_prop_sim_given                   true
% 2.49/1.01  --inst_prop_sim_new                     false
% 2.49/1.01  --inst_subs_new                         false
% 2.49/1.01  --inst_eq_res_simp                      false
% 2.49/1.01  --inst_subs_given                       false
% 2.49/1.01  --inst_orphan_elimination               true
% 2.49/1.01  --inst_learning_loop_flag               true
% 2.49/1.01  --inst_learning_start                   3000
% 2.49/1.01  --inst_learning_factor                  2
% 2.49/1.01  --inst_start_prop_sim_after_learn       3
% 2.49/1.01  --inst_sel_renew                        solver
% 2.49/1.01  --inst_lit_activity_flag                true
% 2.49/1.01  --inst_restr_to_given                   false
% 2.49/1.01  --inst_activity_threshold               500
% 2.49/1.01  --inst_out_proof                        true
% 2.49/1.01  
% 2.49/1.01  ------ Resolution Options
% 2.49/1.01  
% 2.49/1.01  --resolution_flag                       true
% 2.49/1.01  --res_lit_sel                           adaptive
% 2.49/1.01  --res_lit_sel_side                      none
% 2.49/1.01  --res_ordering                          kbo
% 2.49/1.01  --res_to_prop_solver                    active
% 2.49/1.01  --res_prop_simpl_new                    false
% 2.49/1.01  --res_prop_simpl_given                  true
% 2.49/1.01  --res_passive_queue_type                priority_queues
% 2.49/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/1.01  --res_passive_queues_freq               [15;5]
% 2.49/1.01  --res_forward_subs                      full
% 2.49/1.01  --res_backward_subs                     full
% 2.49/1.01  --res_forward_subs_resolution           true
% 2.49/1.01  --res_backward_subs_resolution          true
% 2.49/1.01  --res_orphan_elimination                true
% 2.49/1.01  --res_time_limit                        2.
% 2.49/1.01  --res_out_proof                         true
% 2.49/1.01  
% 2.49/1.01  ------ Superposition Options
% 2.49/1.01  
% 2.49/1.01  --superposition_flag                    true
% 2.49/1.01  --sup_passive_queue_type                priority_queues
% 2.49/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.49/1.01  --demod_completeness_check              fast
% 2.49/1.01  --demod_use_ground                      true
% 2.49/1.01  --sup_to_prop_solver                    passive
% 2.49/1.01  --sup_prop_simpl_new                    true
% 2.49/1.01  --sup_prop_simpl_given                  true
% 2.49/1.01  --sup_fun_splitting                     false
% 2.49/1.01  --sup_smt_interval                      50000
% 2.49/1.01  
% 2.49/1.01  ------ Superposition Simplification Setup
% 2.49/1.01  
% 2.49/1.01  --sup_indices_passive                   []
% 2.49/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.01  --sup_full_bw                           [BwDemod]
% 2.49/1.01  --sup_immed_triv                        [TrivRules]
% 2.49/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.01  --sup_immed_bw_main                     []
% 2.49/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.01  
% 2.49/1.01  ------ Combination Options
% 2.49/1.01  
% 2.49/1.01  --comb_res_mult                         3
% 2.49/1.01  --comb_sup_mult                         2
% 2.49/1.01  --comb_inst_mult                        10
% 2.49/1.01  
% 2.49/1.01  ------ Debug Options
% 2.49/1.01  
% 2.49/1.01  --dbg_backtrace                         false
% 2.49/1.01  --dbg_dump_prop_clauses                 false
% 2.49/1.01  --dbg_dump_prop_clauses_file            -
% 2.49/1.01  --dbg_out_stat                          false
% 2.49/1.01  ------ Parsing...
% 2.49/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.49/1.01  
% 2.49/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.49/1.01  
% 2.49/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.49/1.01  
% 2.49/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.49/1.01  ------ Proving...
% 2.49/1.01  ------ Problem Properties 
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  clauses                                 23
% 2.49/1.01  conjectures                             2
% 2.49/1.01  EPR                                     4
% 2.49/1.01  Horn                                    18
% 2.49/1.01  unary                                   10
% 2.49/1.01  binary                                  8
% 2.49/1.01  lits                                    42
% 2.49/1.01  lits eq                                 20
% 2.49/1.01  fd_pure                                 0
% 2.49/1.01  fd_pseudo                               0
% 2.49/1.01  fd_cond                                 0
% 2.49/1.01  fd_pseudo_cond                          3
% 2.49/1.01  AC symbols                              0
% 2.49/1.01  
% 2.49/1.01  ------ Schedule dynamic 5 is on 
% 2.49/1.01  
% 2.49/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  ------ 
% 2.49/1.01  Current options:
% 2.49/1.01  ------ 
% 2.49/1.01  
% 2.49/1.01  ------ Input Options
% 2.49/1.01  
% 2.49/1.01  --out_options                           all
% 2.49/1.01  --tptp_safe_out                         true
% 2.49/1.01  --problem_path                          ""
% 2.49/1.01  --include_path                          ""
% 2.49/1.01  --clausifier                            res/vclausify_rel
% 2.49/1.01  --clausifier_options                    --mode clausify
% 2.49/1.01  --stdin                                 false
% 2.49/1.01  --stats_out                             all
% 2.49/1.01  
% 2.49/1.01  ------ General Options
% 2.49/1.01  
% 2.49/1.01  --fof                                   false
% 2.49/1.01  --time_out_real                         305.
% 2.49/1.01  --time_out_virtual                      -1.
% 2.49/1.01  --symbol_type_check                     false
% 2.49/1.01  --clausify_out                          false
% 2.49/1.01  --sig_cnt_out                           false
% 2.49/1.01  --trig_cnt_out                          false
% 2.49/1.01  --trig_cnt_out_tolerance                1.
% 2.49/1.01  --trig_cnt_out_sk_spl                   false
% 2.49/1.01  --abstr_cl_out                          false
% 2.49/1.01  
% 2.49/1.01  ------ Global Options
% 2.49/1.01  
% 2.49/1.01  --schedule                              default
% 2.49/1.01  --add_important_lit                     false
% 2.49/1.01  --prop_solver_per_cl                    1000
% 2.49/1.01  --min_unsat_core                        false
% 2.49/1.01  --soft_assumptions                      false
% 2.49/1.01  --soft_lemma_size                       3
% 2.49/1.01  --prop_impl_unit_size                   0
% 2.49/1.01  --prop_impl_unit                        []
% 2.49/1.01  --share_sel_clauses                     true
% 2.49/1.01  --reset_solvers                         false
% 2.49/1.01  --bc_imp_inh                            [conj_cone]
% 2.49/1.01  --conj_cone_tolerance                   3.
% 2.49/1.01  --extra_neg_conj                        none
% 2.49/1.01  --large_theory_mode                     true
% 2.49/1.01  --prolific_symb_bound                   200
% 2.49/1.01  --lt_threshold                          2000
% 2.49/1.01  --clause_weak_htbl                      true
% 2.49/1.01  --gc_record_bc_elim                     false
% 2.49/1.01  
% 2.49/1.01  ------ Preprocessing Options
% 2.49/1.01  
% 2.49/1.01  --preprocessing_flag                    true
% 2.49/1.01  --time_out_prep_mult                    0.1
% 2.49/1.01  --splitting_mode                        input
% 2.49/1.01  --splitting_grd                         true
% 2.49/1.01  --splitting_cvd                         false
% 2.49/1.01  --splitting_cvd_svl                     false
% 2.49/1.01  --splitting_nvd                         32
% 2.49/1.01  --sub_typing                            true
% 2.49/1.01  --prep_gs_sim                           true
% 2.49/1.01  --prep_unflatten                        true
% 2.49/1.01  --prep_res_sim                          true
% 2.49/1.01  --prep_upred                            true
% 2.49/1.01  --prep_sem_filter                       exhaustive
% 2.49/1.01  --prep_sem_filter_out                   false
% 2.49/1.01  --pred_elim                             true
% 2.49/1.01  --res_sim_input                         true
% 2.49/1.01  --eq_ax_congr_red                       true
% 2.49/1.01  --pure_diseq_elim                       true
% 2.49/1.01  --brand_transform                       false
% 2.49/1.01  --non_eq_to_eq                          false
% 2.49/1.01  --prep_def_merge                        true
% 2.49/1.01  --prep_def_merge_prop_impl              false
% 2.49/1.01  --prep_def_merge_mbd                    true
% 2.49/1.01  --prep_def_merge_tr_red                 false
% 2.49/1.01  --prep_def_merge_tr_cl                  false
% 2.49/1.01  --smt_preprocessing                     true
% 2.49/1.01  --smt_ac_axioms                         fast
% 2.49/1.01  --preprocessed_out                      false
% 2.49/1.01  --preprocessed_stats                    false
% 2.49/1.01  
% 2.49/1.01  ------ Abstraction refinement Options
% 2.49/1.01  
% 2.49/1.01  --abstr_ref                             []
% 2.49/1.01  --abstr_ref_prep                        false
% 2.49/1.01  --abstr_ref_until_sat                   false
% 2.49/1.01  --abstr_ref_sig_restrict                funpre
% 2.49/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/1.01  --abstr_ref_under                       []
% 2.49/1.01  
% 2.49/1.01  ------ SAT Options
% 2.49/1.01  
% 2.49/1.01  --sat_mode                              false
% 2.49/1.01  --sat_fm_restart_options                ""
% 2.49/1.01  --sat_gr_def                            false
% 2.49/1.01  --sat_epr_types                         true
% 2.49/1.01  --sat_non_cyclic_types                  false
% 2.49/1.01  --sat_finite_models                     false
% 2.49/1.01  --sat_fm_lemmas                         false
% 2.49/1.01  --sat_fm_prep                           false
% 2.49/1.01  --sat_fm_uc_incr                        true
% 2.49/1.01  --sat_out_model                         small
% 2.49/1.01  --sat_out_clauses                       false
% 2.49/1.01  
% 2.49/1.01  ------ QBF Options
% 2.49/1.01  
% 2.49/1.01  --qbf_mode                              false
% 2.49/1.01  --qbf_elim_univ                         false
% 2.49/1.01  --qbf_dom_inst                          none
% 2.49/1.01  --qbf_dom_pre_inst                      false
% 2.49/1.01  --qbf_sk_in                             false
% 2.49/1.01  --qbf_pred_elim                         true
% 2.49/1.01  --qbf_split                             512
% 2.49/1.01  
% 2.49/1.01  ------ BMC1 Options
% 2.49/1.01  
% 2.49/1.01  --bmc1_incremental                      false
% 2.49/1.01  --bmc1_axioms                           reachable_all
% 2.49/1.01  --bmc1_min_bound                        0
% 2.49/1.01  --bmc1_max_bound                        -1
% 2.49/1.01  --bmc1_max_bound_default                -1
% 2.49/1.01  --bmc1_symbol_reachability              true
% 2.49/1.01  --bmc1_property_lemmas                  false
% 2.49/1.01  --bmc1_k_induction                      false
% 2.49/1.01  --bmc1_non_equiv_states                 false
% 2.49/1.01  --bmc1_deadlock                         false
% 2.49/1.01  --bmc1_ucm                              false
% 2.49/1.01  --bmc1_add_unsat_core                   none
% 2.49/1.01  --bmc1_unsat_core_children              false
% 2.49/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/1.01  --bmc1_out_stat                         full
% 2.49/1.01  --bmc1_ground_init                      false
% 2.49/1.01  --bmc1_pre_inst_next_state              false
% 2.49/1.01  --bmc1_pre_inst_state                   false
% 2.49/1.01  --bmc1_pre_inst_reach_state             false
% 2.49/1.01  --bmc1_out_unsat_core                   false
% 2.49/1.01  --bmc1_aig_witness_out                  false
% 2.49/1.01  --bmc1_verbose                          false
% 2.49/1.01  --bmc1_dump_clauses_tptp                false
% 2.49/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.49/1.01  --bmc1_dump_file                        -
% 2.49/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.49/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.49/1.01  --bmc1_ucm_extend_mode                  1
% 2.49/1.01  --bmc1_ucm_init_mode                    2
% 2.49/1.01  --bmc1_ucm_cone_mode                    none
% 2.49/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.49/1.01  --bmc1_ucm_relax_model                  4
% 2.49/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.49/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/1.01  --bmc1_ucm_layered_model                none
% 2.49/1.01  --bmc1_ucm_max_lemma_size               10
% 2.49/1.01  
% 2.49/1.01  ------ AIG Options
% 2.49/1.01  
% 2.49/1.01  --aig_mode                              false
% 2.49/1.01  
% 2.49/1.01  ------ Instantiation Options
% 2.49/1.01  
% 2.49/1.01  --instantiation_flag                    true
% 2.49/1.01  --inst_sos_flag                         false
% 2.49/1.01  --inst_sos_phase                        true
% 2.49/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/1.01  --inst_lit_sel_side                     none
% 2.49/1.01  --inst_solver_per_active                1400
% 2.49/1.01  --inst_solver_calls_frac                1.
% 2.49/1.01  --inst_passive_queue_type               priority_queues
% 2.49/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/1.01  --inst_passive_queues_freq              [25;2]
% 2.49/1.01  --inst_dismatching                      true
% 2.49/1.01  --inst_eager_unprocessed_to_passive     true
% 2.49/1.01  --inst_prop_sim_given                   true
% 2.49/1.01  --inst_prop_sim_new                     false
% 2.49/1.01  --inst_subs_new                         false
% 2.49/1.01  --inst_eq_res_simp                      false
% 2.49/1.01  --inst_subs_given                       false
% 2.49/1.01  --inst_orphan_elimination               true
% 2.49/1.01  --inst_learning_loop_flag               true
% 2.49/1.01  --inst_learning_start                   3000
% 2.49/1.01  --inst_learning_factor                  2
% 2.49/1.01  --inst_start_prop_sim_after_learn       3
% 2.49/1.01  --inst_sel_renew                        solver
% 2.49/1.01  --inst_lit_activity_flag                true
% 2.49/1.01  --inst_restr_to_given                   false
% 2.49/1.01  --inst_activity_threshold               500
% 2.49/1.01  --inst_out_proof                        true
% 2.49/1.01  
% 2.49/1.01  ------ Resolution Options
% 2.49/1.01  
% 2.49/1.01  --resolution_flag                       false
% 2.49/1.01  --res_lit_sel                           adaptive
% 2.49/1.01  --res_lit_sel_side                      none
% 2.49/1.01  --res_ordering                          kbo
% 2.49/1.01  --res_to_prop_solver                    active
% 2.49/1.01  --res_prop_simpl_new                    false
% 2.49/1.01  --res_prop_simpl_given                  true
% 2.49/1.01  --res_passive_queue_type                priority_queues
% 2.49/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/1.01  --res_passive_queues_freq               [15;5]
% 2.49/1.01  --res_forward_subs                      full
% 2.49/1.01  --res_backward_subs                     full
% 2.49/1.01  --res_forward_subs_resolution           true
% 2.49/1.01  --res_backward_subs_resolution          true
% 2.49/1.01  --res_orphan_elimination                true
% 2.49/1.01  --res_time_limit                        2.
% 2.49/1.01  --res_out_proof                         true
% 2.49/1.01  
% 2.49/1.01  ------ Superposition Options
% 2.49/1.01  
% 2.49/1.01  --superposition_flag                    true
% 2.49/1.01  --sup_passive_queue_type                priority_queues
% 2.49/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.49/1.01  --demod_completeness_check              fast
% 2.49/1.01  --demod_use_ground                      true
% 2.49/1.01  --sup_to_prop_solver                    passive
% 2.49/1.01  --sup_prop_simpl_new                    true
% 2.49/1.01  --sup_prop_simpl_given                  true
% 2.49/1.01  --sup_fun_splitting                     false
% 2.49/1.01  --sup_smt_interval                      50000
% 2.49/1.01  
% 2.49/1.01  ------ Superposition Simplification Setup
% 2.49/1.01  
% 2.49/1.01  --sup_indices_passive                   []
% 2.49/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.01  --sup_full_bw                           [BwDemod]
% 2.49/1.01  --sup_immed_triv                        [TrivRules]
% 2.49/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.01  --sup_immed_bw_main                     []
% 2.49/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.01  
% 2.49/1.01  ------ Combination Options
% 2.49/1.01  
% 2.49/1.01  --comb_res_mult                         3
% 2.49/1.01  --comb_sup_mult                         2
% 2.49/1.01  --comb_inst_mult                        10
% 2.49/1.01  
% 2.49/1.01  ------ Debug Options
% 2.49/1.01  
% 2.49/1.01  --dbg_backtrace                         false
% 2.49/1.01  --dbg_dump_prop_clauses                 false
% 2.49/1.01  --dbg_dump_prop_clauses_file            -
% 2.49/1.01  --dbg_out_stat                          false
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  ------ Proving...
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  % SZS status Theorem for theBenchmark.p
% 2.49/1.01  
% 2.49/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.49/1.01  
% 2.49/1.01  fof(f12,axiom,(
% 2.49/1.01    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f32,plain,(
% 2.49/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.49/1.01    inference(nnf_transformation,[],[f12])).
% 2.49/1.01  
% 2.49/1.01  fof(f33,plain,(
% 2.49/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.49/1.01    inference(flattening,[],[f32])).
% 2.49/1.01  
% 2.49/1.01  fof(f34,plain,(
% 2.49/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.49/1.01    inference(rectify,[],[f33])).
% 2.49/1.01  
% 2.49/1.01  fof(f35,plain,(
% 2.49/1.01    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.49/1.01    introduced(choice_axiom,[])).
% 2.49/1.01  
% 2.49/1.01  fof(f36,plain,(
% 2.49/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 2.49/1.01  
% 2.49/1.01  fof(f55,plain,(
% 2.49/1.01    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.49/1.01    inference(cnf_transformation,[],[f36])).
% 2.49/1.01  
% 2.49/1.01  fof(f14,axiom,(
% 2.49/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f62,plain,(
% 2.49/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f14])).
% 2.49/1.01  
% 2.49/1.01  fof(f15,axiom,(
% 2.49/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f63,plain,(
% 2.49/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f15])).
% 2.49/1.01  
% 2.49/1.01  fof(f16,axiom,(
% 2.49/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f64,plain,(
% 2.49/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f16])).
% 2.49/1.01  
% 2.49/1.01  fof(f71,plain,(
% 2.49/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.49/1.01    inference(definition_unfolding,[],[f63,f64])).
% 2.49/1.01  
% 2.49/1.01  fof(f72,plain,(
% 2.49/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.49/1.01    inference(definition_unfolding,[],[f62,f71])).
% 2.49/1.01  
% 2.49/1.01  fof(f80,plain,(
% 2.49/1.01    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 2.49/1.01    inference(definition_unfolding,[],[f55,f72])).
% 2.49/1.01  
% 2.49/1.01  fof(f88,plain,(
% 2.49/1.01    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X1))) )),
% 2.49/1.01    inference(equality_resolution,[],[f80])).
% 2.49/1.01  
% 2.49/1.01  fof(f6,axiom,(
% 2.49/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f25,plain,(
% 2.49/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.49/1.01    inference(ennf_transformation,[],[f6])).
% 2.49/1.01  
% 2.49/1.01  fof(f49,plain,(
% 2.49/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f25])).
% 2.49/1.01  
% 2.49/1.01  fof(f18,conjecture,(
% 2.49/1.01    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 2.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f19,negated_conjecture,(
% 2.49/1.01    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 2.49/1.01    inference(negated_conjecture,[],[f18])).
% 2.49/1.01  
% 2.49/1.01  fof(f26,plain,(
% 2.49/1.01    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 2.49/1.01    inference(ennf_transformation,[],[f19])).
% 2.49/1.01  
% 2.49/1.01  fof(f38,plain,(
% 2.49/1.01    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK3 != sK5 & sK3 != sK4 & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5)))),
% 2.49/1.01    introduced(choice_axiom,[])).
% 2.49/1.01  
% 2.49/1.01  fof(f39,plain,(
% 2.49/1.01    sK3 != sK5 & sK3 != sK4 & r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5))),
% 2.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f26,f38])).
% 2.49/1.01  
% 2.49/1.01  fof(f67,plain,(
% 2.49/1.01    r1_tarski(k1_tarski(sK3),k2_tarski(sK4,sK5))),
% 2.49/1.01    inference(cnf_transformation,[],[f39])).
% 2.49/1.01  
% 2.49/1.01  fof(f13,axiom,(
% 2.49/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f61,plain,(
% 2.49/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f13])).
% 2.49/1.01  
% 2.49/1.01  fof(f73,plain,(
% 2.49/1.01    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.49/1.01    inference(definition_unfolding,[],[f61,f72])).
% 2.49/1.01  
% 2.49/1.01  fof(f83,plain,(
% 2.49/1.01    r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5))),
% 2.49/1.01    inference(definition_unfolding,[],[f67,f73,f72])).
% 2.49/1.01  
% 2.49/1.01  fof(f4,axiom,(
% 2.49/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f22,plain,(
% 2.49/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.49/1.01    inference(rectify,[],[f4])).
% 2.49/1.01  
% 2.49/1.01  fof(f24,plain,(
% 2.49/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.49/1.01    inference(ennf_transformation,[],[f22])).
% 2.49/1.01  
% 2.49/1.01  fof(f30,plain,(
% 2.49/1.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 2.49/1.01    introduced(choice_axiom,[])).
% 2.49/1.01  
% 2.49/1.01  fof(f31,plain,(
% 2.49/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f30])).
% 2.49/1.01  
% 2.49/1.01  fof(f46,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f31])).
% 2.49/1.01  
% 2.49/1.01  fof(f57,plain,(
% 2.49/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.49/1.01    inference(cnf_transformation,[],[f36])).
% 2.49/1.01  
% 2.49/1.01  fof(f78,plain,(
% 2.49/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 2.49/1.01    inference(definition_unfolding,[],[f57,f72])).
% 2.49/1.01  
% 2.49/1.01  fof(f84,plain,(
% 2.49/1.01    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k3_enumset1(X0,X0,X0,X0,X4) != X2) )),
% 2.49/1.01    inference(equality_resolution,[],[f78])).
% 2.49/1.01  
% 2.49/1.01  fof(f85,plain,(
% 2.49/1.01    ( ! [X4,X0] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X4))) )),
% 2.49/1.01    inference(equality_resolution,[],[f84])).
% 2.49/1.01  
% 2.49/1.01  fof(f2,axiom,(
% 2.49/1.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f20,plain,(
% 2.49/1.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.49/1.01    inference(rectify,[],[f2])).
% 2.49/1.01  
% 2.49/1.01  fof(f42,plain,(
% 2.49/1.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.49/1.01    inference(cnf_transformation,[],[f20])).
% 2.49/1.01  
% 2.49/1.01  fof(f47,plain,(
% 2.49/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.49/1.01    inference(cnf_transformation,[],[f31])).
% 2.49/1.01  
% 2.49/1.01  fof(f17,axiom,(
% 2.49/1.01    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f37,plain,(
% 2.49/1.01    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 2.49/1.01    inference(nnf_transformation,[],[f17])).
% 2.49/1.01  
% 2.49/1.01  fof(f66,plain,(
% 2.49/1.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f37])).
% 2.49/1.01  
% 2.49/1.01  fof(f5,axiom,(
% 2.49/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f48,plain,(
% 2.49/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.49/1.01    inference(cnf_transformation,[],[f5])).
% 2.49/1.01  
% 2.49/1.01  fof(f81,plain,(
% 2.49/1.01    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) | ~r2_hidden(X0,X1)) )),
% 2.49/1.01    inference(definition_unfolding,[],[f66,f48,f73])).
% 2.49/1.01  
% 2.49/1.01  fof(f8,axiom,(
% 2.49/1.01    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f51,plain,(
% 2.49/1.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.49/1.01    inference(cnf_transformation,[],[f8])).
% 2.49/1.01  
% 2.49/1.01  fof(f11,axiom,(
% 2.49/1.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f54,plain,(
% 2.49/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f11])).
% 2.49/1.01  
% 2.49/1.01  fof(f70,plain,(
% 2.49/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 2.49/1.01    inference(definition_unfolding,[],[f54,f48])).
% 2.49/1.01  
% 2.49/1.01  fof(f74,plain,(
% 2.49/1.01    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 2.49/1.01    inference(definition_unfolding,[],[f51,f48,f70])).
% 2.49/1.01  
% 2.49/1.01  fof(f9,axiom,(
% 2.49/1.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.49/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f52,plain,(
% 2.49/1.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.49/1.01    inference(cnf_transformation,[],[f9])).
% 2.49/1.01  
% 2.49/1.01  fof(f65,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f37])).
% 2.49/1.01  
% 2.49/1.01  fof(f82,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1))) )),
% 2.49/1.01    inference(definition_unfolding,[],[f65,f48,f73])).
% 2.49/1.01  
% 2.49/1.01  fof(f69,plain,(
% 2.49/1.01    sK3 != sK5),
% 2.49/1.01    inference(cnf_transformation,[],[f39])).
% 2.49/1.01  
% 2.49/1.01  fof(f68,plain,(
% 2.49/1.01    sK3 != sK4),
% 2.49/1.01    inference(cnf_transformation,[],[f39])).
% 2.49/1.01  
% 2.49/1.01  cnf(c_18,plain,
% 2.49/1.01      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 2.49/1.01      inference(cnf_transformation,[],[f88]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2042,plain,
% 2.49/1.01      ( ~ r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,X1))
% 2.49/1.01      | X0 = X1
% 2.49/1.01      | X0 = sK4 ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3546,plain,
% 2.49/1.01      ( ~ r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK5))
% 2.49/1.01      | sK3 = sK4
% 2.49/1.01      | sK3 = sK5 ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_2042]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_8,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.49/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_23,negated_conjecture,
% 2.49/1.01      ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
% 2.49/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_256,plain,
% 2.49/1.01      ( k3_enumset1(sK4,sK4,sK4,sK4,sK5) != X0
% 2.49/1.01      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != X1
% 2.49/1.01      | k3_xboole_0(X1,X0) = X1 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_23]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_257,plain,
% 2.49/1.01      ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_256]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_7,plain,
% 2.49/1.01      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 2.49/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1188,plain,
% 2.49/1.01      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) = iProver_top
% 2.49/1.01      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2986,plain,
% 2.49/1.01      ( r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 2.49/1.01      | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_257,c_1188]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_16,plain,
% 2.49/1.01      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X0)) ),
% 2.49/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1487,plain,
% 2.49/1.01      ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1488,plain,
% 2.49/1.01      ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_1487]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_778,plain,
% 2.49/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.49/1.01      theory(equality) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1319,plain,
% 2.49/1.01      ( r2_hidden(X0,X1)
% 2.49/1.01      | ~ r2_hidden(X2,k3_enumset1(X3,X3,X3,X3,X2))
% 2.49/1.01      | X0 != X2
% 2.49/1.01      | X1 != k3_enumset1(X3,X3,X3,X3,X2) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_778]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1447,plain,
% 2.49/1.01      ( r2_hidden(X0,k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)))
% 2.49/1.01      | ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 2.49/1.01      | X0 != sK3
% 2.49/1.01      | k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1319]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1966,plain,
% 2.49/1.01      ( r2_hidden(k3_xboole_0(sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)))
% 2.49/1.01      | ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 2.49/1.01      | k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 2.49/1.01      | k3_xboole_0(sK3,sK3) != sK3 ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1447]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1968,plain,
% 2.49/1.01      ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 2.49/1.01      | k3_xboole_0(sK3,sK3) != sK3
% 2.49/1.01      | r2_hidden(k3_xboole_0(sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5))) = iProver_top
% 2.49/1.01      | r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_1966]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2,plain,
% 2.49/1.01      ( k3_xboole_0(X0,X0) = X0 ),
% 2.49/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1967,plain,
% 2.49/1.01      ( k3_xboole_0(sK3,sK3) = sK3 ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_6,plain,
% 2.49/1.01      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 2.49/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2871,plain,
% 2.49/1.01      ( ~ r2_hidden(k3_xboole_0(sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)))
% 2.49/1.01      | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2872,plain,
% 2.49/1.01      ( r2_hidden(k3_xboole_0(sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5))) != iProver_top
% 2.49/1.01      | r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_2871]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3242,plain,
% 2.49/1.01      ( r2_hidden(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_2986,c_257,c_1488,c_1968,c_1967,c_2872]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_19,plain,
% 2.49/1.01      ( ~ r2_hidden(X0,X1)
% 2.49/1.01      | k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) = k1_xboole_0 ),
% 2.49/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1180,plain,
% 2.49/1.01      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) = k1_xboole_0
% 2.49/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3247,plain,
% 2.49/1.01      ( k5_xboole_0(k3_enumset1(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5))),k3_xboole_0(k3_enumset1(sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5)),sK1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK5))),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k1_xboole_0 ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_3242,c_1180]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_10,plain,
% 2.49/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 2.49/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3249,plain,
% 2.49/1.01      ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_xboole_0))) = k1_xboole_0 ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_3247,c_10]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_11,plain,
% 2.49/1.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.49/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3252,plain,
% 2.49/1.01      ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0 ),
% 2.49/1.01      inference(demodulation,[status(thm)],[c_3249,c_2,c_11]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_20,plain,
% 2.49/1.01      ( r2_hidden(X0,X1)
% 2.49/1.01      | k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) != k1_xboole_0 ),
% 2.49/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1179,plain,
% 2.49/1.01      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) != k1_xboole_0
% 2.49/1.01      | r2_hidden(X0,X1) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1519,plain,
% 2.49/1.01      ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != k1_xboole_0
% 2.49/1.01      | r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_257,c_1179]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1531,plain,
% 2.49/1.01      ( r2_hidden(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK5))
% 2.49/1.01      | k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != k1_xboole_0 ),
% 2.49/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1519]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_21,negated_conjecture,
% 2.49/1.01      ( sK3 != sK5 ),
% 2.49/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_22,negated_conjecture,
% 2.49/1.01      ( sK3 != sK4 ),
% 2.49/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(contradiction,plain,
% 2.49/1.01      ( $false ),
% 2.49/1.01      inference(minisat,[status(thm)],[c_3546,c_3252,c_1531,c_21,c_22]) ).
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.49/1.01  
% 2.49/1.01  ------                               Statistics
% 2.49/1.01  
% 2.49/1.01  ------ General
% 2.49/1.01  
% 2.49/1.01  abstr_ref_over_cycles:                  0
% 2.49/1.01  abstr_ref_under_cycles:                 0
% 2.49/1.01  gc_basic_clause_elim:                   0
% 2.49/1.01  forced_gc_time:                         0
% 2.49/1.01  parsing_time:                           0.009
% 2.49/1.01  unif_index_cands_time:                  0.
% 2.49/1.01  unif_index_add_time:                    0.
% 2.49/1.01  orderings_time:                         0.
% 2.49/1.01  out_proof_time:                         0.016
% 2.49/1.01  total_time:                             0.114
% 2.49/1.01  num_of_symbols:                         44
% 2.49/1.01  num_of_terms:                           4226
% 2.49/1.01  
% 2.49/1.01  ------ Preprocessing
% 2.49/1.01  
% 2.49/1.01  num_of_splits:                          0
% 2.49/1.01  num_of_split_atoms:                     0
% 2.49/1.01  num_of_reused_defs:                     0
% 2.49/1.01  num_eq_ax_congr_red:                    24
% 2.49/1.01  num_of_sem_filtered_clauses:            1
% 2.49/1.01  num_of_subtypes:                        0
% 2.49/1.01  monotx_restored_types:                  0
% 2.49/1.01  sat_num_of_epr_types:                   0
% 2.49/1.01  sat_num_of_non_cyclic_types:            0
% 2.49/1.01  sat_guarded_non_collapsed_types:        0
% 2.49/1.01  num_pure_diseq_elim:                    0
% 2.49/1.01  simp_replaced_by:                       0
% 2.49/1.01  res_preprocessed:                       108
% 2.49/1.01  prep_upred:                             0
% 2.49/1.01  prep_unflattend:                        46
% 2.49/1.01  smt_new_axioms:                         0
% 2.49/1.01  pred_elim_cands:                        2
% 2.49/1.01  pred_elim:                              1
% 2.49/1.01  pred_elim_cl:                           1
% 2.49/1.01  pred_elim_cycles:                       3
% 2.49/1.01  merged_defs:                            16
% 2.49/1.01  merged_defs_ncl:                        0
% 2.49/1.01  bin_hyper_res:                          16
% 2.49/1.01  prep_cycles:                            4
% 2.49/1.01  pred_elim_time:                         0.003
% 2.49/1.01  splitting_time:                         0.
% 2.49/1.01  sem_filter_time:                        0.
% 2.49/1.01  monotx_time:                            0.
% 2.49/1.01  subtype_inf_time:                       0.
% 2.49/1.01  
% 2.49/1.01  ------ Problem properties
% 2.49/1.01  
% 2.49/1.01  clauses:                                23
% 2.49/1.01  conjectures:                            2
% 2.49/1.01  epr:                                    4
% 2.49/1.01  horn:                                   18
% 2.49/1.01  ground:                                 3
% 2.49/1.01  unary:                                  10
% 2.49/1.01  binary:                                 8
% 2.49/1.01  lits:                                   42
% 2.49/1.01  lits_eq:                                20
% 2.49/1.01  fd_pure:                                0
% 2.49/1.01  fd_pseudo:                              0
% 2.49/1.01  fd_cond:                                0
% 2.49/1.01  fd_pseudo_cond:                         3
% 2.49/1.01  ac_symbols:                             0
% 2.49/1.01  
% 2.49/1.01  ------ Propositional Solver
% 2.49/1.01  
% 2.49/1.01  prop_solver_calls:                      26
% 2.49/1.01  prop_fast_solver_calls:                 535
% 2.49/1.01  smt_solver_calls:                       0
% 2.49/1.01  smt_fast_solver_calls:                  0
% 2.49/1.01  prop_num_of_clauses:                    1269
% 2.49/1.01  prop_preprocess_simplified:             5401
% 2.49/1.01  prop_fo_subsumed:                       1
% 2.49/1.01  prop_solver_time:                       0.
% 2.49/1.01  smt_solver_time:                        0.
% 2.49/1.01  smt_fast_solver_time:                   0.
% 2.49/1.01  prop_fast_solver_time:                  0.
% 2.49/1.01  prop_unsat_core_time:                   0.
% 2.49/1.01  
% 2.49/1.01  ------ QBF
% 2.49/1.01  
% 2.49/1.01  qbf_q_res:                              0
% 2.49/1.01  qbf_num_tautologies:                    0
% 2.49/1.01  qbf_prep_cycles:                        0
% 2.49/1.01  
% 2.49/1.01  ------ BMC1
% 2.49/1.01  
% 2.49/1.01  bmc1_current_bound:                     -1
% 2.49/1.01  bmc1_last_solved_bound:                 -1
% 2.49/1.01  bmc1_unsat_core_size:                   -1
% 2.49/1.01  bmc1_unsat_core_parents_size:           -1
% 2.49/1.01  bmc1_merge_next_fun:                    0
% 2.49/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.49/1.01  
% 2.49/1.01  ------ Instantiation
% 2.49/1.01  
% 2.49/1.01  inst_num_of_clauses:                    431
% 2.49/1.01  inst_num_in_passive:                    134
% 2.49/1.01  inst_num_in_active:                     153
% 2.49/1.01  inst_num_in_unprocessed:                143
% 2.49/1.01  inst_num_of_loops:                      159
% 2.49/1.01  inst_num_of_learning_restarts:          0
% 2.49/1.01  inst_num_moves_active_passive:          4
% 2.49/1.01  inst_lit_activity:                      0
% 2.49/1.01  inst_lit_activity_moves:                0
% 2.49/1.01  inst_num_tautologies:                   0
% 2.49/1.01  inst_num_prop_implied:                  0
% 2.49/1.01  inst_num_existing_simplified:           0
% 2.49/1.01  inst_num_eq_res_simplified:             0
% 2.49/1.01  inst_num_child_elim:                    0
% 2.49/1.01  inst_num_of_dismatching_blockings:      84
% 2.49/1.01  inst_num_of_non_proper_insts:           394
% 2.49/1.01  inst_num_of_duplicates:                 0
% 2.49/1.01  inst_inst_num_from_inst_to_res:         0
% 2.49/1.01  inst_dismatching_checking_time:         0.
% 2.49/1.01  
% 2.49/1.01  ------ Resolution
% 2.49/1.01  
% 2.49/1.01  res_num_of_clauses:                     0
% 2.49/1.01  res_num_in_passive:                     0
% 2.49/1.01  res_num_in_active:                      0
% 2.49/1.01  res_num_of_loops:                       112
% 2.49/1.01  res_forward_subset_subsumed:            45
% 2.49/1.01  res_backward_subset_subsumed:           0
% 2.49/1.01  res_forward_subsumed:                   0
% 2.49/1.01  res_backward_subsumed:                  0
% 2.49/1.01  res_forward_subsumption_resolution:     0
% 2.49/1.01  res_backward_subsumption_resolution:    0
% 2.49/1.01  res_clause_to_clause_subsumption:       135
% 2.49/1.01  res_orphan_elimination:                 0
% 2.49/1.01  res_tautology_del:                      51
% 2.49/1.01  res_num_eq_res_simplified:              0
% 2.49/1.01  res_num_sel_changes:                    0
% 2.49/1.01  res_moves_from_active_to_pass:          0
% 2.49/1.01  
% 2.49/1.01  ------ Superposition
% 2.49/1.01  
% 2.49/1.01  sup_time_total:                         0.
% 2.49/1.01  sup_time_generating:                    0.
% 2.49/1.01  sup_time_sim_full:                      0.
% 2.49/1.01  sup_time_sim_immed:                     0.
% 2.49/1.01  
% 2.49/1.01  sup_num_of_clauses:                     44
% 2.49/1.01  sup_num_in_active:                      27
% 2.49/1.01  sup_num_in_passive:                     17
% 2.49/1.01  sup_num_of_loops:                       30
% 2.49/1.01  sup_fw_superposition:                   36
% 2.49/1.01  sup_bw_superposition:                   23
% 2.49/1.01  sup_immediate_simplified:               21
% 2.49/1.01  sup_given_eliminated:                   0
% 2.49/1.01  comparisons_done:                       0
% 2.49/1.01  comparisons_avoided:                    0
% 2.49/1.01  
% 2.49/1.01  ------ Simplifications
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  sim_fw_subset_subsumed:                 1
% 2.49/1.01  sim_bw_subset_subsumed:                 0
% 2.49/1.01  sim_fw_subsumed:                        3
% 2.49/1.01  sim_bw_subsumed:                        0
% 2.49/1.01  sim_fw_subsumption_res:                 0
% 2.49/1.01  sim_bw_subsumption_res:                 0
% 2.49/1.01  sim_tautology_del:                      0
% 2.49/1.01  sim_eq_tautology_del:                   8
% 2.49/1.01  sim_eq_res_simp:                        1
% 2.49/1.01  sim_fw_demodulated:                     15
% 2.49/1.01  sim_bw_demodulated:                     3
% 2.49/1.01  sim_light_normalised:                   2
% 2.49/1.01  sim_joinable_taut:                      0
% 2.49/1.01  sim_joinable_simp:                      0
% 2.49/1.01  sim_ac_normalised:                      0
% 2.49/1.01  sim_smt_subsumption:                    0
% 2.49/1.01  
%------------------------------------------------------------------------------
