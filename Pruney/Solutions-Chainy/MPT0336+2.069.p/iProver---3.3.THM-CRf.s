%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:45 EST 2020

% Result     : Theorem 43.75s
% Output     : CNFRefutation 43.75s
% Verified   : 
% Statistics : Number of formulae       :  218 (57706 expanded)
%              Number of clauses        :  158 (20646 expanded)
%              Number of leaves         :   18 (12973 expanded)
%              Depth                    :   38
%              Number of atoms          :  331 (123565 expanded)
%              Number of equality atoms :  194 (42285 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :   11 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f23])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
      & r1_xboole_0(sK3,sK2)
      & r2_hidden(sK4,sK3)
      & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    & r1_xboole_0(sK3,sK2)
    & r2_hidden(sK4,sK3)
    & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f30])).

fof(f54,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

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

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f67,plain,(
    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f54,f42,f59])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f42,f42])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f53,f59])).

fof(f55,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f26])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f39,f42,f42,f42,f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_757,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_770,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3958,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_757,c_770])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_13,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_765,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1519,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_765])).

cnf(c_4100,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3958,c_1519])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_763,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4515,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_4100,c_763])).

cnf(c_19,negated_conjecture,
    ( r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_759,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_774,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2035,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_759,c_774])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_762,plain,
    ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_758,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_773,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4617,plain,
    ( r2_hidden(sK4,X0) != iProver_top
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_758,c_773])).

cnf(c_5087,plain,
    ( k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4)) = X0
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_762,c_4617])).

cnf(c_5274,plain,
    ( k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)) = sK2 ),
    inference(superposition,[status(thm)],[c_2035,c_5087])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4112,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_3958,c_7])).

cnf(c_5276,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_5274,c_4112])).

cnf(c_2176,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_2035,c_763])).

cnf(c_2275,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_2176,c_0])).

cnf(c_1778,plain,
    ( k4_xboole_0(sK3,sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_759,c_763])).

cnf(c_2276,plain,
    ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK3,sK3) ),
    inference(light_normalisation,[status(thm)],[c_2275,c_1778])).

cnf(c_5277,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK3,sK3))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_5276,c_2276])).

cnf(c_2274,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2176,c_1519])).

cnf(c_2277,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,sK3),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2274,c_1778])).

cnf(c_2381,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,sK3),sK2) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_2277,c_763])).

cnf(c_3484,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK3))),k4_xboole_0(sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2381,c_1519])).

cnf(c_2380,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2277,c_774])).

cnf(c_3473,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_2380,c_763])).

cnf(c_3492,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK3,sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3484,c_2276,c_3473])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_775,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4079,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK3,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3492,c_775])).

cnf(c_2046,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k4_xboole_0(sK3,sK3),X0)) ),
    inference(superposition,[status(thm)],[c_1778,c_7])).

cnf(c_3487,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)))) = k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_2381,c_2046])).

cnf(c_3488,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK3,sK3)) = k4_xboole_0(sK3,sK3) ),
    inference(light_normalisation,[status(thm)],[c_3487,c_1778,c_2276,c_3473])).

cnf(c_4080,plain,
    ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4079,c_3488])).

cnf(c_5278,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_5277,c_4080])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_776,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4699,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k1_xboole_0
    | r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4112,c_776])).

cnf(c_5589,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4080,c_2276])).

cnf(c_4099,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3958,c_765])).

cnf(c_4377,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4099,c_775])).

cnf(c_4380,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4377,c_3958])).

cnf(c_1647,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_6995,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_4380,c_1647])).

cnf(c_4078,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2380,c_775])).

cnf(c_4081,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4078,c_4080])).

cnf(c_9,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_769,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4098,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3958,c_769])).

cnf(c_4213,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_4098,c_770])).

cnf(c_1650,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_4073,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_765,c_775])).

cnf(c_1777,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_765,c_763])).

cnf(c_4086,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4073,c_1777])).

cnf(c_4214,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_4213,c_1650,c_4086])).

cnf(c_7184,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_6995,c_4081,c_4214,c_4380,c_5278])).

cnf(c_7185,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7184,c_4086,c_5278])).

cnf(c_44954,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4699,c_5274,c_5278,c_5589,c_7185])).

cnf(c_44955,plain,
    ( r1_xboole_0(sK1,k1_xboole_0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_44954])).

cnf(c_44959,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
    inference(superposition,[status(thm)],[c_44955,c_763])).

cnf(c_45538,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)))) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_4515,c_4515,c_5278,c_44959])).

cnf(c_23941,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_1777])).

cnf(c_24498,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(X1,X0)) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(superposition,[status(thm)],[c_1777,c_23941])).

cnf(c_24011,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1777,c_0])).

cnf(c_24213,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24011,c_4086])).

cnf(c_24806,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_24498,c_24213])).

cnf(c_24807,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24806,c_1777,c_4086])).

cnf(c_2034,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_765,c_774])).

cnf(c_36742,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2034,c_763])).

cnf(c_45539,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_45538,c_7185,c_24807,c_36742])).

cnf(c_1639,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_5727,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_1778,c_1639])).

cnf(c_5854,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_5727,c_4080])).

cnf(c_1666,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(superposition,[status(thm)],[c_7,c_7])).

cnf(c_15515,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)),k4_xboole_0(sK2,sK3)))))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_5854,c_1666])).

cnf(c_1660,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_765])).

cnf(c_12428,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)),k4_xboole_0(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5854,c_1660])).

cnf(c_12587,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12428,c_2176,c_4081,c_5589])).

cnf(c_13539,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12587,c_775])).

cnf(c_13541,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2)) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12587,c_763])).

cnf(c_13542,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13539,c_13541])).

cnf(c_15734,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_15515,c_2176,c_4081,c_5589,c_13542])).

cnf(c_1653,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_10263,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(sK3,sK2),X0)))) = k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,sK2)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,sK2)),X0)) ),
    inference(superposition,[status(thm)],[c_2176,c_1653])).

cnf(c_1687,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1519])).

cnf(c_4921,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1778,c_1687])).

cnf(c_2049,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1778,c_769])).

cnf(c_3963,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2049,c_770])).

cnf(c_4941,plain,
    ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4921,c_2176,c_2276,c_3963,c_4080])).

cnf(c_6447,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) = sK3 ),
    inference(superposition,[status(thm)],[c_4941,c_763])).

cnf(c_10462,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_10263,c_1778,c_5589,c_6447])).

cnf(c_23960,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) ),
    inference(superposition,[status(thm)],[c_10462,c_1777])).

cnf(c_24269,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_23960,c_10462])).

cnf(c_1661,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X3)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(superposition,[status(thm)],[c_7,c_7])).

cnf(c_1667,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X3)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))) ),
    inference(demodulation,[status(thm)],[c_1661,c_7])).

cnf(c_27648,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X1)),k4_xboole_0(sK3,k4_xboole_0(sK3,X1))))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X1)),k4_xboole_0(sK3,k4_xboole_0(sK3,X1))))),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X1)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X1)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X1))),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X1))),X2)))))) ),
    inference(superposition,[status(thm)],[c_24269,c_1667])).

cnf(c_5583,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4080,c_3488])).

cnf(c_11343,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10462,c_1519])).

cnf(c_13786,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11343,c_775])).

cnf(c_13788,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_11343,c_763])).

cnf(c_13789,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13786,c_13788])).

cnf(c_11333,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(sK3,k4_xboole_0(sK3,X1)))) = k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_10462,c_1650])).

cnf(c_5819,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X3)))))) ),
    inference(superposition,[status(thm)],[c_1639,c_1639])).

cnf(c_11428,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,X1)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_11333,c_1650,c_5819,c_10462])).

cnf(c_20703,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X2)) = k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X1)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_11428,c_1650])).

cnf(c_20761,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) ),
    inference(superposition,[status(thm)],[c_11428,c_1667])).

cnf(c_21037,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) ),
    inference(demodulation,[status(thm)],[c_20703,c_20761])).

cnf(c_27751,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X1))),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X1))),k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_27648,c_1650,c_5583,c_13789,c_21037,c_24807])).

cnf(c_27752,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,X1),k4_xboole_0(k4_xboole_0(sK3,X1),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_27751,c_21037])).

cnf(c_5719,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_0,c_1639])).

cnf(c_25156,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X3)))))) ),
    inference(superposition,[status(thm)],[c_1653,c_5719])).

cnf(c_24445,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_0,c_23941])).

cnf(c_3957,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_769,c_770])).

cnf(c_4930,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1687,c_763])).

cnf(c_24887,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_24445,c_3957,c_4930])).

cnf(c_25805,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3)))))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,k4_xboole_0(X0,X3)))) ),
    inference(light_normalisation,[status(thm)],[c_25156,c_24887])).

cnf(c_27753,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_27752,c_10462,c_25805])).

cnf(c_28106,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(sK3,sK2),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k1_xboole_0))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15734,c_27753])).

cnf(c_28629,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k1_xboole_0))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_28106,c_1778])).

cnf(c_4694,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_776])).

cnf(c_28955,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k1_xboole_0))),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_28629,c_4694])).

cnf(c_6622,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) ),
    inference(superposition,[status(thm)],[c_5589,c_7])).

cnf(c_1779,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1519,c_763])).

cnf(c_29258,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_1779])).

cnf(c_29663,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_29258,c_3957,c_4930,c_24887])).

cnf(c_30697,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_6622,c_29663])).

cnf(c_30807,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k1_xboole_0))) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_30697,c_0])).

cnf(c_31370,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28955,c_30807])).

cnf(c_31374,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_31370])).

cnf(c_33680,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_31374,c_5087])).

cnf(c_34395,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_0,c_33680])).

cnf(c_42210,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK2)))) ),
    inference(superposition,[status(thm)],[c_34395,c_7])).

cnf(c_138226,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k1_xboole_0))),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_45539,c_42210])).

cnf(c_139755,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)))) ),
    inference(light_normalisation,[status(thm)],[c_138226,c_5278,c_44959])).

cnf(c_31412,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_31370,c_5087])).

cnf(c_139756,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_139755,c_29663,c_31412,c_44959,c_45539])).

cnf(c_1711,plain,
    ( r1_xboole_0(sK2,sK1)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1058,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_872,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))
    | ~ r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_817,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    | ~ r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_18,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_139756,c_1711,c_1058,c_872,c_817,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:58:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.18/0.34  % Running in FOF mode
% 43.75/6.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.75/6.01  
% 43.75/6.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.75/6.01  
% 43.75/6.01  ------  iProver source info
% 43.75/6.01  
% 43.75/6.01  git: date: 2020-06-30 10:37:57 +0100
% 43.75/6.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.75/6.01  git: non_committed_changes: false
% 43.75/6.01  git: last_make_outside_of_git: false
% 43.75/6.01  
% 43.75/6.01  ------ 
% 43.75/6.01  
% 43.75/6.01  ------ Input Options
% 43.75/6.01  
% 43.75/6.01  --out_options                           all
% 43.75/6.01  --tptp_safe_out                         true
% 43.75/6.01  --problem_path                          ""
% 43.75/6.01  --include_path                          ""
% 43.75/6.01  --clausifier                            res/vclausify_rel
% 43.75/6.01  --clausifier_options                    ""
% 43.75/6.01  --stdin                                 false
% 43.75/6.01  --stats_out                             all
% 43.75/6.01  
% 43.75/6.01  ------ General Options
% 43.75/6.01  
% 43.75/6.01  --fof                                   false
% 43.75/6.01  --time_out_real                         305.
% 43.75/6.01  --time_out_virtual                      -1.
% 43.75/6.01  --symbol_type_check                     false
% 43.75/6.01  --clausify_out                          false
% 43.75/6.01  --sig_cnt_out                           false
% 43.75/6.01  --trig_cnt_out                          false
% 43.75/6.01  --trig_cnt_out_tolerance                1.
% 43.75/6.01  --trig_cnt_out_sk_spl                   false
% 43.75/6.01  --abstr_cl_out                          false
% 43.75/6.01  
% 43.75/6.01  ------ Global Options
% 43.75/6.01  
% 43.75/6.01  --schedule                              default
% 43.75/6.01  --add_important_lit                     false
% 43.75/6.01  --prop_solver_per_cl                    1000
% 43.75/6.01  --min_unsat_core                        false
% 43.75/6.01  --soft_assumptions                      false
% 43.75/6.01  --soft_lemma_size                       3
% 43.75/6.01  --prop_impl_unit_size                   0
% 43.75/6.01  --prop_impl_unit                        []
% 43.75/6.01  --share_sel_clauses                     true
% 43.75/6.01  --reset_solvers                         false
% 43.75/6.01  --bc_imp_inh                            [conj_cone]
% 43.75/6.01  --conj_cone_tolerance                   3.
% 43.75/6.01  --extra_neg_conj                        none
% 43.75/6.01  --large_theory_mode                     true
% 43.75/6.01  --prolific_symb_bound                   200
% 43.75/6.01  --lt_threshold                          2000
% 43.75/6.01  --clause_weak_htbl                      true
% 43.75/6.01  --gc_record_bc_elim                     false
% 43.75/6.01  
% 43.75/6.01  ------ Preprocessing Options
% 43.75/6.01  
% 43.75/6.01  --preprocessing_flag                    true
% 43.75/6.01  --time_out_prep_mult                    0.1
% 43.75/6.01  --splitting_mode                        input
% 43.75/6.01  --splitting_grd                         true
% 43.75/6.01  --splitting_cvd                         false
% 43.75/6.01  --splitting_cvd_svl                     false
% 43.75/6.01  --splitting_nvd                         32
% 43.75/6.01  --sub_typing                            true
% 43.75/6.01  --prep_gs_sim                           true
% 43.75/6.01  --prep_unflatten                        true
% 43.75/6.01  --prep_res_sim                          true
% 43.75/6.01  --prep_upred                            true
% 43.75/6.01  --prep_sem_filter                       exhaustive
% 43.75/6.01  --prep_sem_filter_out                   false
% 43.75/6.01  --pred_elim                             true
% 43.75/6.01  --res_sim_input                         true
% 43.75/6.01  --eq_ax_congr_red                       true
% 43.75/6.01  --pure_diseq_elim                       true
% 43.75/6.01  --brand_transform                       false
% 43.75/6.01  --non_eq_to_eq                          false
% 43.75/6.01  --prep_def_merge                        true
% 43.75/6.01  --prep_def_merge_prop_impl              false
% 43.75/6.01  --prep_def_merge_mbd                    true
% 43.75/6.01  --prep_def_merge_tr_red                 false
% 43.75/6.01  --prep_def_merge_tr_cl                  false
% 43.75/6.01  --smt_preprocessing                     true
% 43.75/6.01  --smt_ac_axioms                         fast
% 43.75/6.01  --preprocessed_out                      false
% 43.75/6.01  --preprocessed_stats                    false
% 43.75/6.01  
% 43.75/6.01  ------ Abstraction refinement Options
% 43.75/6.01  
% 43.75/6.01  --abstr_ref                             []
% 43.75/6.01  --abstr_ref_prep                        false
% 43.75/6.01  --abstr_ref_until_sat                   false
% 43.75/6.01  --abstr_ref_sig_restrict                funpre
% 43.75/6.01  --abstr_ref_af_restrict_to_split_sk     false
% 43.75/6.01  --abstr_ref_under                       []
% 43.75/6.01  
% 43.75/6.01  ------ SAT Options
% 43.75/6.01  
% 43.75/6.01  --sat_mode                              false
% 43.75/6.01  --sat_fm_restart_options                ""
% 43.75/6.01  --sat_gr_def                            false
% 43.75/6.01  --sat_epr_types                         true
% 43.75/6.01  --sat_non_cyclic_types                  false
% 43.75/6.01  --sat_finite_models                     false
% 43.75/6.01  --sat_fm_lemmas                         false
% 43.75/6.01  --sat_fm_prep                           false
% 43.75/6.01  --sat_fm_uc_incr                        true
% 43.75/6.01  --sat_out_model                         small
% 43.75/6.01  --sat_out_clauses                       false
% 43.75/6.01  
% 43.75/6.01  ------ QBF Options
% 43.75/6.01  
% 43.75/6.01  --qbf_mode                              false
% 43.75/6.01  --qbf_elim_univ                         false
% 43.75/6.01  --qbf_dom_inst                          none
% 43.75/6.01  --qbf_dom_pre_inst                      false
% 43.75/6.01  --qbf_sk_in                             false
% 43.75/6.01  --qbf_pred_elim                         true
% 43.75/6.01  --qbf_split                             512
% 43.75/6.01  
% 43.75/6.01  ------ BMC1 Options
% 43.75/6.01  
% 43.75/6.01  --bmc1_incremental                      false
% 43.75/6.01  --bmc1_axioms                           reachable_all
% 43.75/6.01  --bmc1_min_bound                        0
% 43.75/6.01  --bmc1_max_bound                        -1
% 43.75/6.01  --bmc1_max_bound_default                -1
% 43.75/6.01  --bmc1_symbol_reachability              true
% 43.75/6.01  --bmc1_property_lemmas                  false
% 43.75/6.01  --bmc1_k_induction                      false
% 43.75/6.01  --bmc1_non_equiv_states                 false
% 43.75/6.01  --bmc1_deadlock                         false
% 43.75/6.01  --bmc1_ucm                              false
% 43.75/6.01  --bmc1_add_unsat_core                   none
% 43.75/6.01  --bmc1_unsat_core_children              false
% 43.75/6.01  --bmc1_unsat_core_extrapolate_axioms    false
% 43.75/6.01  --bmc1_out_stat                         full
% 43.75/6.01  --bmc1_ground_init                      false
% 43.75/6.01  --bmc1_pre_inst_next_state              false
% 43.75/6.01  --bmc1_pre_inst_state                   false
% 43.75/6.01  --bmc1_pre_inst_reach_state             false
% 43.75/6.01  --bmc1_out_unsat_core                   false
% 43.75/6.01  --bmc1_aig_witness_out                  false
% 43.75/6.01  --bmc1_verbose                          false
% 43.75/6.01  --bmc1_dump_clauses_tptp                false
% 43.75/6.01  --bmc1_dump_unsat_core_tptp             false
% 43.75/6.01  --bmc1_dump_file                        -
% 43.75/6.01  --bmc1_ucm_expand_uc_limit              128
% 43.75/6.01  --bmc1_ucm_n_expand_iterations          6
% 43.75/6.01  --bmc1_ucm_extend_mode                  1
% 43.75/6.01  --bmc1_ucm_init_mode                    2
% 43.75/6.01  --bmc1_ucm_cone_mode                    none
% 43.75/6.01  --bmc1_ucm_reduced_relation_type        0
% 43.75/6.01  --bmc1_ucm_relax_model                  4
% 43.75/6.01  --bmc1_ucm_full_tr_after_sat            true
% 43.75/6.01  --bmc1_ucm_expand_neg_assumptions       false
% 43.75/6.01  --bmc1_ucm_layered_model                none
% 43.75/6.01  --bmc1_ucm_max_lemma_size               10
% 43.75/6.01  
% 43.75/6.01  ------ AIG Options
% 43.75/6.01  
% 43.75/6.01  --aig_mode                              false
% 43.75/6.01  
% 43.75/6.01  ------ Instantiation Options
% 43.75/6.01  
% 43.75/6.01  --instantiation_flag                    true
% 43.75/6.01  --inst_sos_flag                         true
% 43.75/6.01  --inst_sos_phase                        true
% 43.75/6.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.75/6.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.75/6.01  --inst_lit_sel_side                     num_symb
% 43.75/6.01  --inst_solver_per_active                1400
% 43.75/6.01  --inst_solver_calls_frac                1.
% 43.75/6.01  --inst_passive_queue_type               priority_queues
% 43.75/6.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.75/6.01  --inst_passive_queues_freq              [25;2]
% 43.75/6.01  --inst_dismatching                      true
% 43.75/6.01  --inst_eager_unprocessed_to_passive     true
% 43.75/6.01  --inst_prop_sim_given                   true
% 43.75/6.01  --inst_prop_sim_new                     false
% 43.75/6.01  --inst_subs_new                         false
% 43.75/6.01  --inst_eq_res_simp                      false
% 43.75/6.01  --inst_subs_given                       false
% 43.75/6.01  --inst_orphan_elimination               true
% 43.75/6.01  --inst_learning_loop_flag               true
% 43.75/6.01  --inst_learning_start                   3000
% 43.75/6.01  --inst_learning_factor                  2
% 43.75/6.01  --inst_start_prop_sim_after_learn       3
% 43.75/6.01  --inst_sel_renew                        solver
% 43.75/6.01  --inst_lit_activity_flag                true
% 43.75/6.01  --inst_restr_to_given                   false
% 43.75/6.01  --inst_activity_threshold               500
% 43.75/6.01  --inst_out_proof                        true
% 43.75/6.01  
% 43.75/6.01  ------ Resolution Options
% 43.75/6.01  
% 43.75/6.01  --resolution_flag                       true
% 43.75/6.01  --res_lit_sel                           adaptive
% 43.75/6.01  --res_lit_sel_side                      none
% 43.75/6.01  --res_ordering                          kbo
% 43.75/6.01  --res_to_prop_solver                    active
% 43.75/6.01  --res_prop_simpl_new                    false
% 43.75/6.01  --res_prop_simpl_given                  true
% 43.75/6.01  --res_passive_queue_type                priority_queues
% 43.75/6.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.75/6.01  --res_passive_queues_freq               [15;5]
% 43.75/6.01  --res_forward_subs                      full
% 43.75/6.01  --res_backward_subs                     full
% 43.75/6.01  --res_forward_subs_resolution           true
% 43.75/6.01  --res_backward_subs_resolution          true
% 43.75/6.01  --res_orphan_elimination                true
% 43.75/6.01  --res_time_limit                        2.
% 43.75/6.01  --res_out_proof                         true
% 43.75/6.01  
% 43.75/6.01  ------ Superposition Options
% 43.75/6.01  
% 43.75/6.01  --superposition_flag                    true
% 43.75/6.01  --sup_passive_queue_type                priority_queues
% 43.75/6.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.75/6.01  --sup_passive_queues_freq               [8;1;4]
% 43.75/6.01  --demod_completeness_check              fast
% 43.75/6.01  --demod_use_ground                      true
% 43.75/6.01  --sup_to_prop_solver                    passive
% 43.75/6.01  --sup_prop_simpl_new                    true
% 43.75/6.01  --sup_prop_simpl_given                  true
% 43.75/6.01  --sup_fun_splitting                     true
% 43.75/6.01  --sup_smt_interval                      50000
% 43.75/6.01  
% 43.75/6.01  ------ Superposition Simplification Setup
% 43.75/6.01  
% 43.75/6.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.75/6.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.75/6.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.75/6.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.75/6.01  --sup_full_triv                         [TrivRules;PropSubs]
% 43.75/6.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.75/6.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.75/6.01  --sup_immed_triv                        [TrivRules]
% 43.75/6.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.75/6.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.75/6.01  --sup_immed_bw_main                     []
% 43.75/6.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.75/6.01  --sup_input_triv                        [Unflattening;TrivRules]
% 43.75/6.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.75/6.01  --sup_input_bw                          []
% 43.75/6.01  
% 43.75/6.01  ------ Combination Options
% 43.75/6.01  
% 43.75/6.01  --comb_res_mult                         3
% 43.75/6.01  --comb_sup_mult                         2
% 43.75/6.01  --comb_inst_mult                        10
% 43.75/6.01  
% 43.75/6.01  ------ Debug Options
% 43.75/6.01  
% 43.75/6.01  --dbg_backtrace                         false
% 43.75/6.01  --dbg_dump_prop_clauses                 false
% 43.75/6.01  --dbg_dump_prop_clauses_file            -
% 43.75/6.01  --dbg_out_stat                          false
% 43.75/6.01  ------ Parsing...
% 43.75/6.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.75/6.01  
% 43.75/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 43.75/6.01  
% 43.75/6.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.75/6.01  
% 43.75/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.75/6.01  ------ Proving...
% 43.75/6.01  ------ Problem Properties 
% 43.75/6.01  
% 43.75/6.01  
% 43.75/6.01  clauses                                 22
% 43.75/6.01  conjectures                             4
% 43.75/6.01  EPR                                     4
% 43.75/6.01  Horn                                    19
% 43.75/6.01  unary                                   8
% 43.75/6.01  binary                                  12
% 43.75/6.01  lits                                    38
% 43.75/6.01  lits eq                                 9
% 43.75/6.01  fd_pure                                 0
% 43.75/6.01  fd_pseudo                               0
% 43.75/6.01  fd_cond                                 0
% 43.75/6.01  fd_pseudo_cond                          0
% 43.75/6.01  AC symbols                              0
% 43.75/6.01  
% 43.75/6.01  ------ Schedule dynamic 5 is on 
% 43.75/6.01  
% 43.75/6.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 43.75/6.01  
% 43.75/6.01  
% 43.75/6.01  ------ 
% 43.75/6.01  Current options:
% 43.75/6.01  ------ 
% 43.75/6.01  
% 43.75/6.01  ------ Input Options
% 43.75/6.01  
% 43.75/6.01  --out_options                           all
% 43.75/6.01  --tptp_safe_out                         true
% 43.75/6.01  --problem_path                          ""
% 43.75/6.01  --include_path                          ""
% 43.75/6.01  --clausifier                            res/vclausify_rel
% 43.75/6.01  --clausifier_options                    ""
% 43.75/6.01  --stdin                                 false
% 43.75/6.01  --stats_out                             all
% 43.75/6.01  
% 43.75/6.01  ------ General Options
% 43.75/6.01  
% 43.75/6.01  --fof                                   false
% 43.75/6.01  --time_out_real                         305.
% 43.75/6.01  --time_out_virtual                      -1.
% 43.75/6.01  --symbol_type_check                     false
% 43.75/6.01  --clausify_out                          false
% 43.75/6.01  --sig_cnt_out                           false
% 43.75/6.01  --trig_cnt_out                          false
% 43.75/6.01  --trig_cnt_out_tolerance                1.
% 43.75/6.01  --trig_cnt_out_sk_spl                   false
% 43.75/6.01  --abstr_cl_out                          false
% 43.75/6.01  
% 43.75/6.01  ------ Global Options
% 43.75/6.01  
% 43.75/6.01  --schedule                              default
% 43.75/6.01  --add_important_lit                     false
% 43.75/6.01  --prop_solver_per_cl                    1000
% 43.75/6.01  --min_unsat_core                        false
% 43.75/6.01  --soft_assumptions                      false
% 43.75/6.01  --soft_lemma_size                       3
% 43.75/6.01  --prop_impl_unit_size                   0
% 43.75/6.01  --prop_impl_unit                        []
% 43.75/6.01  --share_sel_clauses                     true
% 43.75/6.01  --reset_solvers                         false
% 43.75/6.01  --bc_imp_inh                            [conj_cone]
% 43.75/6.01  --conj_cone_tolerance                   3.
% 43.75/6.01  --extra_neg_conj                        none
% 43.75/6.01  --large_theory_mode                     true
% 43.75/6.01  --prolific_symb_bound                   200
% 43.75/6.01  --lt_threshold                          2000
% 43.75/6.01  --clause_weak_htbl                      true
% 43.75/6.01  --gc_record_bc_elim                     false
% 43.75/6.01  
% 43.75/6.01  ------ Preprocessing Options
% 43.75/6.01  
% 43.75/6.01  --preprocessing_flag                    true
% 43.75/6.01  --time_out_prep_mult                    0.1
% 43.75/6.01  --splitting_mode                        input
% 43.75/6.01  --splitting_grd                         true
% 43.75/6.01  --splitting_cvd                         false
% 43.75/6.01  --splitting_cvd_svl                     false
% 43.75/6.01  --splitting_nvd                         32
% 43.75/6.01  --sub_typing                            true
% 43.75/6.01  --prep_gs_sim                           true
% 43.75/6.01  --prep_unflatten                        true
% 43.75/6.01  --prep_res_sim                          true
% 43.75/6.01  --prep_upred                            true
% 43.75/6.01  --prep_sem_filter                       exhaustive
% 43.75/6.01  --prep_sem_filter_out                   false
% 43.75/6.01  --pred_elim                             true
% 43.75/6.01  --res_sim_input                         true
% 43.75/6.01  --eq_ax_congr_red                       true
% 43.75/6.01  --pure_diseq_elim                       true
% 43.75/6.01  --brand_transform                       false
% 43.75/6.01  --non_eq_to_eq                          false
% 43.75/6.01  --prep_def_merge                        true
% 43.75/6.01  --prep_def_merge_prop_impl              false
% 43.75/6.01  --prep_def_merge_mbd                    true
% 43.75/6.01  --prep_def_merge_tr_red                 false
% 43.75/6.01  --prep_def_merge_tr_cl                  false
% 43.75/6.01  --smt_preprocessing                     true
% 43.75/6.01  --smt_ac_axioms                         fast
% 43.75/6.01  --preprocessed_out                      false
% 43.75/6.01  --preprocessed_stats                    false
% 43.75/6.01  
% 43.75/6.01  ------ Abstraction refinement Options
% 43.75/6.01  
% 43.75/6.01  --abstr_ref                             []
% 43.75/6.01  --abstr_ref_prep                        false
% 43.75/6.01  --abstr_ref_until_sat                   false
% 43.75/6.01  --abstr_ref_sig_restrict                funpre
% 43.75/6.01  --abstr_ref_af_restrict_to_split_sk     false
% 43.75/6.01  --abstr_ref_under                       []
% 43.75/6.01  
% 43.75/6.01  ------ SAT Options
% 43.75/6.01  
% 43.75/6.01  --sat_mode                              false
% 43.75/6.01  --sat_fm_restart_options                ""
% 43.75/6.01  --sat_gr_def                            false
% 43.75/6.01  --sat_epr_types                         true
% 43.75/6.01  --sat_non_cyclic_types                  false
% 43.75/6.01  --sat_finite_models                     false
% 43.75/6.01  --sat_fm_lemmas                         false
% 43.75/6.01  --sat_fm_prep                           false
% 43.75/6.01  --sat_fm_uc_incr                        true
% 43.75/6.01  --sat_out_model                         small
% 43.75/6.01  --sat_out_clauses                       false
% 43.75/6.01  
% 43.75/6.01  ------ QBF Options
% 43.75/6.01  
% 43.75/6.01  --qbf_mode                              false
% 43.75/6.01  --qbf_elim_univ                         false
% 43.75/6.01  --qbf_dom_inst                          none
% 43.75/6.01  --qbf_dom_pre_inst                      false
% 43.75/6.01  --qbf_sk_in                             false
% 43.75/6.01  --qbf_pred_elim                         true
% 43.75/6.01  --qbf_split                             512
% 43.75/6.01  
% 43.75/6.01  ------ BMC1 Options
% 43.75/6.01  
% 43.75/6.01  --bmc1_incremental                      false
% 43.75/6.01  --bmc1_axioms                           reachable_all
% 43.75/6.01  --bmc1_min_bound                        0
% 43.75/6.01  --bmc1_max_bound                        -1
% 43.75/6.01  --bmc1_max_bound_default                -1
% 43.75/6.01  --bmc1_symbol_reachability              true
% 43.75/6.01  --bmc1_property_lemmas                  false
% 43.75/6.01  --bmc1_k_induction                      false
% 43.75/6.01  --bmc1_non_equiv_states                 false
% 43.75/6.01  --bmc1_deadlock                         false
% 43.75/6.01  --bmc1_ucm                              false
% 43.75/6.01  --bmc1_add_unsat_core                   none
% 43.75/6.01  --bmc1_unsat_core_children              false
% 43.75/6.01  --bmc1_unsat_core_extrapolate_axioms    false
% 43.75/6.01  --bmc1_out_stat                         full
% 43.75/6.01  --bmc1_ground_init                      false
% 43.75/6.01  --bmc1_pre_inst_next_state              false
% 43.75/6.01  --bmc1_pre_inst_state                   false
% 43.75/6.01  --bmc1_pre_inst_reach_state             false
% 43.75/6.01  --bmc1_out_unsat_core                   false
% 43.75/6.01  --bmc1_aig_witness_out                  false
% 43.75/6.01  --bmc1_verbose                          false
% 43.75/6.01  --bmc1_dump_clauses_tptp                false
% 43.75/6.01  --bmc1_dump_unsat_core_tptp             false
% 43.75/6.01  --bmc1_dump_file                        -
% 43.75/6.01  --bmc1_ucm_expand_uc_limit              128
% 43.75/6.01  --bmc1_ucm_n_expand_iterations          6
% 43.75/6.01  --bmc1_ucm_extend_mode                  1
% 43.75/6.01  --bmc1_ucm_init_mode                    2
% 43.75/6.01  --bmc1_ucm_cone_mode                    none
% 43.75/6.01  --bmc1_ucm_reduced_relation_type        0
% 43.75/6.01  --bmc1_ucm_relax_model                  4
% 43.75/6.01  --bmc1_ucm_full_tr_after_sat            true
% 43.75/6.01  --bmc1_ucm_expand_neg_assumptions       false
% 43.75/6.01  --bmc1_ucm_layered_model                none
% 43.75/6.01  --bmc1_ucm_max_lemma_size               10
% 43.75/6.01  
% 43.75/6.01  ------ AIG Options
% 43.75/6.01  
% 43.75/6.01  --aig_mode                              false
% 43.75/6.01  
% 43.75/6.01  ------ Instantiation Options
% 43.75/6.01  
% 43.75/6.01  --instantiation_flag                    true
% 43.75/6.01  --inst_sos_flag                         true
% 43.75/6.01  --inst_sos_phase                        true
% 43.75/6.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.75/6.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.75/6.01  --inst_lit_sel_side                     none
% 43.75/6.01  --inst_solver_per_active                1400
% 43.75/6.01  --inst_solver_calls_frac                1.
% 43.75/6.01  --inst_passive_queue_type               priority_queues
% 43.75/6.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.75/6.01  --inst_passive_queues_freq              [25;2]
% 43.75/6.01  --inst_dismatching                      true
% 43.75/6.01  --inst_eager_unprocessed_to_passive     true
% 43.75/6.01  --inst_prop_sim_given                   true
% 43.75/6.01  --inst_prop_sim_new                     false
% 43.75/6.01  --inst_subs_new                         false
% 43.75/6.01  --inst_eq_res_simp                      false
% 43.75/6.01  --inst_subs_given                       false
% 43.75/6.01  --inst_orphan_elimination               true
% 43.75/6.01  --inst_learning_loop_flag               true
% 43.75/6.01  --inst_learning_start                   3000
% 43.75/6.01  --inst_learning_factor                  2
% 43.75/6.01  --inst_start_prop_sim_after_learn       3
% 43.75/6.01  --inst_sel_renew                        solver
% 43.75/6.01  --inst_lit_activity_flag                true
% 43.75/6.01  --inst_restr_to_given                   false
% 43.75/6.01  --inst_activity_threshold               500
% 43.75/6.01  --inst_out_proof                        true
% 43.75/6.01  
% 43.75/6.01  ------ Resolution Options
% 43.75/6.01  
% 43.75/6.01  --resolution_flag                       false
% 43.75/6.01  --res_lit_sel                           adaptive
% 43.75/6.01  --res_lit_sel_side                      none
% 43.75/6.01  --res_ordering                          kbo
% 43.75/6.01  --res_to_prop_solver                    active
% 43.75/6.01  --res_prop_simpl_new                    false
% 43.75/6.01  --res_prop_simpl_given                  true
% 43.75/6.01  --res_passive_queue_type                priority_queues
% 43.75/6.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.75/6.01  --res_passive_queues_freq               [15;5]
% 43.75/6.01  --res_forward_subs                      full
% 43.75/6.01  --res_backward_subs                     full
% 43.75/6.01  --res_forward_subs_resolution           true
% 43.75/6.01  --res_backward_subs_resolution          true
% 43.75/6.01  --res_orphan_elimination                true
% 43.75/6.01  --res_time_limit                        2.
% 43.75/6.01  --res_out_proof                         true
% 43.75/6.01  
% 43.75/6.01  ------ Superposition Options
% 43.75/6.01  
% 43.75/6.01  --superposition_flag                    true
% 43.75/6.01  --sup_passive_queue_type                priority_queues
% 43.75/6.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.75/6.01  --sup_passive_queues_freq               [8;1;4]
% 43.75/6.01  --demod_completeness_check              fast
% 43.75/6.01  --demod_use_ground                      true
% 43.75/6.01  --sup_to_prop_solver                    passive
% 43.75/6.01  --sup_prop_simpl_new                    true
% 43.75/6.01  --sup_prop_simpl_given                  true
% 43.75/6.01  --sup_fun_splitting                     true
% 43.75/6.01  --sup_smt_interval                      50000
% 43.75/6.01  
% 43.75/6.01  ------ Superposition Simplification Setup
% 43.75/6.01  
% 43.75/6.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.75/6.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.75/6.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.75/6.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.75/6.01  --sup_full_triv                         [TrivRules;PropSubs]
% 43.75/6.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.75/6.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.75/6.01  --sup_immed_triv                        [TrivRules]
% 43.75/6.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.75/6.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.75/6.01  --sup_immed_bw_main                     []
% 43.75/6.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.75/6.01  --sup_input_triv                        [Unflattening;TrivRules]
% 43.75/6.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.75/6.01  --sup_input_bw                          []
% 43.75/6.01  
% 43.75/6.01  ------ Combination Options
% 43.75/6.01  
% 43.75/6.01  --comb_res_mult                         3
% 43.75/6.01  --comb_sup_mult                         2
% 43.75/6.01  --comb_inst_mult                        10
% 43.75/6.01  
% 43.75/6.01  ------ Debug Options
% 43.75/6.01  
% 43.75/6.01  --dbg_backtrace                         false
% 43.75/6.01  --dbg_dump_prop_clauses                 false
% 43.75/6.01  --dbg_dump_prop_clauses_file            -
% 43.75/6.01  --dbg_out_stat                          false
% 43.75/6.01  
% 43.75/6.01  
% 43.75/6.01  
% 43.75/6.01  
% 43.75/6.01  ------ Proving...
% 43.75/6.01  
% 43.75/6.01  
% 43.75/6.01  % SZS status Theorem for theBenchmark.p
% 43.75/6.01  
% 43.75/6.01  % SZS output start CNFRefutation for theBenchmark.p
% 43.75/6.01  
% 43.75/6.01  fof(f16,conjecture,(
% 43.75/6.01    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 43.75/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.75/6.01  
% 43.75/6.01  fof(f17,negated_conjecture,(
% 43.75/6.01    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 43.75/6.01    inference(negated_conjecture,[],[f16])).
% 43.75/6.01  
% 43.75/6.01  fof(f23,plain,(
% 43.75/6.01    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 43.75/6.01    inference(ennf_transformation,[],[f17])).
% 43.75/6.01  
% 43.75/6.01  fof(f24,plain,(
% 43.75/6.01    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 43.75/6.01    inference(flattening,[],[f23])).
% 43.75/6.01  
% 43.75/6.01  fof(f30,plain,(
% 43.75/6.01    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)))),
% 43.75/6.01    introduced(choice_axiom,[])).
% 43.75/6.01  
% 43.75/6.01  fof(f31,plain,(
% 43.75/6.01    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 43.75/6.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f30])).
% 43.75/6.01  
% 43.75/6.01  fof(f54,plain,(
% 43.75/6.01    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 43.75/6.01    inference(cnf_transformation,[],[f31])).
% 43.75/6.01  
% 43.75/6.01  fof(f8,axiom,(
% 43.75/6.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 43.75/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.75/6.01  
% 43.75/6.01  fof(f42,plain,(
% 43.75/6.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 43.75/6.01    inference(cnf_transformation,[],[f8])).
% 43.75/6.01  
% 43.75/6.01  fof(f12,axiom,(
% 43.75/6.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 43.75/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.75/6.01  
% 43.75/6.01  fof(f49,plain,(
% 43.75/6.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 43.75/6.01    inference(cnf_transformation,[],[f12])).
% 43.75/6.01  
% 43.75/6.01  fof(f13,axiom,(
% 43.75/6.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 43.75/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.75/6.01  
% 43.75/6.01  fof(f50,plain,(
% 43.75/6.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 43.75/6.01    inference(cnf_transformation,[],[f13])).
% 43.75/6.01  
% 43.75/6.01  fof(f14,axiom,(
% 43.75/6.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 43.75/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.75/6.01  
% 43.75/6.01  fof(f51,plain,(
% 43.75/6.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 43.75/6.01    inference(cnf_transformation,[],[f14])).
% 43.75/6.01  
% 43.75/6.01  fof(f58,plain,(
% 43.75/6.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 43.75/6.01    inference(definition_unfolding,[],[f50,f51])).
% 43.75/6.01  
% 43.75/6.01  fof(f59,plain,(
% 43.75/6.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 43.75/6.01    inference(definition_unfolding,[],[f49,f58])).
% 43.75/6.01  
% 43.75/6.01  fof(f67,plain,(
% 43.75/6.01    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))),
% 43.75/6.01    inference(definition_unfolding,[],[f54,f42,f59])).
% 43.75/6.01  
% 43.75/6.01  fof(f6,axiom,(
% 43.75/6.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 43.75/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.75/6.01  
% 43.75/6.01  fof(f21,plain,(
% 43.75/6.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 43.75/6.01    inference(ennf_transformation,[],[f6])).
% 43.75/6.01  
% 43.75/6.01  fof(f40,plain,(
% 43.75/6.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 43.75/6.01    inference(cnf_transformation,[],[f21])).
% 43.75/6.01  
% 43.75/6.01  fof(f64,plain,(
% 43.75/6.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 43.75/6.01    inference(definition_unfolding,[],[f40,f42])).
% 43.75/6.01  
% 43.75/6.01  fof(f1,axiom,(
% 43.75/6.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 43.75/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.75/6.01  
% 43.75/6.01  fof(f32,plain,(
% 43.75/6.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 43.75/6.01    inference(cnf_transformation,[],[f1])).
% 43.75/6.01  
% 43.75/6.01  fof(f60,plain,(
% 43.75/6.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 43.75/6.01    inference(definition_unfolding,[],[f32,f42,f42])).
% 43.75/6.01  
% 43.75/6.01  fof(f10,axiom,(
% 43.75/6.01    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 43.75/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.75/6.01  
% 43.75/6.01  fof(f46,plain,(
% 43.75/6.01    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 43.75/6.01    inference(cnf_transformation,[],[f10])).
% 43.75/6.01  
% 43.75/6.01  fof(f11,axiom,(
% 43.75/6.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 43.75/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.75/6.01  
% 43.75/6.01  fof(f28,plain,(
% 43.75/6.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 43.75/6.01    inference(nnf_transformation,[],[f11])).
% 43.75/6.01  
% 43.75/6.01  fof(f47,plain,(
% 43.75/6.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 43.75/6.01    inference(cnf_transformation,[],[f28])).
% 43.75/6.01  
% 43.75/6.01  fof(f56,plain,(
% 43.75/6.01    r1_xboole_0(sK3,sK2)),
% 43.75/6.01    inference(cnf_transformation,[],[f31])).
% 43.75/6.01  
% 43.75/6.01  fof(f3,axiom,(
% 43.75/6.01    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 43.75/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.75/6.01  
% 43.75/6.01  fof(f19,plain,(
% 43.75/6.01    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 43.75/6.01    inference(ennf_transformation,[],[f3])).
% 43.75/6.01  
% 43.75/6.01  fof(f35,plain,(
% 43.75/6.01    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 43.75/6.01    inference(cnf_transformation,[],[f19])).
% 43.75/6.01  
% 43.75/6.01  fof(f15,axiom,(
% 43.75/6.01    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 43.75/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.75/6.01  
% 43.75/6.01  fof(f29,plain,(
% 43.75/6.01    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 43.75/6.01    inference(nnf_transformation,[],[f15])).
% 43.75/6.01  
% 43.75/6.01  fof(f53,plain,(
% 43.75/6.01    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 43.75/6.01    inference(cnf_transformation,[],[f29])).
% 43.75/6.01  
% 43.75/6.01  fof(f65,plain,(
% 43.75/6.01    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 43.75/6.01    inference(definition_unfolding,[],[f53,f59])).
% 43.75/6.01  
% 43.75/6.01  fof(f55,plain,(
% 43.75/6.01    r2_hidden(sK4,sK3)),
% 43.75/6.01    inference(cnf_transformation,[],[f31])).
% 43.75/6.01  
% 43.75/6.01  fof(f4,axiom,(
% 43.75/6.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 43.75/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.75/6.01  
% 43.75/6.01  fof(f18,plain,(
% 43.75/6.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 43.75/6.01    inference(rectify,[],[f4])).
% 43.75/6.01  
% 43.75/6.01  fof(f20,plain,(
% 43.75/6.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 43.75/6.01    inference(ennf_transformation,[],[f18])).
% 43.75/6.01  
% 43.75/6.01  fof(f26,plain,(
% 43.75/6.01    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 43.75/6.01    introduced(choice_axiom,[])).
% 43.75/6.01  
% 43.75/6.01  fof(f27,plain,(
% 43.75/6.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 43.75/6.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f26])).
% 43.75/6.01  
% 43.75/6.01  fof(f38,plain,(
% 43.75/6.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 43.75/6.01    inference(cnf_transformation,[],[f27])).
% 43.75/6.01  
% 43.75/6.01  fof(f5,axiom,(
% 43.75/6.01    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 43.75/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.75/6.01  
% 43.75/6.01  fof(f39,plain,(
% 43.75/6.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 43.75/6.01    inference(cnf_transformation,[],[f5])).
% 43.75/6.01  
% 43.75/6.01  fof(f63,plain,(
% 43.75/6.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 43.75/6.01    inference(definition_unfolding,[],[f39,f42,f42,f42,f42])).
% 43.75/6.01  
% 43.75/6.01  fof(f2,axiom,(
% 43.75/6.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 43.75/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.75/6.01  
% 43.75/6.01  fof(f25,plain,(
% 43.75/6.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 43.75/6.01    inference(nnf_transformation,[],[f2])).
% 43.75/6.01  
% 43.75/6.01  fof(f33,plain,(
% 43.75/6.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 43.75/6.01    inference(cnf_transformation,[],[f25])).
% 43.75/6.01  
% 43.75/6.01  fof(f62,plain,(
% 43.75/6.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 43.75/6.01    inference(definition_unfolding,[],[f33,f42])).
% 43.75/6.01  
% 43.75/6.01  fof(f34,plain,(
% 43.75/6.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 43.75/6.01    inference(cnf_transformation,[],[f25])).
% 43.75/6.01  
% 43.75/6.01  fof(f61,plain,(
% 43.75/6.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 43.75/6.01    inference(definition_unfolding,[],[f34,f42])).
% 43.75/6.01  
% 43.75/6.01  fof(f7,axiom,(
% 43.75/6.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 43.75/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.75/6.01  
% 43.75/6.01  fof(f41,plain,(
% 43.75/6.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 43.75/6.01    inference(cnf_transformation,[],[f7])).
% 43.75/6.01  
% 43.75/6.01  fof(f9,axiom,(
% 43.75/6.01    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 43.75/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.75/6.01  
% 43.75/6.01  fof(f22,plain,(
% 43.75/6.01    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 43.75/6.01    inference(ennf_transformation,[],[f9])).
% 43.75/6.01  
% 43.75/6.01  fof(f43,plain,(
% 43.75/6.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 43.75/6.01    inference(cnf_transformation,[],[f22])).
% 43.75/6.01  
% 43.75/6.01  fof(f57,plain,(
% 43.75/6.01    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 43.75/6.01    inference(cnf_transformation,[],[f31])).
% 43.75/6.01  
% 43.75/6.01  cnf(c_21,negated_conjecture,
% 43.75/6.01      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 43.75/6.01      inference(cnf_transformation,[],[f67]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_757,plain,
% 43.75/6.01      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 43.75/6.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_8,plain,
% 43.75/6.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 43.75/6.01      inference(cnf_transformation,[],[f64]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_770,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 43.75/6.01      | r1_tarski(X0,X1) != iProver_top ),
% 43.75/6.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_3958,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_757,c_770]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_0,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 43.75/6.01      inference(cnf_transformation,[],[f60]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_13,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 43.75/6.01      inference(cnf_transformation,[],[f46]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_765,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 43.75/6.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_1519,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_0,c_765]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4100,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_3958,c_1519]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_15,plain,
% 43.75/6.01      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 43.75/6.01      inference(cnf_transformation,[],[f47]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_763,plain,
% 43.75/6.01      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 43.75/6.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4515,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_4100,c_763]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_19,negated_conjecture,
% 43.75/6.01      ( r1_xboole_0(sK3,sK2) ),
% 43.75/6.01      inference(cnf_transformation,[],[f56]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_759,plain,
% 43.75/6.01      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 43.75/6.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_3,plain,
% 43.75/6.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 43.75/6.01      inference(cnf_transformation,[],[f35]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_774,plain,
% 43.75/6.01      ( r1_xboole_0(X0,X1) != iProver_top
% 43.75/6.01      | r1_xboole_0(X1,X0) = iProver_top ),
% 43.75/6.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_2035,plain,
% 43.75/6.01      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_759,c_774]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_16,plain,
% 43.75/6.01      ( r2_hidden(X0,X1)
% 43.75/6.01      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
% 43.75/6.01      inference(cnf_transformation,[],[f65]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_762,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
% 43.75/6.01      | r2_hidden(X1,X0) = iProver_top ),
% 43.75/6.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_20,negated_conjecture,
% 43.75/6.01      ( r2_hidden(sK4,sK3) ),
% 43.75/6.01      inference(cnf_transformation,[],[f55]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_758,plain,
% 43.75/6.01      ( r2_hidden(sK4,sK3) = iProver_top ),
% 43.75/6.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4,plain,
% 43.75/6.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 43.75/6.01      inference(cnf_transformation,[],[f38]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_773,plain,
% 43.75/6.01      ( r2_hidden(X0,X1) != iProver_top
% 43.75/6.01      | r2_hidden(X0,X2) != iProver_top
% 43.75/6.01      | r1_xboole_0(X2,X1) != iProver_top ),
% 43.75/6.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4617,plain,
% 43.75/6.01      ( r2_hidden(sK4,X0) != iProver_top
% 43.75/6.01      | r1_xboole_0(X0,sK3) != iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_758,c_773]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_5087,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4)) = X0
% 43.75/6.01      | r1_xboole_0(X0,sK3) != iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_762,c_4617]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_5274,plain,
% 43.75/6.01      ( k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)) = sK2 ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_2035,c_5087]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_7,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 43.75/6.01      inference(cnf_transformation,[],[f63]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4112,plain,
% 43.75/6.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_3958,c_7]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_5276,plain,
% 43.75/6.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 43.75/6.01      inference(demodulation,[status(thm)],[c_5274,c_4112]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_2176,plain,
% 43.75/6.01      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_2035,c_763]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_2275,plain,
% 43.75/6.01      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,sK2) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_2176,c_0]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_1778,plain,
% 43.75/6.01      ( k4_xboole_0(sK3,sK2) = sK3 ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_759,c_763]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_2276,plain,
% 43.75/6.01      ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK3,sK3) ),
% 43.75/6.01      inference(light_normalisation,[status(thm)],[c_2275,c_1778]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_5277,plain,
% 43.75/6.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK3,sK3))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 43.75/6.01      inference(light_normalisation,[status(thm)],[c_5276,c_2276]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_2274,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)),sK2) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_2176,c_1519]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_2277,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(sK3,sK3),sK2) = iProver_top ),
% 43.75/6.01      inference(light_normalisation,[status(thm)],[c_2274,c_1778]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_2381,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK3,sK3),sK2) = k4_xboole_0(sK3,sK3) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_2277,c_763]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_3484,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK3))),k4_xboole_0(sK3,sK3)) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_2381,c_1519]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_2380,plain,
% 43.75/6.01      ( r1_xboole_0(sK2,k4_xboole_0(sK3,sK3)) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_2277,c_774]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_3473,plain,
% 43.75/6.01      ( k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)) = sK2 ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_2380,c_763]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_3492,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK3,sK3)) = iProver_top ),
% 43.75/6.01      inference(light_normalisation,[status(thm)],[c_3484,c_2276,c_3473]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_2,plain,
% 43.75/6.01      ( ~ r1_xboole_0(X0,X1)
% 43.75/6.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 43.75/6.01      inference(cnf_transformation,[],[f62]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_775,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 43.75/6.01      | r1_xboole_0(X0,X1) != iProver_top ),
% 43.75/6.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4079,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK3,sK3))) = k1_xboole_0 ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_3492,c_775]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_2046,plain,
% 43.75/6.01      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k4_xboole_0(sK3,sK3),X0)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_1778,c_7]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_3487,plain,
% 43.75/6.01      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)))) = k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK3,sK3)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_2381,c_2046]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_3488,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK3,sK3)) = k4_xboole_0(sK3,sK3) ),
% 43.75/6.01      inference(light_normalisation,
% 43.75/6.01                [status(thm)],
% 43.75/6.01                [c_3487,c_1778,c_2276,c_3473]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4080,plain,
% 43.75/6.01      ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
% 43.75/6.01      inference(light_normalisation,[status(thm)],[c_4079,c_3488]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_5278,plain,
% 43.75/6.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 43.75/6.01      inference(demodulation,[status(thm)],[c_5277,c_4080]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_1,plain,
% 43.75/6.01      ( r1_xboole_0(X0,X1)
% 43.75/6.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 43.75/6.01      inference(cnf_transformation,[],[f61]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_776,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 43.75/6.01      | r1_xboole_0(X0,X1) = iProver_top ),
% 43.75/6.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4699,plain,
% 43.75/6.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k1_xboole_0
% 43.75/6.01      | r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)))) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_4112,c_776]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_5589,plain,
% 43.75/6.01      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 43.75/6.01      inference(demodulation,[status(thm)],[c_4080,c_2276]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4099,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_3958,c_765]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4377,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)))) = k1_xboole_0 ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_4099,c_775]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4380,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 43.75/6.01      inference(light_normalisation,[status(thm)],[c_4377,c_3958]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_1647,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_6995,plain,
% 43.75/6.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_4380,c_1647]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4078,plain,
% 43.75/6.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK3))) = k1_xboole_0 ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_2380,c_775]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4081,plain,
% 43.75/6.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 43.75/6.01      inference(demodulation,[status(thm)],[c_4078,c_4080]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_9,plain,
% 43.75/6.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 43.75/6.01      inference(cnf_transformation,[],[f41]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_769,plain,
% 43.75/6.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 43.75/6.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4098,plain,
% 43.75/6.01      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_3958,c_769]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4213,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_4098,c_770]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_1650,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4073,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_765,c_775]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_1777,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_765,c_763]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4086,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 43.75/6.01      inference(light_normalisation,[status(thm)],[c_4073,c_1777]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4214,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 43.75/6.01      inference(demodulation,[status(thm)],[c_4213,c_1650,c_4086]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_7184,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) ),
% 43.75/6.01      inference(light_normalisation,
% 43.75/6.01                [status(thm)],
% 43.75/6.01                [c_6995,c_4081,c_4214,c_4380,c_5278]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_7185,plain,
% 43.75/6.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) = k1_xboole_0 ),
% 43.75/6.01      inference(demodulation,[status(thm)],[c_7184,c_4086,c_5278]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_44954,plain,
% 43.75/6.01      ( k1_xboole_0 != k1_xboole_0
% 43.75/6.01      | r1_xboole_0(sK1,k1_xboole_0) = iProver_top ),
% 43.75/6.01      inference(light_normalisation,
% 43.75/6.01                [status(thm)],
% 43.75/6.01                [c_4699,c_5274,c_5278,c_5589,c_7185]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_44955,plain,
% 43.75/6.01      ( r1_xboole_0(sK1,k1_xboole_0) = iProver_top ),
% 43.75/6.01      inference(equality_resolution_simp,[status(thm)],[c_44954]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_44959,plain,
% 43.75/6.01      ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_44955,c_763]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_45538,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)))) = k4_xboole_0(sK1,sK1) ),
% 43.75/6.01      inference(light_normalisation,
% 43.75/6.01                [status(thm)],
% 43.75/6.01                [c_4515,c_4515,c_5278,c_44959]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_23941,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_0,c_1777]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_24498,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(X1,X0)) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_1777,c_23941]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_24011,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_1777,c_0]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_24213,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 43.75/6.01      inference(demodulation,[status(thm)],[c_24011,c_4086]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_24806,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 43.75/6.01      inference(light_normalisation,[status(thm)],[c_24498,c_24213]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_24807,plain,
% 43.75/6.01      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 43.75/6.01      inference(demodulation,[status(thm)],[c_24806,c_1777,c_4086]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_2034,plain,
% 43.75/6.01      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_765,c_774]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_36742,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_2034,c_763]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_45539,plain,
% 43.75/6.01      ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
% 43.75/6.01      inference(demodulation,
% 43.75/6.01                [status(thm)],
% 43.75/6.01                [c_45538,c_7185,c_24807,c_36742]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_1639,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_5727,plain,
% 43.75/6.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_1778,c_1639]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_5854,plain,
% 43.75/6.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 43.75/6.01      inference(light_normalisation,[status(thm)],[c_5727,c_4080]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_1666,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_7,c_7]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_15515,plain,
% 43.75/6.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)),k4_xboole_0(sK2,sK3)))))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_5854,c_1666]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_1660,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_7,c_765]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_12428,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)),k4_xboole_0(sK2,sK3))) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_5854,c_1660]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_12587,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2)) = iProver_top ),
% 43.75/6.01      inference(light_normalisation,
% 43.75/6.01                [status(thm)],
% 43.75/6.01                [c_12428,c_2176,c_4081,c_5589]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_13539,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2))) = k1_xboole_0 ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_12587,c_775]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_13541,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2)) = k4_xboole_0(sK2,k1_xboole_0) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_12587,c_763]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_13542,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 43.75/6.01      inference(demodulation,[status(thm)],[c_13539,c_13541]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_15734,plain,
% 43.75/6.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2))))) = k1_xboole_0 ),
% 43.75/6.01      inference(light_normalisation,
% 43.75/6.01                [status(thm)],
% 43.75/6.01                [c_15515,c_2176,c_4081,c_5589,c_13542]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_1653,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_10263,plain,
% 43.75/6.01      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(sK3,sK2),X0)))) = k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,sK2)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,sK2)),X0)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_2176,c_1653]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_1687,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_0,c_1519]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4921,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK3,sK3)) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_1778,c_1687]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_2049,plain,
% 43.75/6.01      ( r1_tarski(sK3,sK3) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_1778,c_769]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_3963,plain,
% 43.75/6.01      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)) = sK3 ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_2049,c_770]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4941,plain,
% 43.75/6.01      ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
% 43.75/6.01      inference(light_normalisation,
% 43.75/6.01                [status(thm)],
% 43.75/6.01                [c_4921,c_2176,c_2276,c_3963,c_4080]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_6447,plain,
% 43.75/6.01      ( k4_xboole_0(sK3,k1_xboole_0) = sK3 ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_4941,c_763]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_10462,plain,
% 43.75/6.01      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) ),
% 43.75/6.01      inference(light_normalisation,
% 43.75/6.01                [status(thm)],
% 43.75/6.01                [c_10263,c_1778,c_5589,c_6447]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_23960,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_10462,c_1777]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_24269,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) ),
% 43.75/6.01      inference(light_normalisation,[status(thm)],[c_23960,c_10462]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_1661,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X3)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_7,c_7]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_1667,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X3)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))) ),
% 43.75/6.01      inference(demodulation,[status(thm)],[c_1661,c_7]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_27648,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X1)),k4_xboole_0(sK3,k4_xboole_0(sK3,X1))))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X1)),k4_xboole_0(sK3,k4_xboole_0(sK3,X1))))),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X1)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X1)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X1))),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X1))),X2)))))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_24269,c_1667]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_5583,plain,
% 43.75/6.01      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 43.75/6.01      inference(demodulation,[status(thm)],[c_4080,c_3488]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_11343,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),sK3)) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_10462,c_1519]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_13786,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),sK3))) = k1_xboole_0 ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_11343,c_775]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_13788,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_11343,c_763]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_13789,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k1_xboole_0 ),
% 43.75/6.01      inference(demodulation,[status(thm)],[c_13786,c_13788]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_11333,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(sK3,k4_xboole_0(sK3,X1)))) = k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),X1)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_10462,c_1650]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_5819,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X3)))))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_1639,c_1639]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_11428,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,X1)))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 43.75/6.01      inference(demodulation,
% 43.75/6.01                [status(thm)],
% 43.75/6.01                [c_11333,c_1650,c_5819,c_10462]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_20703,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X2)) = k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X1)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_11428,c_1650]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_20761,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_11428,c_1667]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_21037,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) ),
% 43.75/6.01      inference(demodulation,[status(thm)],[c_20703,c_20761]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_27751,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X1))),k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X1))),k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))))) = k1_xboole_0 ),
% 43.75/6.01      inference(demodulation,
% 43.75/6.01                [status(thm)],
% 43.75/6.01                [c_27648,c_1650,c_5583,c_13789,c_21037,c_24807]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_27752,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,X1),k4_xboole_0(k4_xboole_0(sK3,X1),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))))))) = k1_xboole_0 ),
% 43.75/6.01      inference(demodulation,[status(thm)],[c_27751,c_21037]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_5719,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_0,c_1639]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_25156,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X3)))))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_1653,c_5719]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_24445,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_0,c_23941]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_3957,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_769,c_770]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4930,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_1687,c_763]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_24887,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 43.75/6.01      inference(light_normalisation,
% 43.75/6.01                [status(thm)],
% 43.75/6.01                [c_24445,c_3957,c_4930]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_25805,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X3)))))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,k4_xboole_0(X0,X3)))) ),
% 43.75/6.01      inference(light_normalisation,[status(thm)],[c_25156,c_24887]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_27753,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(k4_xboole_0(sK3,X0),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k1_xboole_0 ),
% 43.75/6.01      inference(demodulation,[status(thm)],[c_27752,c_10462,c_25805]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_28106,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(sK3,sK2),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k1_xboole_0))))) = k1_xboole_0 ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_15734,c_27753]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_28629,plain,
% 43.75/6.01      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k1_xboole_0))))) = k1_xboole_0 ),
% 43.75/6.01      inference(light_normalisation,[status(thm)],[c_28106,c_1778]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_4694,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 43.75/6.01      | r1_xboole_0(X1,X0) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_0,c_776]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_28955,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k1_xboole_0))),sK3) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_28629,c_4694]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_6622,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_5589,c_7]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_1779,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_1519,c_763]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_29258,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_0,c_1779]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_29663,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 43.75/6.01      inference(light_normalisation,
% 43.75/6.01                [status(thm)],
% 43.75/6.01                [c_29258,c_3957,c_4930,c_24887]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_30697,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
% 43.75/6.01      inference(demodulation,[status(thm)],[c_6622,c_29663]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_30807,plain,
% 43.75/6.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k1_xboole_0))) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_30697,c_0]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_31370,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),sK3) = iProver_top ),
% 43.75/6.01      inference(light_normalisation,[status(thm)],[c_28955,c_30807]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_31374,plain,
% 43.75/6.01      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),sK3) = iProver_top ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_0,c_31370]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_33680,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_31374,c_5087]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_34395,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_0,c_33680]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_42210,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK2)))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_34395,c_7]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_138226,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k1_xboole_0))),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_45539,c_42210]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_139755,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)))) ),
% 43.75/6.01      inference(light_normalisation,
% 43.75/6.01                [status(thm)],
% 43.75/6.01                [c_138226,c_5278,c_44959]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_31412,plain,
% 43.75/6.01      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
% 43.75/6.01      inference(superposition,[status(thm)],[c_31370,c_5087]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_139756,plain,
% 43.75/6.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 43.75/6.01      inference(demodulation,
% 43.75/6.01                [status(thm)],
% 43.75/6.01                [c_139755,c_29663,c_31412,c_44959,c_45539]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_1711,plain,
% 43.75/6.01      ( r1_xboole_0(sK2,sK1)
% 43.75/6.01      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != k1_xboole_0 ),
% 43.75/6.01      inference(instantiation,[status(thm)],[c_1]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_1058,plain,
% 43.75/6.01      ( r1_xboole_0(sK2,sK3) | ~ r1_xboole_0(sK3,sK2) ),
% 43.75/6.01      inference(instantiation,[status(thm)],[c_3]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_12,plain,
% 43.75/6.01      ( ~ r1_xboole_0(X0,X1)
% 43.75/6.01      | ~ r1_xboole_0(X0,X2)
% 43.75/6.01      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 43.75/6.01      inference(cnf_transformation,[],[f43]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_872,plain,
% 43.75/6.01      ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))
% 43.75/6.01      | ~ r1_xboole_0(sK2,sK3)
% 43.75/6.01      | ~ r1_xboole_0(sK2,sK1) ),
% 43.75/6.01      inference(instantiation,[status(thm)],[c_12]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_817,plain,
% 43.75/6.01      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
% 43.75/6.01      | ~ r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
% 43.75/6.01      inference(instantiation,[status(thm)],[c_3]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(c_18,negated_conjecture,
% 43.75/6.01      ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
% 43.75/6.01      inference(cnf_transformation,[],[f57]) ).
% 43.75/6.01  
% 43.75/6.01  cnf(contradiction,plain,
% 43.75/6.01      ( $false ),
% 43.75/6.01      inference(minisat,
% 43.75/6.01                [status(thm)],
% 43.75/6.01                [c_139756,c_1711,c_1058,c_872,c_817,c_18,c_19]) ).
% 43.75/6.01  
% 43.75/6.01  
% 43.75/6.01  % SZS output end CNFRefutation for theBenchmark.p
% 43.75/6.01  
% 43.75/6.01  ------                               Statistics
% 43.75/6.01  
% 43.75/6.01  ------ General
% 43.75/6.01  
% 43.75/6.01  abstr_ref_over_cycles:                  0
% 43.75/6.01  abstr_ref_under_cycles:                 0
% 43.75/6.01  gc_basic_clause_elim:                   0
% 43.75/6.01  forced_gc_time:                         0
% 43.75/6.01  parsing_time:                           0.011
% 43.75/6.01  unif_index_cands_time:                  0.
% 43.75/6.01  unif_index_add_time:                    0.
% 43.75/6.01  orderings_time:                         0.
% 43.75/6.01  out_proof_time:                         0.017
% 43.75/6.01  total_time:                             5.341
% 43.75/6.01  num_of_symbols:                         43
% 43.75/6.01  num_of_terms:                           235198
% 43.75/6.01  
% 43.75/6.01  ------ Preprocessing
% 43.75/6.01  
% 43.75/6.01  num_of_splits:                          0
% 43.75/6.01  num_of_split_atoms:                     0
% 43.75/6.01  num_of_reused_defs:                     0
% 43.75/6.01  num_eq_ax_congr_red:                    4
% 43.75/6.01  num_of_sem_filtered_clauses:            1
% 43.75/6.01  num_of_subtypes:                        0
% 43.75/6.01  monotx_restored_types:                  0
% 43.75/6.01  sat_num_of_epr_types:                   0
% 43.75/6.01  sat_num_of_non_cyclic_types:            0
% 43.75/6.01  sat_guarded_non_collapsed_types:        0
% 43.75/6.01  num_pure_diseq_elim:                    0
% 43.75/6.01  simp_replaced_by:                       0
% 43.75/6.01  res_preprocessed:                       83
% 43.75/6.01  prep_upred:                             0
% 43.75/6.01  prep_unflattend:                        4
% 43.75/6.01  smt_new_axioms:                         0
% 43.75/6.01  pred_elim_cands:                        3
% 43.75/6.01  pred_elim:                              0
% 43.75/6.01  pred_elim_cl:                           0
% 43.75/6.01  pred_elim_cycles:                       1
% 43.75/6.01  merged_defs:                            18
% 43.75/6.01  merged_defs_ncl:                        0
% 43.75/6.01  bin_hyper_res:                          18
% 43.75/6.01  prep_cycles:                            3
% 43.75/6.01  pred_elim_time:                         0.
% 43.75/6.01  splitting_time:                         0.
% 43.75/6.01  sem_filter_time:                        0.
% 43.75/6.01  monotx_time:                            0.001
% 43.75/6.01  subtype_inf_time:                       0.
% 43.75/6.01  
% 43.75/6.01  ------ Problem properties
% 43.75/6.01  
% 43.75/6.01  clauses:                                22
% 43.75/6.01  conjectures:                            4
% 43.75/6.01  epr:                                    4
% 43.75/6.01  horn:                                   19
% 43.75/6.01  ground:                                 4
% 43.75/6.01  unary:                                  8
% 43.75/6.01  binary:                                 12
% 43.75/6.01  lits:                                   38
% 43.75/6.01  lits_eq:                                9
% 43.75/6.01  fd_pure:                                0
% 43.75/6.01  fd_pseudo:                              0
% 43.75/6.01  fd_cond:                                0
% 43.75/6.01  fd_pseudo_cond:                         0
% 43.75/6.01  ac_symbols:                             0
% 43.75/6.01  
% 43.75/6.01  ------ Propositional Solver
% 43.75/6.01  
% 43.75/6.01  prop_solver_calls:                      49
% 43.75/6.01  prop_fast_solver_calls:                 1018
% 43.75/6.01  smt_solver_calls:                       0
% 43.75/6.01  smt_fast_solver_calls:                  0
% 43.75/6.01  prop_num_of_clauses:                    49181
% 43.75/6.01  prop_preprocess_simplified:             34536
% 43.75/6.01  prop_fo_subsumed:                       5
% 43.75/6.01  prop_solver_time:                       0.
% 43.75/6.01  smt_solver_time:                        0.
% 43.75/6.01  smt_fast_solver_time:                   0.
% 43.75/6.01  prop_fast_solver_time:                  0.
% 43.75/6.01  prop_unsat_core_time:                   0.004
% 43.75/6.01  
% 43.75/6.01  ------ QBF
% 43.75/6.01  
% 43.75/6.01  qbf_q_res:                              0
% 43.75/6.01  qbf_num_tautologies:                    0
% 43.75/6.01  qbf_prep_cycles:                        0
% 43.75/6.01  
% 43.75/6.01  ------ BMC1
% 43.75/6.01  
% 43.75/6.01  bmc1_current_bound:                     -1
% 43.75/6.01  bmc1_last_solved_bound:                 -1
% 43.75/6.01  bmc1_unsat_core_size:                   -1
% 43.75/6.01  bmc1_unsat_core_parents_size:           -1
% 43.75/6.01  bmc1_merge_next_fun:                    0
% 43.75/6.01  bmc1_unsat_core_clauses_time:           0.
% 43.75/6.01  
% 43.75/6.01  ------ Instantiation
% 43.75/6.01  
% 43.75/6.01  inst_num_of_clauses:                    5129
% 43.75/6.01  inst_num_in_passive:                    1460
% 43.75/6.01  inst_num_in_active:                     1721
% 43.75/6.01  inst_num_in_unprocessed:                1948
% 43.75/6.01  inst_num_of_loops:                      2010
% 43.75/6.01  inst_num_of_learning_restarts:          0
% 43.75/6.01  inst_num_moves_active_passive:          287
% 43.75/6.01  inst_lit_activity:                      0
% 43.75/6.01  inst_lit_activity_moves:                1
% 43.75/6.01  inst_num_tautologies:                   0
% 43.75/6.01  inst_num_prop_implied:                  0
% 43.75/6.01  inst_num_existing_simplified:           0
% 43.75/6.01  inst_num_eq_res_simplified:             0
% 43.75/6.01  inst_num_child_elim:                    0
% 43.75/6.01  inst_num_of_dismatching_blockings:      3677
% 43.75/6.01  inst_num_of_non_proper_insts:           4845
% 43.75/6.01  inst_num_of_duplicates:                 0
% 43.75/6.01  inst_inst_num_from_inst_to_res:         0
% 43.75/6.01  inst_dismatching_checking_time:         0.
% 43.75/6.01  
% 43.75/6.01  ------ Resolution
% 43.75/6.01  
% 43.75/6.01  res_num_of_clauses:                     0
% 43.75/6.01  res_num_in_passive:                     0
% 43.75/6.01  res_num_in_active:                      0
% 43.75/6.01  res_num_of_loops:                       86
% 43.75/6.01  res_forward_subset_subsumed:            257
% 43.75/6.01  res_backward_subset_subsumed:           2
% 43.75/6.01  res_forward_subsumed:                   0
% 43.75/6.01  res_backward_subsumed:                  0
% 43.75/6.01  res_forward_subsumption_resolution:     0
% 43.75/6.01  res_backward_subsumption_resolution:    0
% 43.75/6.01  res_clause_to_clause_subsumption:       175717
% 43.75/6.01  res_orphan_elimination:                 0
% 43.75/6.01  res_tautology_del:                      355
% 43.75/6.01  res_num_eq_res_simplified:              0
% 43.75/6.01  res_num_sel_changes:                    0
% 43.75/6.01  res_moves_from_active_to_pass:          0
% 43.75/6.01  
% 43.75/6.01  ------ Superposition
% 43.75/6.01  
% 43.75/6.01  sup_time_total:                         0.
% 43.75/6.01  sup_time_generating:                    0.
% 43.75/6.01  sup_time_sim_full:                      0.
% 43.75/6.01  sup_time_sim_immed:                     0.
% 43.75/6.01  
% 43.75/6.01  sup_num_of_clauses:                     10420
% 43.75/6.01  sup_num_in_active:                      341
% 43.75/6.01  sup_num_in_passive:                     10079
% 43.75/6.01  sup_num_of_loops:                       401
% 43.75/6.01  sup_fw_superposition:                   20996
% 43.75/6.01  sup_bw_superposition:                   24038
% 43.75/6.01  sup_immediate_simplified:               29307
% 43.75/6.01  sup_given_eliminated:                   13
% 43.75/6.01  comparisons_done:                       0
% 43.75/6.01  comparisons_avoided:                    0
% 43.75/6.01  
% 43.75/6.01  ------ Simplifications
% 43.75/6.01  
% 43.75/6.01  
% 43.75/6.01  sim_fw_subset_subsumed:                 238
% 43.75/6.01  sim_bw_subset_subsumed:                 0
% 43.75/6.01  sim_fw_subsumed:                        2658
% 43.75/6.01  sim_bw_subsumed:                        434
% 43.75/6.01  sim_fw_subsumption_res:                 0
% 43.75/6.01  sim_bw_subsumption_res:                 0
% 43.75/6.01  sim_tautology_del:                      2
% 43.75/6.01  sim_eq_tautology_del:                   2977
% 43.75/6.01  sim_eq_res_simp:                        478
% 43.75/6.01  sim_fw_demodulated:                     19459
% 43.75/6.01  sim_bw_demodulated:                     1302
% 43.75/6.01  sim_light_normalised:                   17501
% 43.75/6.01  sim_joinable_taut:                      0
% 43.75/6.01  sim_joinable_simp:                      0
% 43.75/6.01  sim_ac_normalised:                      0
% 43.75/6.01  sim_smt_subsumption:                    0
% 43.75/6.01  
%------------------------------------------------------------------------------
