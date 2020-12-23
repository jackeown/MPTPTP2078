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
% DateTime   : Thu Dec  3 11:38:36 EST 2020

% Result     : Theorem 35.80s
% Output     : CNFRefutation 35.80s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 990 expanded)
%              Number of clauses        :  129 ( 398 expanded)
%              Number of leaves         :   19 ( 198 expanded)
%              Depth                    :   21
%              Number of atoms          :  385 (2321 expanded)
%              Number of equality atoms :  139 ( 534 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f64])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f65])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f29])).

fof(f36,plain,
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

fof(f37,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f36])).

fof(f59,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f59,f65])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
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

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f32])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f54,f48])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f63])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) ),
    inference(definition_unfolding,[],[f62,f63])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_225,plain,
    ( k3_xboole_0(X0_41,X1_41) = k3_xboole_0(X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_217,plain,
    ( r2_hidden(sK1(X0_41,X1_41),k3_xboole_0(X0_41,X1_41))
    | r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_672,plain,
    ( r2_hidden(sK1(X0_41,X1_41),k3_xboole_0(X0_41,X1_41)) = iProver_top
    | r1_xboole_0(X0_41,X1_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_217])).

cnf(c_1953,plain,
    ( r2_hidden(sK1(X0_41,X1_41),k3_xboole_0(X1_41,X0_41)) = iProver_top
    | r1_xboole_0(X0_41,X1_41) = iProver_top ),
    inference(superposition,[status(thm)],[c_225,c_672])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_211,plain,
    ( r2_hidden(X0_42,X0_41)
    | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),X0_41) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_678,plain,
    ( r2_hidden(X0_42,X0_41) = iProver_top
    | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_207,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_682,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_215,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | k3_xboole_0(X0_41,X1_41) = X0_41 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_674,plain,
    ( k3_xboole_0(X0_41,X1_41) = X0_41
    | r1_tarski(X0_41,X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_1421,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_682,c_674])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_218,plain,
    ( ~ r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41))
    | ~ r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_671,plain,
    ( r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41)) != iProver_top
    | r1_xboole_0(X0_41,X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_1933,plain,
    ( r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41)) != iProver_top
    | r1_xboole_0(X1_41,X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_225,c_671])).

cnf(c_3736,plain,
    ( r2_hidden(X0_42,k3_xboole_0(sK2,sK3)) != iProver_top
    | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1933])).

cnf(c_23716,plain,
    ( r2_hidden(X0_42,k3_xboole_0(sK2,sK3)) != iProver_top
    | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_678,c_3736])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_221,plain,
    ( ~ r2_hidden(X0_42,X0_41)
    | ~ r2_hidden(X0_42,X1_41)
    | ~ r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_869,plain,
    ( ~ r2_hidden(X0_42,sK3)
    | ~ r2_hidden(X0_42,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_221])).

cnf(c_871,plain,
    ( ~ r2_hidden(sK5,sK3)
    | ~ r2_hidden(sK5,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_869])).

cnf(c_989,plain,
    ( r2_hidden(X0_42,sK3)
    | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),sK3) ),
    inference(instantiation,[status(thm)],[c_211])).

cnf(c_991,plain,
    ( r2_hidden(sK5,sK3)
    | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_3739,plain,
    ( r2_hidden(X0_42,k3_xboole_0(sK2,sK3)) != iProver_top
    | r1_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_671])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_223,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X0_41,X1_41) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2868,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41)
    | k3_xboole_0(k3_xboole_0(sK2,sK3),X0_41) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_6443,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK3),sK3)
    | k3_xboole_0(k3_xboole_0(sK2,sK3),sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2868])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_224,plain,
    ( r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X0_41,X1_41) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1799,plain,
    ( r1_xboole_0(X0_41,sK3)
    | k3_xboole_0(X0_41,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_6445,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,sK3),sK3)
    | k3_xboole_0(k3_xboole_0(sK2,sK3),sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_6457,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),sK3) != k1_xboole_0
    | r1_xboole_0(k3_xboole_0(sK2,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6445])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_222,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2869,plain,
    ( r1_xboole_0(X0_41,k3_xboole_0(sK2,sK3))
    | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_6542,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK3),sK3)
    | r1_xboole_0(sK3,k3_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2869])).

cnf(c_6544,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,sK3),sK3) != iProver_top
    | r1_xboole_0(sK3,k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6542])).

cnf(c_1305,plain,
    ( ~ r2_hidden(X0_42,k3_xboole_0(sK3,X0_41))
    | ~ r1_xboole_0(sK3,X0_41) ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_3412,plain,
    ( ~ r2_hidden(sK0(X0_41,k3_xboole_0(sK3,X1_41)),k3_xboole_0(sK3,X1_41))
    | ~ r1_xboole_0(sK3,X1_41) ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_11861,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))),k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))
    | ~ r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_3412])).

cnf(c_6,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_220,plain,
    ( r2_hidden(sK0(X0_41,X1_41),X1_41)
    | r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_854,plain,
    ( r2_hidden(sK0(X0_41,k3_xboole_0(X1_41,X2_41)),k3_xboole_0(X1_41,X2_41))
    | r1_xboole_0(X0_41,k3_xboole_0(X1_41,X2_41)) ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_1783,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(X0_41,k2_enumset1(sK5,sK5,sK5,sK5))),k3_xboole_0(X0_41,k2_enumset1(sK5,sK5,sK5,sK5)))
    | r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(X0_41,k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_11862,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))),k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))
    | r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_1783])).

cnf(c_1131,plain,
    ( ~ r1_xboole_0(X0_41,sK3)
    | r1_xboole_0(sK3,X0_41) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_21598,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3)
    | r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,X2)
    | ~ r1_xboole_0(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_xboole_0(X0_41,X2_41)
    | ~ r1_xboole_0(X0_41,k3_xboole_0(X2_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1270,plain,
    ( ~ r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))
    | r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41)
    | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(X0_41,k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_43311,plain,
    ( ~ r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))
    | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))
    | r1_xboole_0(k3_xboole_0(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_1270])).

cnf(c_3738,plain,
    ( r2_hidden(sK1(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)),k3_xboole_0(sK2,sK3)) = iProver_top
    | r1_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_672])).

cnf(c_10,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_216,plain,
    ( r1_tarski(k3_xboole_0(X0_41,X1_41),X0_41) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_673,plain,
    ( r1_tarski(k3_xboole_0(X0_41,X1_41),X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_216])).

cnf(c_1070,plain,
    ( r1_tarski(k3_xboole_0(X0_41,X1_41),X1_41) = iProver_top ),
    inference(superposition,[status(thm)],[c_225,c_673])).

cnf(c_1423,plain,
    ( k3_xboole_0(k3_xboole_0(X0_41,X1_41),X1_41) = k3_xboole_0(X0_41,X1_41) ),
    inference(superposition,[status(thm)],[c_1070,c_674])).

cnf(c_4572,plain,
    ( r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41)) != iProver_top
    | r1_xboole_0(X1_41,k3_xboole_0(X0_41,X1_41)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_1933])).

cnf(c_53057,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
    | r1_xboole_0(sK3,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3738,c_4572])).

cnf(c_179208,plain,
    ( r2_hidden(X0_42,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23716,c_19,c_18,c_17,c_871,c_991,c_3739,c_6443,c_6457,c_6544,c_11861,c_11862,c_21598,c_43311,c_53057])).

cnf(c_179219,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1953,c_179208])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_212,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X0_41,k5_xboole_0(X1_41,k5_xboole_0(X2_41,k3_xboole_0(X2_41,X1_41)))) = k3_xboole_0(X0_41,X2_41) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_677,plain,
    ( k3_xboole_0(X0_41,k5_xboole_0(X1_41,k5_xboole_0(X2_41,k3_xboole_0(X2_41,X1_41)))) = k3_xboole_0(X0_41,X2_41)
    | r1_xboole_0(X0_41,X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_179865,plain,
    ( k3_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK2)))) = k3_xboole_0(sK3,X0_41) ),
    inference(superposition,[status(thm)],[c_179219,c_677])).

cnf(c_668,plain,
    ( r2_hidden(X0_42,X0_41) != iProver_top
    | r2_hidden(X0_42,X1_41) != iProver_top
    | r1_xboole_0(X1_41,X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_2520,plain,
    ( r2_hidden(sK1(X0_41,X1_41),X2_41) != iProver_top
    | r1_xboole_0(X0_41,X1_41) = iProver_top
    | r1_xboole_0(k3_xboole_0(X1_41,X0_41),X2_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_1953,c_668])).

cnf(c_15254,plain,
    ( r1_xboole_0(X0_41,X1_41) = iProver_top
    | r1_xboole_0(k3_xboole_0(X1_41,X0_41),k3_xboole_0(X0_41,X1_41)) != iProver_top ),
    inference(superposition,[status(thm)],[c_672,c_2520])).

cnf(c_186780,plain,
    ( r1_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK2))),sK3),k3_xboole_0(sK3,X0_41)) != iProver_top
    | r1_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_179865,c_15254])).

cnf(c_209,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_680,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_666,plain,
    ( k3_xboole_0(X0_41,X1_41) = k1_xboole_0
    | r1_xboole_0(X0_41,X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_1200,plain,
    ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_680,c_666])).

cnf(c_676,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_xboole_0(X0_41,X2_41) = iProver_top
    | r1_xboole_0(X0_41,k3_xboole_0(X2_41,X1_41)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_2967,plain,
    ( r1_tarski(X0_41,sK3) != iProver_top
    | r1_xboole_0(X0_41,sK4) = iProver_top
    | r1_xboole_0(X0_41,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_676])).

cnf(c_1478,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(X2_41,k3_xboole_0(X0_41,X1_41)) ),
    inference(resolution,[status(thm)],[c_218,c_220])).

cnf(c_3285,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r1_xboole_0(X2_41,X1_41)
    | r1_xboole_0(X0_41,X2_41) ),
    inference(resolution,[status(thm)],[c_213,c_1478])).

cnf(c_3574,plain,
    ( ~ r1_tarski(X0_41,sK3)
    | r1_xboole_0(X0_41,sK4) ),
    inference(resolution,[status(thm)],[c_3285,c_209])).

cnf(c_3575,plain,
    ( r1_tarski(X0_41,sK3) != iProver_top
    | r1_xboole_0(X0_41,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3574])).

cnf(c_19078,plain,
    ( r1_xboole_0(X0_41,sK4) = iProver_top
    | r1_tarski(X0_41,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2967,c_3575])).

cnf(c_19079,plain,
    ( r1_tarski(X0_41,sK3) != iProver_top
    | r1_xboole_0(X0_41,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_19078])).

cnf(c_19084,plain,
    ( r1_xboole_0(k3_xboole_0(sK3,X0_41),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_673,c_19079])).

cnf(c_19358,plain,
    ( k3_xboole_0(k3_xboole_0(sK3,X0_41),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19084,c_666])).

cnf(c_667,plain,
    ( r1_xboole_0(X0_41,X1_41) != iProver_top
    | r1_xboole_0(X1_41,X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_1410,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_680,c_667])).

cnf(c_3544,plain,
    ( k3_xboole_0(sK3,k5_xboole_0(sK4,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK4)))) = k3_xboole_0(sK3,X0_41) ),
    inference(superposition,[status(thm)],[c_1410,c_677])).

cnf(c_20004,plain,
    ( k3_xboole_0(sK3,k5_xboole_0(sK4,k5_xboole_0(k3_xboole_0(sK3,X0_41),k1_xboole_0))) = k3_xboole_0(sK3,k3_xboole_0(sK3,X0_41)) ),
    inference(superposition,[status(thm)],[c_19358,c_3544])).

cnf(c_4563,plain,
    ( k3_xboole_0(k3_xboole_0(X0_41,X1_41),X0_41) = k3_xboole_0(X1_41,X0_41) ),
    inference(superposition,[status(thm)],[c_225,c_1423])).

cnf(c_5097,plain,
    ( k3_xboole_0(X0_41,k3_xboole_0(X0_41,X1_41)) = k3_xboole_0(X1_41,X0_41) ),
    inference(superposition,[status(thm)],[c_4563,c_225])).

cnf(c_20008,plain,
    ( k3_xboole_0(sK3,k5_xboole_0(sK4,k5_xboole_0(k3_xboole_0(sK3,X0_41),k1_xboole_0))) = k3_xboole_0(X0_41,sK3) ),
    inference(demodulation,[status(thm)],[c_20004,c_5097])).

cnf(c_187020,plain,
    ( k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK2))),sK3) = k3_xboole_0(sK3,k5_xboole_0(sK4,k5_xboole_0(k3_xboole_0(sK3,X0_41),k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_179865,c_20008])).

cnf(c_19085,plain,
    ( r1_xboole_0(k3_xboole_0(X0_41,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1070,c_19079])).

cnf(c_19389,plain,
    ( k3_xboole_0(k3_xboole_0(X0_41,sK3),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19085,c_666])).

cnf(c_20519,plain,
    ( k3_xboole_0(sK3,k5_xboole_0(sK4,k5_xboole_0(k3_xboole_0(X0_41,sK3),k1_xboole_0))) = k3_xboole_0(sK3,k3_xboole_0(X0_41,sK3)) ),
    inference(superposition,[status(thm)],[c_19389,c_3544])).

cnf(c_1422,plain,
    ( k3_xboole_0(k3_xboole_0(X0_41,X1_41),X0_41) = k3_xboole_0(X0_41,X1_41) ),
    inference(superposition,[status(thm)],[c_673,c_674])).

cnf(c_4314,plain,
    ( k3_xboole_0(k3_xboole_0(X0_41,X1_41),X1_41) = k3_xboole_0(X1_41,X0_41) ),
    inference(superposition,[status(thm)],[c_225,c_1422])).

cnf(c_4677,plain,
    ( k3_xboole_0(X0_41,k3_xboole_0(X1_41,X0_41)) = k3_xboole_0(X0_41,X1_41) ),
    inference(superposition,[status(thm)],[c_4314,c_225])).

cnf(c_20521,plain,
    ( k3_xboole_0(sK3,k5_xboole_0(sK4,k5_xboole_0(k3_xboole_0(X0_41,sK3),k1_xboole_0))) = k3_xboole_0(sK3,X0_41) ),
    inference(demodulation,[status(thm)],[c_20519,c_4677])).

cnf(c_26051,plain,
    ( k3_xboole_0(sK3,k5_xboole_0(sK4,k5_xboole_0(k3_xboole_0(sK3,X0_41),k1_xboole_0))) = k3_xboole_0(sK3,X0_41) ),
    inference(superposition,[status(thm)],[c_225,c_20521])).

cnf(c_187059,plain,
    ( k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK2))),sK3) = k3_xboole_0(sK3,X0_41) ),
    inference(light_normalisation,[status(thm)],[c_187020,c_26051])).

cnf(c_187514,plain,
    ( r1_xboole_0(k3_xboole_0(sK3,X0_41),k3_xboole_0(sK3,X0_41)) != iProver_top
    | r1_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_186780,c_187059])).

cnf(c_187575,plain,
    ( r1_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) != iProver_top
    | r1_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_187514])).

cnf(c_7,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_219,plain,
    ( r2_hidden(sK0(X0_41,X1_41),X0_41)
    | r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_844,plain,
    ( r2_hidden(sK0(k3_xboole_0(X0_41,X1_41),X2_41),k3_xboole_0(X0_41,X1_41))
    | r1_xboole_0(k3_xboole_0(X0_41,X1_41),X2_41) ),
    inference(instantiation,[status(thm)],[c_219])).

cnf(c_2058,plain,
    ( r2_hidden(sK0(k3_xboole_0(X0_41,X1_41),k3_xboole_0(X0_41,X1_41)),k3_xboole_0(X0_41,X1_41))
    | r1_xboole_0(k3_xboole_0(X0_41,X1_41),k3_xboole_0(X0_41,X1_41)) ),
    inference(instantiation,[status(thm)],[c_844])).

cnf(c_23333,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)),k3_xboole_0(sK3,sK4))
    | r1_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2058])).

cnf(c_23337,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)),k3_xboole_0(sK3,sK4)) = iProver_top
    | r1_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23333])).

cnf(c_855,plain,
    ( ~ r2_hidden(sK0(X0_41,k3_xboole_0(X1_41,X2_41)),k3_xboole_0(X1_41,X2_41))
    | ~ r1_xboole_0(X1_41,X2_41) ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_2057,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(X0_41,X1_41),k3_xboole_0(X0_41,X1_41)),k3_xboole_0(X0_41,X1_41))
    | ~ r1_xboole_0(X0_41,X1_41) ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_22222,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)),k3_xboole_0(sK3,sK4))
    | ~ r1_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2057])).

cnf(c_22223,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)),k3_xboole_0(sK3,sK4)) != iProver_top
    | r1_xboole_0(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22222])).

cnf(c_1101,plain,
    ( r1_xboole_0(X0_41,sK3)
    | ~ r1_xboole_0(sK3,X0_41) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_1788,plain,
    ( r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3)
    | ~ r1_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2)))) ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_1789,plain,
    ( r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) = iProver_top
    | r1_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1788])).

cnf(c_802,plain,
    ( r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_803,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top
    | r1_xboole_0(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_802])).

cnf(c_16,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,plain,
    ( r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_22,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_187575,c_23337,c_22223,c_1789,c_803,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.80/4.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.80/4.98  
% 35.80/4.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.80/4.98  
% 35.80/4.98  ------  iProver source info
% 35.80/4.98  
% 35.80/4.98  git: date: 2020-06-30 10:37:57 +0100
% 35.80/4.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.80/4.98  git: non_committed_changes: false
% 35.80/4.98  git: last_make_outside_of_git: false
% 35.80/4.98  
% 35.80/4.98  ------ 
% 35.80/4.98  
% 35.80/4.98  ------ Input Options
% 35.80/4.98  
% 35.80/4.98  --out_options                           all
% 35.80/4.98  --tptp_safe_out                         true
% 35.80/4.98  --problem_path                          ""
% 35.80/4.98  --include_path                          ""
% 35.80/4.98  --clausifier                            res/vclausify_rel
% 35.80/4.98  --clausifier_options                    --mode clausify
% 35.80/4.98  --stdin                                 false
% 35.80/4.98  --stats_out                             sel
% 35.80/4.98  
% 35.80/4.98  ------ General Options
% 35.80/4.98  
% 35.80/4.98  --fof                                   false
% 35.80/4.98  --time_out_real                         604.99
% 35.80/4.98  --time_out_virtual                      -1.
% 35.80/4.98  --symbol_type_check                     false
% 35.80/4.98  --clausify_out                          false
% 35.80/4.98  --sig_cnt_out                           false
% 35.80/4.98  --trig_cnt_out                          false
% 35.80/4.98  --trig_cnt_out_tolerance                1.
% 35.80/4.98  --trig_cnt_out_sk_spl                   false
% 35.80/4.98  --abstr_cl_out                          false
% 35.80/4.98  
% 35.80/4.98  ------ Global Options
% 35.80/4.98  
% 35.80/4.98  --schedule                              none
% 35.80/4.98  --add_important_lit                     false
% 35.80/4.98  --prop_solver_per_cl                    1000
% 35.80/4.98  --min_unsat_core                        false
% 35.80/4.98  --soft_assumptions                      false
% 35.80/4.98  --soft_lemma_size                       3
% 35.80/4.98  --prop_impl_unit_size                   0
% 35.80/4.98  --prop_impl_unit                        []
% 35.80/4.98  --share_sel_clauses                     true
% 35.80/4.98  --reset_solvers                         false
% 35.80/4.98  --bc_imp_inh                            [conj_cone]
% 35.80/4.98  --conj_cone_tolerance                   3.
% 35.80/4.98  --extra_neg_conj                        none
% 35.80/4.98  --large_theory_mode                     true
% 35.80/4.98  --prolific_symb_bound                   200
% 35.80/4.98  --lt_threshold                          2000
% 35.80/4.98  --clause_weak_htbl                      true
% 35.80/4.98  --gc_record_bc_elim                     false
% 35.80/4.98  
% 35.80/4.98  ------ Preprocessing Options
% 35.80/4.98  
% 35.80/4.98  --preprocessing_flag                    true
% 35.80/4.98  --time_out_prep_mult                    0.1
% 35.80/4.98  --splitting_mode                        input
% 35.80/4.98  --splitting_grd                         true
% 35.80/4.98  --splitting_cvd                         false
% 35.80/4.98  --splitting_cvd_svl                     false
% 35.80/4.98  --splitting_nvd                         32
% 35.80/4.98  --sub_typing                            true
% 35.80/4.98  --prep_gs_sim                           false
% 35.80/4.98  --prep_unflatten                        true
% 35.80/4.98  --prep_res_sim                          true
% 35.80/4.98  --prep_upred                            true
% 35.80/4.98  --prep_sem_filter                       exhaustive
% 35.80/4.98  --prep_sem_filter_out                   false
% 35.80/4.98  --pred_elim                             false
% 35.80/4.98  --res_sim_input                         true
% 35.80/4.98  --eq_ax_congr_red                       true
% 35.80/4.98  --pure_diseq_elim                       true
% 35.80/4.98  --brand_transform                       false
% 35.80/4.98  --non_eq_to_eq                          false
% 35.80/4.98  --prep_def_merge                        true
% 35.80/4.98  --prep_def_merge_prop_impl              false
% 35.80/4.98  --prep_def_merge_mbd                    true
% 35.80/4.98  --prep_def_merge_tr_red                 false
% 35.80/4.98  --prep_def_merge_tr_cl                  false
% 35.80/4.98  --smt_preprocessing                     true
% 35.80/4.98  --smt_ac_axioms                         fast
% 35.80/4.98  --preprocessed_out                      false
% 35.80/4.98  --preprocessed_stats                    false
% 35.80/4.98  
% 35.80/4.98  ------ Abstraction refinement Options
% 35.80/4.98  
% 35.80/4.98  --abstr_ref                             []
% 35.80/4.98  --abstr_ref_prep                        false
% 35.80/4.98  --abstr_ref_until_sat                   false
% 35.80/4.98  --abstr_ref_sig_restrict                funpre
% 35.80/4.98  --abstr_ref_af_restrict_to_split_sk     false
% 35.80/4.98  --abstr_ref_under                       []
% 35.80/4.98  
% 35.80/4.98  ------ SAT Options
% 35.80/4.98  
% 35.80/4.98  --sat_mode                              false
% 35.80/4.98  --sat_fm_restart_options                ""
% 35.80/4.98  --sat_gr_def                            false
% 35.80/4.98  --sat_epr_types                         true
% 35.80/4.98  --sat_non_cyclic_types                  false
% 35.80/4.98  --sat_finite_models                     false
% 35.80/4.98  --sat_fm_lemmas                         false
% 35.80/4.98  --sat_fm_prep                           false
% 35.80/4.98  --sat_fm_uc_incr                        true
% 35.80/4.98  --sat_out_model                         small
% 35.80/4.98  --sat_out_clauses                       false
% 35.80/4.98  
% 35.80/4.98  ------ QBF Options
% 35.80/4.98  
% 35.80/4.98  --qbf_mode                              false
% 35.80/4.98  --qbf_elim_univ                         false
% 35.80/4.98  --qbf_dom_inst                          none
% 35.80/4.98  --qbf_dom_pre_inst                      false
% 35.80/4.98  --qbf_sk_in                             false
% 35.80/4.98  --qbf_pred_elim                         true
% 35.80/4.98  --qbf_split                             512
% 35.80/4.98  
% 35.80/4.98  ------ BMC1 Options
% 35.80/4.98  
% 35.80/4.98  --bmc1_incremental                      false
% 35.80/4.98  --bmc1_axioms                           reachable_all
% 35.80/4.98  --bmc1_min_bound                        0
% 35.80/4.98  --bmc1_max_bound                        -1
% 35.80/4.98  --bmc1_max_bound_default                -1
% 35.80/4.98  --bmc1_symbol_reachability              true
% 35.80/4.98  --bmc1_property_lemmas                  false
% 35.80/4.98  --bmc1_k_induction                      false
% 35.80/4.98  --bmc1_non_equiv_states                 false
% 35.80/4.98  --bmc1_deadlock                         false
% 35.80/4.98  --bmc1_ucm                              false
% 35.80/4.98  --bmc1_add_unsat_core                   none
% 35.80/4.98  --bmc1_unsat_core_children              false
% 35.80/4.98  --bmc1_unsat_core_extrapolate_axioms    false
% 35.80/4.98  --bmc1_out_stat                         full
% 35.80/4.98  --bmc1_ground_init                      false
% 35.80/4.98  --bmc1_pre_inst_next_state              false
% 35.80/4.98  --bmc1_pre_inst_state                   false
% 35.80/4.98  --bmc1_pre_inst_reach_state             false
% 35.80/4.98  --bmc1_out_unsat_core                   false
% 35.80/4.98  --bmc1_aig_witness_out                  false
% 35.80/4.98  --bmc1_verbose                          false
% 35.80/4.98  --bmc1_dump_clauses_tptp                false
% 35.80/4.98  --bmc1_dump_unsat_core_tptp             false
% 35.80/4.98  --bmc1_dump_file                        -
% 35.80/4.98  --bmc1_ucm_expand_uc_limit              128
% 35.80/4.98  --bmc1_ucm_n_expand_iterations          6
% 35.80/4.98  --bmc1_ucm_extend_mode                  1
% 35.80/4.98  --bmc1_ucm_init_mode                    2
% 35.80/4.98  --bmc1_ucm_cone_mode                    none
% 35.80/4.98  --bmc1_ucm_reduced_relation_type        0
% 35.80/4.98  --bmc1_ucm_relax_model                  4
% 35.80/4.98  --bmc1_ucm_full_tr_after_sat            true
% 35.80/4.98  --bmc1_ucm_expand_neg_assumptions       false
% 35.80/4.98  --bmc1_ucm_layered_model                none
% 35.80/4.98  --bmc1_ucm_max_lemma_size               10
% 35.80/4.98  
% 35.80/4.98  ------ AIG Options
% 35.80/4.98  
% 35.80/4.98  --aig_mode                              false
% 35.80/4.98  
% 35.80/4.98  ------ Instantiation Options
% 35.80/4.98  
% 35.80/4.98  --instantiation_flag                    true
% 35.80/4.98  --inst_sos_flag                         false
% 35.80/4.98  --inst_sos_phase                        true
% 35.80/4.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.80/4.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.80/4.98  --inst_lit_sel_side                     num_symb
% 35.80/4.98  --inst_solver_per_active                1400
% 35.80/4.98  --inst_solver_calls_frac                1.
% 35.80/4.98  --inst_passive_queue_type               priority_queues
% 35.80/4.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.80/4.98  --inst_passive_queues_freq              [25;2]
% 35.80/4.98  --inst_dismatching                      true
% 35.80/4.98  --inst_eager_unprocessed_to_passive     true
% 35.80/4.98  --inst_prop_sim_given                   true
% 35.80/4.98  --inst_prop_sim_new                     false
% 35.80/4.98  --inst_subs_new                         false
% 35.80/4.98  --inst_eq_res_simp                      false
% 35.80/4.98  --inst_subs_given                       false
% 35.80/4.98  --inst_orphan_elimination               true
% 35.80/4.98  --inst_learning_loop_flag               true
% 35.80/4.98  --inst_learning_start                   3000
% 35.80/4.98  --inst_learning_factor                  2
% 35.80/4.98  --inst_start_prop_sim_after_learn       3
% 35.80/4.98  --inst_sel_renew                        solver
% 35.80/4.98  --inst_lit_activity_flag                true
% 35.80/4.98  --inst_restr_to_given                   false
% 35.80/4.98  --inst_activity_threshold               500
% 35.80/4.98  --inst_out_proof                        true
% 35.80/4.98  
% 35.80/4.98  ------ Resolution Options
% 35.80/4.98  
% 35.80/4.98  --resolution_flag                       true
% 35.80/4.98  --res_lit_sel                           adaptive
% 35.80/4.98  --res_lit_sel_side                      none
% 35.80/4.98  --res_ordering                          kbo
% 35.80/4.98  --res_to_prop_solver                    active
% 35.80/4.98  --res_prop_simpl_new                    false
% 35.80/4.98  --res_prop_simpl_given                  true
% 35.80/4.98  --res_passive_queue_type                priority_queues
% 35.80/4.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.80/4.98  --res_passive_queues_freq               [15;5]
% 35.80/4.98  --res_forward_subs                      full
% 35.80/4.98  --res_backward_subs                     full
% 35.80/4.98  --res_forward_subs_resolution           true
% 35.80/4.98  --res_backward_subs_resolution          true
% 35.80/4.98  --res_orphan_elimination                true
% 35.80/4.98  --res_time_limit                        2.
% 35.80/4.98  --res_out_proof                         true
% 35.80/4.98  
% 35.80/4.98  ------ Superposition Options
% 35.80/4.98  
% 35.80/4.98  --superposition_flag                    true
% 35.80/4.98  --sup_passive_queue_type                priority_queues
% 35.80/4.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.80/4.98  --sup_passive_queues_freq               [1;4]
% 35.80/4.98  --demod_completeness_check              fast
% 35.80/4.98  --demod_use_ground                      true
% 35.80/4.98  --sup_to_prop_solver                    passive
% 35.80/4.98  --sup_prop_simpl_new                    true
% 35.80/4.98  --sup_prop_simpl_given                  true
% 35.80/4.98  --sup_fun_splitting                     false
% 35.80/4.98  --sup_smt_interval                      50000
% 35.80/4.98  
% 35.80/4.98  ------ Superposition Simplification Setup
% 35.80/4.98  
% 35.80/4.98  --sup_indices_passive                   []
% 35.80/4.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.80/4.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.80/4.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.80/4.98  --sup_full_triv                         [TrivRules;PropSubs]
% 35.80/4.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.80/4.98  --sup_full_bw                           [BwDemod]
% 35.80/4.98  --sup_immed_triv                        [TrivRules]
% 35.80/4.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.80/4.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.80/4.98  --sup_immed_bw_main                     []
% 35.80/4.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.80/4.98  --sup_input_triv                        [Unflattening;TrivRules]
% 35.80/4.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.80/4.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.80/4.98  
% 35.80/4.98  ------ Combination Options
% 35.80/4.98  
% 35.80/4.98  --comb_res_mult                         3
% 35.80/4.98  --comb_sup_mult                         2
% 35.80/4.98  --comb_inst_mult                        10
% 35.80/4.98  
% 35.80/4.98  ------ Debug Options
% 35.80/4.98  
% 35.80/4.98  --dbg_backtrace                         false
% 35.80/4.98  --dbg_dump_prop_clauses                 false
% 35.80/4.98  --dbg_dump_prop_clauses_file            -
% 35.80/4.98  --dbg_out_stat                          false
% 35.80/4.98  ------ Parsing...
% 35.80/4.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.80/4.98  
% 35.80/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 35.80/4.98  
% 35.80/4.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.80/4.98  
% 35.80/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.80/4.98  ------ Proving...
% 35.80/4.98  ------ Problem Properties 
% 35.80/4.98  
% 35.80/4.98  
% 35.80/4.98  clauses                                 20
% 35.80/4.98  conjectures                             4
% 35.80/4.98  EPR                                     5
% 35.80/4.98  Horn                                    16
% 35.80/4.98  unary                                   8
% 35.80/4.98  binary                                  10
% 35.80/4.98  lits                                    34
% 35.80/4.98  lits eq                                 6
% 35.80/4.98  fd_pure                                 0
% 35.80/4.98  fd_pseudo                               0
% 35.80/4.98  fd_cond                                 0
% 35.80/4.98  fd_pseudo_cond                          0
% 35.80/4.98  AC symbols                              0
% 35.80/4.98  
% 35.80/4.98  ------ Input Options Time Limit: Unbounded
% 35.80/4.98  
% 35.80/4.98  
% 35.80/4.98  ------ 
% 35.80/4.98  Current options:
% 35.80/4.98  ------ 
% 35.80/4.98  
% 35.80/4.98  ------ Input Options
% 35.80/4.98  
% 35.80/4.98  --out_options                           all
% 35.80/4.98  --tptp_safe_out                         true
% 35.80/4.98  --problem_path                          ""
% 35.80/4.98  --include_path                          ""
% 35.80/4.98  --clausifier                            res/vclausify_rel
% 35.80/4.98  --clausifier_options                    --mode clausify
% 35.80/4.98  --stdin                                 false
% 35.80/4.98  --stats_out                             sel
% 35.80/4.98  
% 35.80/4.98  ------ General Options
% 35.80/4.98  
% 35.80/4.98  --fof                                   false
% 35.80/4.98  --time_out_real                         604.99
% 35.80/4.98  --time_out_virtual                      -1.
% 35.80/4.98  --symbol_type_check                     false
% 35.80/4.98  --clausify_out                          false
% 35.80/4.98  --sig_cnt_out                           false
% 35.80/4.98  --trig_cnt_out                          false
% 35.80/4.98  --trig_cnt_out_tolerance                1.
% 35.80/4.98  --trig_cnt_out_sk_spl                   false
% 35.80/4.98  --abstr_cl_out                          false
% 35.80/4.98  
% 35.80/4.98  ------ Global Options
% 35.80/4.98  
% 35.80/4.98  --schedule                              none
% 35.80/4.98  --add_important_lit                     false
% 35.80/4.98  --prop_solver_per_cl                    1000
% 35.80/4.98  --min_unsat_core                        false
% 35.80/4.98  --soft_assumptions                      false
% 35.80/4.98  --soft_lemma_size                       3
% 35.80/4.98  --prop_impl_unit_size                   0
% 35.80/4.98  --prop_impl_unit                        []
% 35.80/4.98  --share_sel_clauses                     true
% 35.80/4.98  --reset_solvers                         false
% 35.80/4.98  --bc_imp_inh                            [conj_cone]
% 35.80/4.98  --conj_cone_tolerance                   3.
% 35.80/4.98  --extra_neg_conj                        none
% 35.80/4.98  --large_theory_mode                     true
% 35.80/4.98  --prolific_symb_bound                   200
% 35.80/4.98  --lt_threshold                          2000
% 35.80/4.98  --clause_weak_htbl                      true
% 35.80/4.98  --gc_record_bc_elim                     false
% 35.80/4.98  
% 35.80/4.98  ------ Preprocessing Options
% 35.80/4.98  
% 35.80/4.98  --preprocessing_flag                    true
% 35.80/4.98  --time_out_prep_mult                    0.1
% 35.80/4.98  --splitting_mode                        input
% 35.80/4.98  --splitting_grd                         true
% 35.80/4.98  --splitting_cvd                         false
% 35.80/4.98  --splitting_cvd_svl                     false
% 35.80/4.98  --splitting_nvd                         32
% 35.80/4.98  --sub_typing                            true
% 35.80/4.98  --prep_gs_sim                           false
% 35.80/4.98  --prep_unflatten                        true
% 35.80/4.98  --prep_res_sim                          true
% 35.80/4.98  --prep_upred                            true
% 35.80/4.98  --prep_sem_filter                       exhaustive
% 35.80/4.98  --prep_sem_filter_out                   false
% 35.80/4.98  --pred_elim                             false
% 35.80/4.98  --res_sim_input                         true
% 35.80/4.98  --eq_ax_congr_red                       true
% 35.80/4.98  --pure_diseq_elim                       true
% 35.80/4.98  --brand_transform                       false
% 35.80/4.98  --non_eq_to_eq                          false
% 35.80/4.98  --prep_def_merge                        true
% 35.80/4.98  --prep_def_merge_prop_impl              false
% 35.80/4.98  --prep_def_merge_mbd                    true
% 35.80/4.98  --prep_def_merge_tr_red                 false
% 35.80/4.98  --prep_def_merge_tr_cl                  false
% 35.80/4.98  --smt_preprocessing                     true
% 35.80/4.98  --smt_ac_axioms                         fast
% 35.80/4.98  --preprocessed_out                      false
% 35.80/4.98  --preprocessed_stats                    false
% 35.80/4.98  
% 35.80/4.98  ------ Abstraction refinement Options
% 35.80/4.98  
% 35.80/4.98  --abstr_ref                             []
% 35.80/4.98  --abstr_ref_prep                        false
% 35.80/4.98  --abstr_ref_until_sat                   false
% 35.80/4.98  --abstr_ref_sig_restrict                funpre
% 35.80/4.98  --abstr_ref_af_restrict_to_split_sk     false
% 35.80/4.98  --abstr_ref_under                       []
% 35.80/4.98  
% 35.80/4.98  ------ SAT Options
% 35.80/4.98  
% 35.80/4.98  --sat_mode                              false
% 35.80/4.98  --sat_fm_restart_options                ""
% 35.80/4.98  --sat_gr_def                            false
% 35.80/4.98  --sat_epr_types                         true
% 35.80/4.98  --sat_non_cyclic_types                  false
% 35.80/4.98  --sat_finite_models                     false
% 35.80/4.98  --sat_fm_lemmas                         false
% 35.80/4.98  --sat_fm_prep                           false
% 35.80/4.98  --sat_fm_uc_incr                        true
% 35.80/4.98  --sat_out_model                         small
% 35.80/4.98  --sat_out_clauses                       false
% 35.80/4.98  
% 35.80/4.98  ------ QBF Options
% 35.80/4.98  
% 35.80/4.98  --qbf_mode                              false
% 35.80/4.98  --qbf_elim_univ                         false
% 35.80/4.98  --qbf_dom_inst                          none
% 35.80/4.98  --qbf_dom_pre_inst                      false
% 35.80/4.98  --qbf_sk_in                             false
% 35.80/4.98  --qbf_pred_elim                         true
% 35.80/4.98  --qbf_split                             512
% 35.80/4.98  
% 35.80/4.98  ------ BMC1 Options
% 35.80/4.98  
% 35.80/4.98  --bmc1_incremental                      false
% 35.80/4.98  --bmc1_axioms                           reachable_all
% 35.80/4.98  --bmc1_min_bound                        0
% 35.80/4.98  --bmc1_max_bound                        -1
% 35.80/4.98  --bmc1_max_bound_default                -1
% 35.80/4.98  --bmc1_symbol_reachability              true
% 35.80/4.98  --bmc1_property_lemmas                  false
% 35.80/4.98  --bmc1_k_induction                      false
% 35.80/4.98  --bmc1_non_equiv_states                 false
% 35.80/4.98  --bmc1_deadlock                         false
% 35.80/4.98  --bmc1_ucm                              false
% 35.80/4.98  --bmc1_add_unsat_core                   none
% 35.80/4.98  --bmc1_unsat_core_children              false
% 35.80/4.98  --bmc1_unsat_core_extrapolate_axioms    false
% 35.80/4.98  --bmc1_out_stat                         full
% 35.80/4.98  --bmc1_ground_init                      false
% 35.80/4.98  --bmc1_pre_inst_next_state              false
% 35.80/4.98  --bmc1_pre_inst_state                   false
% 35.80/4.98  --bmc1_pre_inst_reach_state             false
% 35.80/4.98  --bmc1_out_unsat_core                   false
% 35.80/4.98  --bmc1_aig_witness_out                  false
% 35.80/4.98  --bmc1_verbose                          false
% 35.80/4.98  --bmc1_dump_clauses_tptp                false
% 35.80/4.98  --bmc1_dump_unsat_core_tptp             false
% 35.80/4.98  --bmc1_dump_file                        -
% 35.80/4.98  --bmc1_ucm_expand_uc_limit              128
% 35.80/4.98  --bmc1_ucm_n_expand_iterations          6
% 35.80/4.98  --bmc1_ucm_extend_mode                  1
% 35.80/4.98  --bmc1_ucm_init_mode                    2
% 35.80/4.98  --bmc1_ucm_cone_mode                    none
% 35.80/4.98  --bmc1_ucm_reduced_relation_type        0
% 35.80/4.98  --bmc1_ucm_relax_model                  4
% 35.80/4.98  --bmc1_ucm_full_tr_after_sat            true
% 35.80/4.98  --bmc1_ucm_expand_neg_assumptions       false
% 35.80/4.98  --bmc1_ucm_layered_model                none
% 35.80/4.98  --bmc1_ucm_max_lemma_size               10
% 35.80/4.98  
% 35.80/4.98  ------ AIG Options
% 35.80/4.98  
% 35.80/4.98  --aig_mode                              false
% 35.80/4.98  
% 35.80/4.98  ------ Instantiation Options
% 35.80/4.98  
% 35.80/4.98  --instantiation_flag                    true
% 35.80/4.98  --inst_sos_flag                         false
% 35.80/4.98  --inst_sos_phase                        true
% 35.80/4.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.80/4.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.80/4.98  --inst_lit_sel_side                     num_symb
% 35.80/4.98  --inst_solver_per_active                1400
% 35.80/4.98  --inst_solver_calls_frac                1.
% 35.80/4.98  --inst_passive_queue_type               priority_queues
% 35.80/4.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.80/4.98  --inst_passive_queues_freq              [25;2]
% 35.80/4.98  --inst_dismatching                      true
% 35.80/4.98  --inst_eager_unprocessed_to_passive     true
% 35.80/4.98  --inst_prop_sim_given                   true
% 35.80/4.98  --inst_prop_sim_new                     false
% 35.80/4.98  --inst_subs_new                         false
% 35.80/4.98  --inst_eq_res_simp                      false
% 35.80/4.98  --inst_subs_given                       false
% 35.80/4.98  --inst_orphan_elimination               true
% 35.80/4.98  --inst_learning_loop_flag               true
% 35.80/4.98  --inst_learning_start                   3000
% 35.80/4.98  --inst_learning_factor                  2
% 35.80/4.98  --inst_start_prop_sim_after_learn       3
% 35.80/4.98  --inst_sel_renew                        solver
% 35.80/4.98  --inst_lit_activity_flag                true
% 35.80/4.98  --inst_restr_to_given                   false
% 35.80/4.98  --inst_activity_threshold               500
% 35.80/4.98  --inst_out_proof                        true
% 35.80/4.98  
% 35.80/4.98  ------ Resolution Options
% 35.80/4.98  
% 35.80/4.98  --resolution_flag                       true
% 35.80/4.98  --res_lit_sel                           adaptive
% 35.80/4.98  --res_lit_sel_side                      none
% 35.80/4.98  --res_ordering                          kbo
% 35.80/4.98  --res_to_prop_solver                    active
% 35.80/4.98  --res_prop_simpl_new                    false
% 35.80/4.98  --res_prop_simpl_given                  true
% 35.80/4.98  --res_passive_queue_type                priority_queues
% 35.80/4.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.80/4.98  --res_passive_queues_freq               [15;5]
% 35.80/4.98  --res_forward_subs                      full
% 35.80/4.98  --res_backward_subs                     full
% 35.80/4.98  --res_forward_subs_resolution           true
% 35.80/4.98  --res_backward_subs_resolution          true
% 35.80/4.98  --res_orphan_elimination                true
% 35.80/4.98  --res_time_limit                        2.
% 35.80/4.98  --res_out_proof                         true
% 35.80/4.98  
% 35.80/4.98  ------ Superposition Options
% 35.80/4.98  
% 35.80/4.98  --superposition_flag                    true
% 35.80/4.98  --sup_passive_queue_type                priority_queues
% 35.80/4.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.80/4.98  --sup_passive_queues_freq               [1;4]
% 35.80/4.98  --demod_completeness_check              fast
% 35.80/4.98  --demod_use_ground                      true
% 35.80/4.98  --sup_to_prop_solver                    passive
% 35.80/4.98  --sup_prop_simpl_new                    true
% 35.80/4.98  --sup_prop_simpl_given                  true
% 35.80/4.98  --sup_fun_splitting                     false
% 35.80/4.98  --sup_smt_interval                      50000
% 35.80/4.98  
% 35.80/4.98  ------ Superposition Simplification Setup
% 35.80/4.98  
% 35.80/4.98  --sup_indices_passive                   []
% 35.80/4.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.80/4.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.80/4.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.80/4.98  --sup_full_triv                         [TrivRules;PropSubs]
% 35.80/4.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.80/4.98  --sup_full_bw                           [BwDemod]
% 35.80/4.98  --sup_immed_triv                        [TrivRules]
% 35.80/4.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.80/4.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.80/4.98  --sup_immed_bw_main                     []
% 35.80/4.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.80/4.98  --sup_input_triv                        [Unflattening;TrivRules]
% 35.80/4.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.80/4.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.80/4.98  
% 35.80/4.98  ------ Combination Options
% 35.80/4.98  
% 35.80/4.98  --comb_res_mult                         3
% 35.80/4.98  --comb_sup_mult                         2
% 35.80/4.98  --comb_inst_mult                        10
% 35.80/4.98  
% 35.80/4.98  ------ Debug Options
% 35.80/4.98  
% 35.80/4.98  --dbg_backtrace                         false
% 35.80/4.98  --dbg_dump_prop_clauses                 false
% 35.80/4.98  --dbg_dump_prop_clauses_file            -
% 35.80/4.98  --dbg_out_stat                          false
% 35.80/4.98  
% 35.80/4.98  
% 35.80/4.98  
% 35.80/4.98  
% 35.80/4.98  ------ Proving...
% 35.80/4.98  
% 35.80/4.98  
% 35.80/4.98  % SZS status Theorem for theBenchmark.p
% 35.80/4.98  
% 35.80/4.98  % SZS output start CNFRefutation for theBenchmark.p
% 35.80/4.98  
% 35.80/4.98  fof(f2,axiom,(
% 35.80/4.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.80/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.80/4.98  
% 35.80/4.98  fof(f39,plain,(
% 35.80/4.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.80/4.98    inference(cnf_transformation,[],[f2])).
% 35.80/4.98  
% 35.80/4.98  fof(f6,axiom,(
% 35.80/4.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.80/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.80/4.98  
% 35.80/4.98  fof(f21,plain,(
% 35.80/4.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.80/4.98    inference(rectify,[],[f6])).
% 35.80/4.98  
% 35.80/4.98  fof(f24,plain,(
% 35.80/4.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.80/4.98    inference(ennf_transformation,[],[f21])).
% 35.80/4.98  
% 35.80/4.98  fof(f34,plain,(
% 35.80/4.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 35.80/4.98    introduced(choice_axiom,[])).
% 35.80/4.98  
% 35.80/4.98  fof(f35,plain,(
% 35.80/4.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.80/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f34])).
% 35.80/4.98  
% 35.80/4.98  fof(f46,plain,(
% 35.80/4.98    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 35.80/4.98    inference(cnf_transformation,[],[f35])).
% 35.80/4.98  
% 35.80/4.98  fof(f17,axiom,(
% 35.80/4.98    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 35.80/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.80/4.98  
% 35.80/4.98  fof(f28,plain,(
% 35.80/4.98    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 35.80/4.98    inference(ennf_transformation,[],[f17])).
% 35.80/4.98  
% 35.80/4.98  fof(f58,plain,(
% 35.80/4.98    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 35.80/4.98    inference(cnf_transformation,[],[f28])).
% 35.80/4.98  
% 35.80/4.98  fof(f14,axiom,(
% 35.80/4.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 35.80/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.80/4.98  
% 35.80/4.98  fof(f55,plain,(
% 35.80/4.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 35.80/4.98    inference(cnf_transformation,[],[f14])).
% 35.80/4.98  
% 35.80/4.98  fof(f15,axiom,(
% 35.80/4.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 35.80/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.80/4.98  
% 35.80/4.98  fof(f56,plain,(
% 35.80/4.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 35.80/4.98    inference(cnf_transformation,[],[f15])).
% 35.80/4.98  
% 35.80/4.98  fof(f16,axiom,(
% 35.80/4.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.80/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.80/4.98  
% 35.80/4.98  fof(f57,plain,(
% 35.80/4.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.80/4.98    inference(cnf_transformation,[],[f16])).
% 35.80/4.98  
% 35.80/4.98  fof(f64,plain,(
% 35.80/4.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 35.80/4.98    inference(definition_unfolding,[],[f56,f57])).
% 35.80/4.98  
% 35.80/4.98  fof(f65,plain,(
% 35.80/4.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 35.80/4.98    inference(definition_unfolding,[],[f55,f64])).
% 35.80/4.98  
% 35.80/4.98  fof(f68,plain,(
% 35.80/4.98    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 35.80/4.98    inference(definition_unfolding,[],[f58,f65])).
% 35.80/4.98  
% 35.80/4.98  fof(f18,conjecture,(
% 35.80/4.98    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 35.80/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.80/4.98  
% 35.80/4.98  fof(f19,negated_conjecture,(
% 35.80/4.98    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 35.80/4.98    inference(negated_conjecture,[],[f18])).
% 35.80/4.98  
% 35.80/4.98  fof(f29,plain,(
% 35.80/4.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 35.80/4.98    inference(ennf_transformation,[],[f19])).
% 35.80/4.98  
% 35.80/4.98  fof(f30,plain,(
% 35.80/4.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 35.80/4.98    inference(flattening,[],[f29])).
% 35.80/4.98  
% 35.80/4.98  fof(f36,plain,(
% 35.80/4.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 35.80/4.98    introduced(choice_axiom,[])).
% 35.80/4.98  
% 35.80/4.98  fof(f37,plain,(
% 35.80/4.98    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 35.80/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f36])).
% 35.80/4.98  
% 35.80/4.98  fof(f59,plain,(
% 35.80/4.98    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 35.80/4.98    inference(cnf_transformation,[],[f37])).
% 35.80/4.98  
% 35.80/4.98  fof(f70,plain,(
% 35.80/4.98    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))),
% 35.80/4.98    inference(definition_unfolding,[],[f59,f65])).
% 35.80/4.98  
% 35.80/4.98  fof(f9,axiom,(
% 35.80/4.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.80/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.80/4.98  
% 35.80/4.98  fof(f25,plain,(
% 35.80/4.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.80/4.98    inference(ennf_transformation,[],[f9])).
% 35.80/4.98  
% 35.80/4.98  fof(f50,plain,(
% 35.80/4.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.80/4.98    inference(cnf_transformation,[],[f25])).
% 35.80/4.98  
% 35.80/4.98  fof(f47,plain,(
% 35.80/4.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 35.80/4.98    inference(cnf_transformation,[],[f35])).
% 35.80/4.98  
% 35.80/4.98  fof(f60,plain,(
% 35.80/4.98    r2_hidden(sK5,sK4)),
% 35.80/4.98    inference(cnf_transformation,[],[f37])).
% 35.80/4.98  
% 35.80/4.98  fof(f61,plain,(
% 35.80/4.98    r1_xboole_0(sK4,sK3)),
% 35.80/4.98    inference(cnf_transformation,[],[f37])).
% 35.80/4.98  
% 35.80/4.98  fof(f5,axiom,(
% 35.80/4.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 35.80/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.80/4.98  
% 35.80/4.98  fof(f20,plain,(
% 35.80/4.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 35.80/4.98    inference(rectify,[],[f5])).
% 35.80/4.98  
% 35.80/4.98  fof(f23,plain,(
% 35.80/4.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 35.80/4.98    inference(ennf_transformation,[],[f20])).
% 35.80/4.98  
% 35.80/4.98  fof(f32,plain,(
% 35.80/4.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 35.80/4.98    introduced(choice_axiom,[])).
% 35.80/4.98  
% 35.80/4.98  fof(f33,plain,(
% 35.80/4.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 35.80/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f32])).
% 35.80/4.98  
% 35.80/4.98  fof(f45,plain,(
% 35.80/4.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 35.80/4.98    inference(cnf_transformation,[],[f33])).
% 35.80/4.98  
% 35.80/4.98  fof(f3,axiom,(
% 35.80/4.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 35.80/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.80/4.98  
% 35.80/4.98  fof(f31,plain,(
% 35.80/4.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 35.80/4.98    inference(nnf_transformation,[],[f3])).
% 35.80/4.98  
% 35.80/4.98  fof(f40,plain,(
% 35.80/4.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 35.80/4.98    inference(cnf_transformation,[],[f31])).
% 35.80/4.98  
% 35.80/4.98  fof(f41,plain,(
% 35.80/4.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 35.80/4.98    inference(cnf_transformation,[],[f31])).
% 35.80/4.98  
% 35.80/4.98  fof(f4,axiom,(
% 35.80/4.98    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 35.80/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.80/4.98  
% 35.80/4.98  fof(f22,plain,(
% 35.80/4.98    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 35.80/4.98    inference(ennf_transformation,[],[f4])).
% 35.80/4.98  
% 35.80/4.98  fof(f42,plain,(
% 35.80/4.98    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 35.80/4.98    inference(cnf_transformation,[],[f22])).
% 35.80/4.98  
% 35.80/4.98  fof(f44,plain,(
% 35.80/4.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 35.80/4.98    inference(cnf_transformation,[],[f33])).
% 35.80/4.98  
% 35.80/4.98  fof(f11,axiom,(
% 35.80/4.98    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 35.80/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.80/4.98  
% 35.80/4.98  fof(f26,plain,(
% 35.80/4.98    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 35.80/4.98    inference(ennf_transformation,[],[f11])).
% 35.80/4.98  
% 35.80/4.98  fof(f52,plain,(
% 35.80/4.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 35.80/4.98    inference(cnf_transformation,[],[f26])).
% 35.80/4.98  
% 35.80/4.98  fof(f8,axiom,(
% 35.80/4.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 35.80/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.80/4.98  
% 35.80/4.98  fof(f49,plain,(
% 35.80/4.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 35.80/4.98    inference(cnf_transformation,[],[f8])).
% 35.80/4.98  
% 35.80/4.98  fof(f12,axiom,(
% 35.80/4.98    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 35.80/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.80/4.98  
% 35.80/4.98  fof(f27,plain,(
% 35.80/4.98    ! [X0,X1,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 35.80/4.98    inference(ennf_transformation,[],[f12])).
% 35.80/4.98  
% 35.80/4.98  fof(f53,plain,(
% 35.80/4.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 35.80/4.98    inference(cnf_transformation,[],[f27])).
% 35.80/4.98  
% 35.80/4.98  fof(f13,axiom,(
% 35.80/4.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 35.80/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.80/4.98  
% 35.80/4.98  fof(f54,plain,(
% 35.80/4.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 35.80/4.98    inference(cnf_transformation,[],[f13])).
% 35.80/4.98  
% 35.80/4.98  fof(f7,axiom,(
% 35.80/4.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 35.80/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.80/4.98  
% 35.80/4.98  fof(f48,plain,(
% 35.80/4.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.80/4.98    inference(cnf_transformation,[],[f7])).
% 35.80/4.98  
% 35.80/4.98  fof(f63,plain,(
% 35.80/4.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 35.80/4.98    inference(definition_unfolding,[],[f54,f48])).
% 35.80/4.98  
% 35.80/4.98  fof(f67,plain,(
% 35.80/4.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) | ~r1_xboole_0(X0,X1)) )),
% 35.80/4.98    inference(definition_unfolding,[],[f53,f63])).
% 35.80/4.98  
% 35.80/4.98  fof(f43,plain,(
% 35.80/4.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 35.80/4.98    inference(cnf_transformation,[],[f33])).
% 35.80/4.98  
% 35.80/4.98  fof(f62,plain,(
% 35.80/4.98    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 35.80/4.98    inference(cnf_transformation,[],[f37])).
% 35.80/4.98  
% 35.80/4.98  fof(f69,plain,(
% 35.80/4.98    ~r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3)),
% 35.80/4.98    inference(definition_unfolding,[],[f62,f63])).
% 35.80/4.98  
% 35.80/4.98  cnf(c_1,plain,
% 35.80/4.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 35.80/4.98      inference(cnf_transformation,[],[f39]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_225,plain,
% 35.80/4.98      ( k3_xboole_0(X0_41,X1_41) = k3_xboole_0(X1_41,X0_41) ),
% 35.80/4.98      inference(subtyping,[status(esa)],[c_1]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_9,plain,
% 35.80/4.98      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 35.80/4.98      inference(cnf_transformation,[],[f46]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_217,plain,
% 35.80/4.98      ( r2_hidden(sK1(X0_41,X1_41),k3_xboole_0(X0_41,X1_41))
% 35.80/4.98      | r1_xboole_0(X0_41,X1_41) ),
% 35.80/4.98      inference(subtyping,[status(esa)],[c_9]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_672,plain,
% 35.80/4.98      ( r2_hidden(sK1(X0_41,X1_41),k3_xboole_0(X0_41,X1_41)) = iProver_top
% 35.80/4.98      | r1_xboole_0(X0_41,X1_41) = iProver_top ),
% 35.80/4.98      inference(predicate_to_equality,[status(thm)],[c_217]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_1953,plain,
% 35.80/4.98      ( r2_hidden(sK1(X0_41,X1_41),k3_xboole_0(X1_41,X0_41)) = iProver_top
% 35.80/4.98      | r1_xboole_0(X0_41,X1_41) = iProver_top ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_225,c_672]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_15,plain,
% 35.80/4.98      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 35.80/4.98      inference(cnf_transformation,[],[f68]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_211,plain,
% 35.80/4.98      ( r2_hidden(X0_42,X0_41)
% 35.80/4.98      | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),X0_41) ),
% 35.80/4.98      inference(subtyping,[status(esa)],[c_15]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_678,plain,
% 35.80/4.98      ( r2_hidden(X0_42,X0_41) = iProver_top
% 35.80/4.98      | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),X0_41) = iProver_top ),
% 35.80/4.98      inference(predicate_to_equality,[status(thm)],[c_211]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_19,negated_conjecture,
% 35.80/4.98      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 35.80/4.98      inference(cnf_transformation,[],[f70]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_207,negated_conjecture,
% 35.80/4.98      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 35.80/4.98      inference(subtyping,[status(esa)],[c_19]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_682,plain,
% 35.80/4.98      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 35.80/4.98      inference(predicate_to_equality,[status(thm)],[c_207]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_11,plain,
% 35.80/4.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 35.80/4.98      inference(cnf_transformation,[],[f50]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_215,plain,
% 35.80/4.98      ( ~ r1_tarski(X0_41,X1_41) | k3_xboole_0(X0_41,X1_41) = X0_41 ),
% 35.80/4.98      inference(subtyping,[status(esa)],[c_11]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_674,plain,
% 35.80/4.98      ( k3_xboole_0(X0_41,X1_41) = X0_41
% 35.80/4.98      | r1_tarski(X0_41,X1_41) != iProver_top ),
% 35.80/4.98      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_1421,plain,
% 35.80/4.98      ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_682,c_674]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_8,plain,
% 35.80/4.98      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 35.80/4.98      inference(cnf_transformation,[],[f47]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_218,plain,
% 35.80/4.98      ( ~ r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41))
% 35.80/4.98      | ~ r1_xboole_0(X0_41,X1_41) ),
% 35.80/4.98      inference(subtyping,[status(esa)],[c_8]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_671,plain,
% 35.80/4.98      ( r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41)) != iProver_top
% 35.80/4.98      | r1_xboole_0(X0_41,X1_41) != iProver_top ),
% 35.80/4.98      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_1933,plain,
% 35.80/4.98      ( r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41)) != iProver_top
% 35.80/4.98      | r1_xboole_0(X1_41,X0_41) != iProver_top ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_225,c_671]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_3736,plain,
% 35.80/4.98      ( r2_hidden(X0_42,k3_xboole_0(sK2,sK3)) != iProver_top
% 35.80/4.98      | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)) != iProver_top ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_1421,c_1933]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_23716,plain,
% 35.80/4.98      ( r2_hidden(X0_42,k3_xboole_0(sK2,sK3)) != iProver_top
% 35.80/4.98      | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) = iProver_top ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_678,c_3736]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_18,negated_conjecture,
% 35.80/4.98      ( r2_hidden(sK5,sK4) ),
% 35.80/4.98      inference(cnf_transformation,[],[f60]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_17,negated_conjecture,
% 35.80/4.98      ( r1_xboole_0(sK4,sK3) ),
% 35.80/4.98      inference(cnf_transformation,[],[f61]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_5,plain,
% 35.80/4.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 35.80/4.98      inference(cnf_transformation,[],[f45]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_221,plain,
% 35.80/4.98      ( ~ r2_hidden(X0_42,X0_41)
% 35.80/4.98      | ~ r2_hidden(X0_42,X1_41)
% 35.80/4.98      | ~ r1_xboole_0(X0_41,X1_41) ),
% 35.80/4.98      inference(subtyping,[status(esa)],[c_5]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_869,plain,
% 35.80/4.98      ( ~ r2_hidden(X0_42,sK3)
% 35.80/4.98      | ~ r2_hidden(X0_42,sK4)
% 35.80/4.98      | ~ r1_xboole_0(sK4,sK3) ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_221]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_871,plain,
% 35.80/4.98      ( ~ r2_hidden(sK5,sK3)
% 35.80/4.98      | ~ r2_hidden(sK5,sK4)
% 35.80/4.98      | ~ r1_xboole_0(sK4,sK3) ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_869]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_989,plain,
% 35.80/4.98      ( r2_hidden(X0_42,sK3)
% 35.80/4.98      | r1_xboole_0(k2_enumset1(X0_42,X0_42,X0_42,X0_42),sK3) ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_211]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_991,plain,
% 35.80/4.98      ( r2_hidden(sK5,sK3)
% 35.80/4.98      | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_989]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_3739,plain,
% 35.80/4.98      ( r2_hidden(X0_42,k3_xboole_0(sK2,sK3)) != iProver_top
% 35.80/4.98      | r1_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_1421,c_671]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_3,plain,
% 35.80/4.98      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 35.80/4.98      inference(cnf_transformation,[],[f40]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_223,plain,
% 35.80/4.98      ( ~ r1_xboole_0(X0_41,X1_41)
% 35.80/4.98      | k3_xboole_0(X0_41,X1_41) = k1_xboole_0 ),
% 35.80/4.98      inference(subtyping,[status(esa)],[c_3]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_2868,plain,
% 35.80/4.98      ( ~ r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41)
% 35.80/4.98      | k3_xboole_0(k3_xboole_0(sK2,sK3),X0_41) = k1_xboole_0 ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_223]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_6443,plain,
% 35.80/4.98      ( ~ r1_xboole_0(k3_xboole_0(sK2,sK3),sK3)
% 35.80/4.98      | k3_xboole_0(k3_xboole_0(sK2,sK3),sK3) = k1_xboole_0 ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_2868]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_2,plain,
% 35.80/4.98      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 35.80/4.98      inference(cnf_transformation,[],[f41]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_224,plain,
% 35.80/4.98      ( r1_xboole_0(X0_41,X1_41)
% 35.80/4.98      | k3_xboole_0(X0_41,X1_41) != k1_xboole_0 ),
% 35.80/4.98      inference(subtyping,[status(esa)],[c_2]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_1799,plain,
% 35.80/4.98      ( r1_xboole_0(X0_41,sK3) | k3_xboole_0(X0_41,sK3) != k1_xboole_0 ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_224]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_6445,plain,
% 35.80/4.98      ( r1_xboole_0(k3_xboole_0(sK2,sK3),sK3)
% 35.80/4.98      | k3_xboole_0(k3_xboole_0(sK2,sK3),sK3) != k1_xboole_0 ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_1799]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_6457,plain,
% 35.80/4.98      ( k3_xboole_0(k3_xboole_0(sK2,sK3),sK3) != k1_xboole_0
% 35.80/4.98      | r1_xboole_0(k3_xboole_0(sK2,sK3),sK3) = iProver_top ),
% 35.80/4.98      inference(predicate_to_equality,[status(thm)],[c_6445]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_4,plain,
% 35.80/4.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 35.80/4.98      inference(cnf_transformation,[],[f42]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_222,plain,
% 35.80/4.98      ( ~ r1_xboole_0(X0_41,X1_41) | r1_xboole_0(X1_41,X0_41) ),
% 35.80/4.98      inference(subtyping,[status(esa)],[c_4]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_2869,plain,
% 35.80/4.98      ( r1_xboole_0(X0_41,k3_xboole_0(sK2,sK3))
% 35.80/4.98      | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41) ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_222]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_6542,plain,
% 35.80/4.98      ( ~ r1_xboole_0(k3_xboole_0(sK2,sK3),sK3)
% 35.80/4.98      | r1_xboole_0(sK3,k3_xboole_0(sK2,sK3)) ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_2869]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_6544,plain,
% 35.80/4.98      ( r1_xboole_0(k3_xboole_0(sK2,sK3),sK3) != iProver_top
% 35.80/4.98      | r1_xboole_0(sK3,k3_xboole_0(sK2,sK3)) = iProver_top ),
% 35.80/4.98      inference(predicate_to_equality,[status(thm)],[c_6542]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_1305,plain,
% 35.80/4.98      ( ~ r2_hidden(X0_42,k3_xboole_0(sK3,X0_41))
% 35.80/4.98      | ~ r1_xboole_0(sK3,X0_41) ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_218]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_3412,plain,
% 35.80/4.98      ( ~ r2_hidden(sK0(X0_41,k3_xboole_0(sK3,X1_41)),k3_xboole_0(sK3,X1_41))
% 35.80/4.98      | ~ r1_xboole_0(sK3,X1_41) ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_1305]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_11861,plain,
% 35.80/4.98      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))),k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))
% 35.80/4.98      | ~ r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_3412]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_6,plain,
% 35.80/4.98      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 35.80/4.98      inference(cnf_transformation,[],[f44]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_220,plain,
% 35.80/4.98      ( r2_hidden(sK0(X0_41,X1_41),X1_41) | r1_xboole_0(X0_41,X1_41) ),
% 35.80/4.98      inference(subtyping,[status(esa)],[c_6]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_854,plain,
% 35.80/4.98      ( r2_hidden(sK0(X0_41,k3_xboole_0(X1_41,X2_41)),k3_xboole_0(X1_41,X2_41))
% 35.80/4.98      | r1_xboole_0(X0_41,k3_xboole_0(X1_41,X2_41)) ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_220]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_1783,plain,
% 35.80/4.98      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(X0_41,k2_enumset1(sK5,sK5,sK5,sK5))),k3_xboole_0(X0_41,k2_enumset1(sK5,sK5,sK5,sK5)))
% 35.80/4.98      | r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(X0_41,k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_854]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_11862,plain,
% 35.80/4.98      ( r2_hidden(sK0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))),k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))
% 35.80/4.98      | r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_1783]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_1131,plain,
% 35.80/4.98      ( ~ r1_xboole_0(X0_41,sK3) | r1_xboole_0(sK3,X0_41) ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_222]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_21598,plain,
% 35.80/4.98      ( ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3)
% 35.80/4.98      | r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_1131]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_13,plain,
% 35.80/4.98      ( ~ r1_tarski(X0,X1)
% 35.80/4.98      | r1_xboole_0(X0,X2)
% 35.80/4.98      | ~ r1_xboole_0(X0,k3_xboole_0(X2,X1)) ),
% 35.80/4.98      inference(cnf_transformation,[],[f52]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_213,plain,
% 35.80/4.98      ( ~ r1_tarski(X0_41,X1_41)
% 35.80/4.98      | r1_xboole_0(X0_41,X2_41)
% 35.80/4.98      | ~ r1_xboole_0(X0_41,k3_xboole_0(X2_41,X1_41)) ),
% 35.80/4.98      inference(subtyping,[status(esa)],[c_13]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_1270,plain,
% 35.80/4.98      ( ~ r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))
% 35.80/4.98      | r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41)
% 35.80/4.98      | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(X0_41,k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_213]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_43311,plain,
% 35.80/4.98      ( ~ r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))
% 35.80/4.98      | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))
% 35.80/4.98      | r1_xboole_0(k3_xboole_0(sK2,sK3),sK3) ),
% 35.80/4.98      inference(instantiation,[status(thm)],[c_1270]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_3738,plain,
% 35.80/4.98      ( r2_hidden(sK1(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)),k3_xboole_0(sK2,sK3)) = iProver_top
% 35.80/4.98      | r1_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_1421,c_672]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_10,plain,
% 35.80/4.98      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 35.80/4.98      inference(cnf_transformation,[],[f49]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_216,plain,
% 35.80/4.98      ( r1_tarski(k3_xboole_0(X0_41,X1_41),X0_41) ),
% 35.80/4.98      inference(subtyping,[status(esa)],[c_10]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_673,plain,
% 35.80/4.98      ( r1_tarski(k3_xboole_0(X0_41,X1_41),X0_41) = iProver_top ),
% 35.80/4.98      inference(predicate_to_equality,[status(thm)],[c_216]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_1070,plain,
% 35.80/4.98      ( r1_tarski(k3_xboole_0(X0_41,X1_41),X1_41) = iProver_top ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_225,c_673]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_1423,plain,
% 35.80/4.98      ( k3_xboole_0(k3_xboole_0(X0_41,X1_41),X1_41) = k3_xboole_0(X0_41,X1_41) ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_1070,c_674]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_4572,plain,
% 35.80/4.98      ( r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41)) != iProver_top
% 35.80/4.98      | r1_xboole_0(X1_41,k3_xboole_0(X0_41,X1_41)) != iProver_top ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_1423,c_1933]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_53057,plain,
% 35.80/4.98      ( r1_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
% 35.80/4.98      | r1_xboole_0(sK3,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_3738,c_4572]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_179208,plain,
% 35.80/4.98      ( r2_hidden(X0_42,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 35.80/4.98      inference(global_propositional_subsumption,
% 35.80/4.98                [status(thm)],
% 35.80/4.98                [c_23716,c_19,c_18,c_17,c_871,c_991,c_3739,c_6443,c_6457,
% 35.80/4.98                 c_6544,c_11861,c_11862,c_21598,c_43311,c_53057]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_179219,plain,
% 35.80/4.98      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_1953,c_179208]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_14,plain,
% 35.80/4.98      ( ~ r1_xboole_0(X0,X1)
% 35.80/4.98      | k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_xboole_0(X0,X2) ),
% 35.80/4.98      inference(cnf_transformation,[],[f67]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_212,plain,
% 35.80/4.98      ( ~ r1_xboole_0(X0_41,X1_41)
% 35.80/4.98      | k3_xboole_0(X0_41,k5_xboole_0(X1_41,k5_xboole_0(X2_41,k3_xboole_0(X2_41,X1_41)))) = k3_xboole_0(X0_41,X2_41) ),
% 35.80/4.98      inference(subtyping,[status(esa)],[c_14]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_677,plain,
% 35.80/4.98      ( k3_xboole_0(X0_41,k5_xboole_0(X1_41,k5_xboole_0(X2_41,k3_xboole_0(X2_41,X1_41)))) = k3_xboole_0(X0_41,X2_41)
% 35.80/4.98      | r1_xboole_0(X0_41,X1_41) != iProver_top ),
% 35.80/4.98      inference(predicate_to_equality,[status(thm)],[c_212]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_179865,plain,
% 35.80/4.98      ( k3_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK2)))) = k3_xboole_0(sK3,X0_41) ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_179219,c_677]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_668,plain,
% 35.80/4.98      ( r2_hidden(X0_42,X0_41) != iProver_top
% 35.80/4.98      | r2_hidden(X0_42,X1_41) != iProver_top
% 35.80/4.98      | r1_xboole_0(X1_41,X0_41) != iProver_top ),
% 35.80/4.98      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_2520,plain,
% 35.80/4.98      ( r2_hidden(sK1(X0_41,X1_41),X2_41) != iProver_top
% 35.80/4.98      | r1_xboole_0(X0_41,X1_41) = iProver_top
% 35.80/4.98      | r1_xboole_0(k3_xboole_0(X1_41,X0_41),X2_41) != iProver_top ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_1953,c_668]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_15254,plain,
% 35.80/4.98      ( r1_xboole_0(X0_41,X1_41) = iProver_top
% 35.80/4.98      | r1_xboole_0(k3_xboole_0(X1_41,X0_41),k3_xboole_0(X0_41,X1_41)) != iProver_top ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_672,c_2520]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_186780,plain,
% 35.80/4.98      ( r1_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK2))),sK3),k3_xboole_0(sK3,X0_41)) != iProver_top
% 35.80/4.98      | r1_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK2)))) = iProver_top ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_179865,c_15254]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_209,negated_conjecture,
% 35.80/4.98      ( r1_xboole_0(sK4,sK3) ),
% 35.80/4.98      inference(subtyping,[status(esa)],[c_17]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_680,plain,
% 35.80/4.98      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 35.80/4.98      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_666,plain,
% 35.80/4.98      ( k3_xboole_0(X0_41,X1_41) = k1_xboole_0
% 35.80/4.98      | r1_xboole_0(X0_41,X1_41) != iProver_top ),
% 35.80/4.98      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_1200,plain,
% 35.80/4.98      ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_680,c_666]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_676,plain,
% 35.80/4.98      ( r1_tarski(X0_41,X1_41) != iProver_top
% 35.80/4.98      | r1_xboole_0(X0_41,X2_41) = iProver_top
% 35.80/4.98      | r1_xboole_0(X0_41,k3_xboole_0(X2_41,X1_41)) != iProver_top ),
% 35.80/4.98      inference(predicate_to_equality,[status(thm)],[c_213]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_2967,plain,
% 35.80/4.98      ( r1_tarski(X0_41,sK3) != iProver_top
% 35.80/4.98      | r1_xboole_0(X0_41,sK4) = iProver_top
% 35.80/4.98      | r1_xboole_0(X0_41,k1_xboole_0) != iProver_top ),
% 35.80/4.98      inference(superposition,[status(thm)],[c_1200,c_676]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_1478,plain,
% 35.80/4.98      ( ~ r1_xboole_0(X0_41,X1_41)
% 35.80/4.98      | r1_xboole_0(X2_41,k3_xboole_0(X0_41,X1_41)) ),
% 35.80/4.98      inference(resolution,[status(thm)],[c_218,c_220]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_3285,plain,
% 35.80/4.98      ( ~ r1_tarski(X0_41,X1_41)
% 35.80/4.98      | ~ r1_xboole_0(X2_41,X1_41)
% 35.80/4.98      | r1_xboole_0(X0_41,X2_41) ),
% 35.80/4.98      inference(resolution,[status(thm)],[c_213,c_1478]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_3574,plain,
% 35.80/4.98      ( ~ r1_tarski(X0_41,sK3) | r1_xboole_0(X0_41,sK4) ),
% 35.80/4.98      inference(resolution,[status(thm)],[c_3285,c_209]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_3575,plain,
% 35.80/4.98      ( r1_tarski(X0_41,sK3) != iProver_top
% 35.80/4.98      | r1_xboole_0(X0_41,sK4) = iProver_top ),
% 35.80/4.98      inference(predicate_to_equality,[status(thm)],[c_3574]) ).
% 35.80/4.98  
% 35.80/4.98  cnf(c_19078,plain,
% 35.80/4.98      ( r1_xboole_0(X0_41,sK4) = iProver_top
% 35.80/4.99      | r1_tarski(X0_41,sK3) != iProver_top ),
% 35.80/4.99      inference(global_propositional_subsumption,
% 35.80/4.99                [status(thm)],
% 35.80/4.99                [c_2967,c_3575]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_19079,plain,
% 35.80/4.99      ( r1_tarski(X0_41,sK3) != iProver_top
% 35.80/4.99      | r1_xboole_0(X0_41,sK4) = iProver_top ),
% 35.80/4.99      inference(renaming,[status(thm)],[c_19078]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_19084,plain,
% 35.80/4.99      ( r1_xboole_0(k3_xboole_0(sK3,X0_41),sK4) = iProver_top ),
% 35.80/4.99      inference(superposition,[status(thm)],[c_673,c_19079]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_19358,plain,
% 35.80/4.99      ( k3_xboole_0(k3_xboole_0(sK3,X0_41),sK4) = k1_xboole_0 ),
% 35.80/4.99      inference(superposition,[status(thm)],[c_19084,c_666]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_667,plain,
% 35.80/4.99      ( r1_xboole_0(X0_41,X1_41) != iProver_top
% 35.80/4.99      | r1_xboole_0(X1_41,X0_41) = iProver_top ),
% 35.80/4.99      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_1410,plain,
% 35.80/4.99      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 35.80/4.99      inference(superposition,[status(thm)],[c_680,c_667]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_3544,plain,
% 35.80/4.99      ( k3_xboole_0(sK3,k5_xboole_0(sK4,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK4)))) = k3_xboole_0(sK3,X0_41) ),
% 35.80/4.99      inference(superposition,[status(thm)],[c_1410,c_677]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_20004,plain,
% 35.80/4.99      ( k3_xboole_0(sK3,k5_xboole_0(sK4,k5_xboole_0(k3_xboole_0(sK3,X0_41),k1_xboole_0))) = k3_xboole_0(sK3,k3_xboole_0(sK3,X0_41)) ),
% 35.80/4.99      inference(superposition,[status(thm)],[c_19358,c_3544]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_4563,plain,
% 35.80/4.99      ( k3_xboole_0(k3_xboole_0(X0_41,X1_41),X0_41) = k3_xboole_0(X1_41,X0_41) ),
% 35.80/4.99      inference(superposition,[status(thm)],[c_225,c_1423]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_5097,plain,
% 35.80/4.99      ( k3_xboole_0(X0_41,k3_xboole_0(X0_41,X1_41)) = k3_xboole_0(X1_41,X0_41) ),
% 35.80/4.99      inference(superposition,[status(thm)],[c_4563,c_225]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_20008,plain,
% 35.80/4.99      ( k3_xboole_0(sK3,k5_xboole_0(sK4,k5_xboole_0(k3_xboole_0(sK3,X0_41),k1_xboole_0))) = k3_xboole_0(X0_41,sK3) ),
% 35.80/4.99      inference(demodulation,[status(thm)],[c_20004,c_5097]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_187020,plain,
% 35.80/4.99      ( k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK2))),sK3) = k3_xboole_0(sK3,k5_xboole_0(sK4,k5_xboole_0(k3_xboole_0(sK3,X0_41),k1_xboole_0))) ),
% 35.80/4.99      inference(superposition,[status(thm)],[c_179865,c_20008]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_19085,plain,
% 35.80/4.99      ( r1_xboole_0(k3_xboole_0(X0_41,sK3),sK4) = iProver_top ),
% 35.80/4.99      inference(superposition,[status(thm)],[c_1070,c_19079]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_19389,plain,
% 35.80/4.99      ( k3_xboole_0(k3_xboole_0(X0_41,sK3),sK4) = k1_xboole_0 ),
% 35.80/4.99      inference(superposition,[status(thm)],[c_19085,c_666]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_20519,plain,
% 35.80/4.99      ( k3_xboole_0(sK3,k5_xboole_0(sK4,k5_xboole_0(k3_xboole_0(X0_41,sK3),k1_xboole_0))) = k3_xboole_0(sK3,k3_xboole_0(X0_41,sK3)) ),
% 35.80/4.99      inference(superposition,[status(thm)],[c_19389,c_3544]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_1422,plain,
% 35.80/4.99      ( k3_xboole_0(k3_xboole_0(X0_41,X1_41),X0_41) = k3_xboole_0(X0_41,X1_41) ),
% 35.80/4.99      inference(superposition,[status(thm)],[c_673,c_674]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_4314,plain,
% 35.80/4.99      ( k3_xboole_0(k3_xboole_0(X0_41,X1_41),X1_41) = k3_xboole_0(X1_41,X0_41) ),
% 35.80/4.99      inference(superposition,[status(thm)],[c_225,c_1422]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_4677,plain,
% 35.80/4.99      ( k3_xboole_0(X0_41,k3_xboole_0(X1_41,X0_41)) = k3_xboole_0(X0_41,X1_41) ),
% 35.80/4.99      inference(superposition,[status(thm)],[c_4314,c_225]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_20521,plain,
% 35.80/4.99      ( k3_xboole_0(sK3,k5_xboole_0(sK4,k5_xboole_0(k3_xboole_0(X0_41,sK3),k1_xboole_0))) = k3_xboole_0(sK3,X0_41) ),
% 35.80/4.99      inference(demodulation,[status(thm)],[c_20519,c_4677]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_26051,plain,
% 35.80/4.99      ( k3_xboole_0(sK3,k5_xboole_0(sK4,k5_xboole_0(k3_xboole_0(sK3,X0_41),k1_xboole_0))) = k3_xboole_0(sK3,X0_41) ),
% 35.80/4.99      inference(superposition,[status(thm)],[c_225,c_20521]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_187059,plain,
% 35.80/4.99      ( k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK2))),sK3) = k3_xboole_0(sK3,X0_41) ),
% 35.80/4.99      inference(light_normalisation,[status(thm)],[c_187020,c_26051]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_187514,plain,
% 35.80/4.99      ( r1_xboole_0(k3_xboole_0(sK3,X0_41),k3_xboole_0(sK3,X0_41)) != iProver_top
% 35.80/4.99      | r1_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK2)))) = iProver_top ),
% 35.80/4.99      inference(light_normalisation,[status(thm)],[c_186780,c_187059]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_187575,plain,
% 35.80/4.99      ( r1_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) != iProver_top
% 35.80/4.99      | r1_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2)))) = iProver_top ),
% 35.80/4.99      inference(instantiation,[status(thm)],[c_187514]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_7,plain,
% 35.80/4.99      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 35.80/4.99      inference(cnf_transformation,[],[f43]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_219,plain,
% 35.80/4.99      ( r2_hidden(sK0(X0_41,X1_41),X0_41) | r1_xboole_0(X0_41,X1_41) ),
% 35.80/4.99      inference(subtyping,[status(esa)],[c_7]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_844,plain,
% 35.80/4.99      ( r2_hidden(sK0(k3_xboole_0(X0_41,X1_41),X2_41),k3_xboole_0(X0_41,X1_41))
% 35.80/4.99      | r1_xboole_0(k3_xboole_0(X0_41,X1_41),X2_41) ),
% 35.80/4.99      inference(instantiation,[status(thm)],[c_219]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_2058,plain,
% 35.80/4.99      ( r2_hidden(sK0(k3_xboole_0(X0_41,X1_41),k3_xboole_0(X0_41,X1_41)),k3_xboole_0(X0_41,X1_41))
% 35.80/4.99      | r1_xboole_0(k3_xboole_0(X0_41,X1_41),k3_xboole_0(X0_41,X1_41)) ),
% 35.80/4.99      inference(instantiation,[status(thm)],[c_844]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_23333,plain,
% 35.80/4.99      ( r2_hidden(sK0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)),k3_xboole_0(sK3,sK4))
% 35.80/4.99      | r1_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) ),
% 35.80/4.99      inference(instantiation,[status(thm)],[c_2058]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_23337,plain,
% 35.80/4.99      ( r2_hidden(sK0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)),k3_xboole_0(sK3,sK4)) = iProver_top
% 35.80/4.99      | r1_xboole_0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)) = iProver_top ),
% 35.80/4.99      inference(predicate_to_equality,[status(thm)],[c_23333]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_855,plain,
% 35.80/4.99      ( ~ r2_hidden(sK0(X0_41,k3_xboole_0(X1_41,X2_41)),k3_xboole_0(X1_41,X2_41))
% 35.80/4.99      | ~ r1_xboole_0(X1_41,X2_41) ),
% 35.80/4.99      inference(instantiation,[status(thm)],[c_218]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_2057,plain,
% 35.80/4.99      ( ~ r2_hidden(sK0(k3_xboole_0(X0_41,X1_41),k3_xboole_0(X0_41,X1_41)),k3_xboole_0(X0_41,X1_41))
% 35.80/4.99      | ~ r1_xboole_0(X0_41,X1_41) ),
% 35.80/4.99      inference(instantiation,[status(thm)],[c_855]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_22222,plain,
% 35.80/4.99      ( ~ r2_hidden(sK0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)),k3_xboole_0(sK3,sK4))
% 35.80/4.99      | ~ r1_xboole_0(sK3,sK4) ),
% 35.80/4.99      inference(instantiation,[status(thm)],[c_2057]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_22223,plain,
% 35.80/4.99      ( r2_hidden(sK0(k3_xboole_0(sK3,sK4),k3_xboole_0(sK3,sK4)),k3_xboole_0(sK3,sK4)) != iProver_top
% 35.80/4.99      | r1_xboole_0(sK3,sK4) != iProver_top ),
% 35.80/4.99      inference(predicate_to_equality,[status(thm)],[c_22222]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_1101,plain,
% 35.80/4.99      ( r1_xboole_0(X0_41,sK3) | ~ r1_xboole_0(sK3,X0_41) ),
% 35.80/4.99      inference(instantiation,[status(thm)],[c_222]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_1788,plain,
% 35.80/4.99      ( r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3)
% 35.80/4.99      | ~ r1_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2)))) ),
% 35.80/4.99      inference(instantiation,[status(thm)],[c_1101]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_1789,plain,
% 35.80/4.99      ( r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) = iProver_top
% 35.80/4.99      | r1_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2)))) != iProver_top ),
% 35.80/4.99      inference(predicate_to_equality,[status(thm)],[c_1788]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_802,plain,
% 35.80/4.99      ( r1_xboole_0(sK3,sK4) | ~ r1_xboole_0(sK4,sK3) ),
% 35.80/4.99      inference(instantiation,[status(thm)],[c_222]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_803,plain,
% 35.80/4.99      ( r1_xboole_0(sK3,sK4) = iProver_top
% 35.80/4.99      | r1_xboole_0(sK4,sK3) != iProver_top ),
% 35.80/4.99      inference(predicate_to_equality,[status(thm)],[c_802]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_16,negated_conjecture,
% 35.80/4.99      ( ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) ),
% 35.80/4.99      inference(cnf_transformation,[],[f69]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_23,plain,
% 35.80/4.99      ( r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) != iProver_top ),
% 35.80/4.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(c_22,plain,
% 35.80/4.99      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 35.80/4.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 35.80/4.99  
% 35.80/4.99  cnf(contradiction,plain,
% 35.80/4.99      ( $false ),
% 35.80/4.99      inference(minisat,
% 35.80/4.99                [status(thm)],
% 35.80/4.99                [c_187575,c_23337,c_22223,c_1789,c_803,c_23,c_22]) ).
% 35.80/4.99  
% 35.80/4.99  
% 35.80/4.99  % SZS output end CNFRefutation for theBenchmark.p
% 35.80/4.99  
% 35.80/4.99  ------                               Statistics
% 35.80/4.99  
% 35.80/4.99  ------ Selected
% 35.80/4.99  
% 35.80/4.99  total_time:                             4.372
% 35.80/4.99  
%------------------------------------------------------------------------------
