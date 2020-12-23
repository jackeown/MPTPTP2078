%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:37 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 235 expanded)
%              Number of clauses        :   57 (  85 expanded)
%              Number of leaves         :   19 (  57 expanded)
%              Depth                    :   18
%              Number of atoms          :  250 ( 543 expanded)
%              Number of equality atoms :   71 ( 147 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(rectify,[],[f5])).

fof(f21,plain,(
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

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f31])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f26])).

fof(f33,plain,
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

fof(f34,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f33])).

fof(f56,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f61])).

fof(f64,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f56,f62])).

fof(f59,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f62])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_410,plain,
    ( r2_hidden(sK0(X0_41,X1_41),X0_41)
    | r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_859,plain,
    ( r2_hidden(sK0(X0_41,X1_41),X0_41) = iProver_top
    | r1_xboole_0(X0_41,X1_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_409,plain,
    ( ~ r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41))
    | ~ r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_10,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_420,plain,
    ( ~ r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41))
    | ~ r1_xboole_0(X1_41,X0_41) ),
    inference(theory_normalisation,[status(thm)],[c_409,c_10,c_1])).

cnf(c_860,plain,
    ( r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41)) != iProver_top
    | r1_xboole_0(X1_41,X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_2722,plain,
    ( r1_xboole_0(X0_41,X1_41) != iProver_top
    | r1_xboole_0(k3_xboole_0(X1_41,X0_41),X2_41) = iProver_top ),
    inference(superposition,[status(thm)],[c_859,c_860])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_245,plain,
    ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) != X0
    | k3_xboole_0(X1,X0) = X1
    | k3_xboole_0(sK2,sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_246,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_398,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_246])).

cnf(c_422,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK3,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) = k3_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_398,c_10,c_1])).

cnf(c_2730,plain,
    ( r2_hidden(X0_42,k3_xboole_0(sK2,sK3)) != iProver_top
    | r1_xboole_0(k3_xboole_0(sK3,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_422,c_860])).

cnf(c_17,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_413,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_920,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_18,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_400,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_938,plain,
    ( r1_xboole_0(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_413,c_400])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_403,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | ~ r1_xboole_0(X0_41,X2_41)
    | r1_xboole_0(X0_41,k2_xboole_0(X1_41,X2_41)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1016,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
    | ~ r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_403])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_415,plain,
    ( r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X0_41,X1_41) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_418,plain,
    ( r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X1_41,X0_41) != k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_415,c_10,c_1])).

cnf(c_1263,plain,
    ( r1_xboole_0(sK3,sK2)
    | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_418])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_414,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X0_41,X1_41) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_419,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X1_41,X0_41) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_414,c_10,c_1])).

cnf(c_426,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_424,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_1426,plain,
    ( X0_41 != X1_41
    | X1_41 = X0_41 ),
    inference(resolution,[status(thm)],[c_426,c_424])).

cnf(c_4991,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | k1_xboole_0 = k3_xboole_0(X1_41,X0_41) ),
    inference(resolution,[status(thm)],[c_419,c_1426])).

cnf(c_3012,plain,
    ( k3_xboole_0(sK2,sK3) = k3_xboole_0(sK2,k3_xboole_0(sK3,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) ),
    inference(resolution,[status(thm)],[c_1426,c_422])).

cnf(c_3364,plain,
    ( X0_41 != k3_xboole_0(sK2,k3_xboole_0(sK3,k3_enumset1(sK5,sK5,sK5,sK5,sK5)))
    | k3_xboole_0(sK2,sK3) = X0_41 ),
    inference(resolution,[status(thm)],[c_3012,c_426])).

cnf(c_18484,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK3,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),sK2)
    | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4991,c_3364])).

cnf(c_18497,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0
    | r1_xboole_0(k3_xboole_0(sK3,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18484])).

cnf(c_33920,plain,
    ( r1_xboole_0(k3_xboole_0(sK3,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2730,c_17,c_920,c_938,c_1016,c_1263,c_18497])).

cnf(c_33924,plain,
    ( r1_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2722,c_33920])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_402,plain,
    ( r2_hidden(X0_42,X0_41)
    | r1_xboole_0(k3_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42),X0_41) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_28342,plain,
    ( r2_hidden(X0_42,sK3)
    | r1_xboole_0(k3_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42),sK3) ),
    inference(instantiation,[status(thm)],[c_402])).

cnf(c_28347,plain,
    ( r2_hidden(X0_42,sK3) = iProver_top
    | r1_xboole_0(k3_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28342])).

cnf(c_28349,plain,
    ( r2_hidden(sK5,sK3) = iProver_top
    | r1_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_28347])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_412,plain,
    ( ~ r2_hidden(X0_42,X0_41)
    | ~ r2_hidden(X0_42,X1_41)
    | ~ r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_7736,plain,
    ( ~ r2_hidden(X0_42,sK3)
    | ~ r2_hidden(X0_42,sK4) ),
    inference(resolution,[status(thm)],[c_412,c_400])).

cnf(c_7737,plain,
    ( r2_hidden(X0_42,sK3) != iProver_top
    | r2_hidden(X0_42,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7736])).

cnf(c_7739,plain,
    ( r2_hidden(sK5,sK3) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7737])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33924,c_28349,c_7739,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:09:22 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  % Running in FOF mode
% 7.65/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/1.49  
% 7.65/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.65/1.49  
% 7.65/1.49  ------  iProver source info
% 7.65/1.49  
% 7.65/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.65/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.65/1.49  git: non_committed_changes: false
% 7.65/1.49  git: last_make_outside_of_git: false
% 7.65/1.49  
% 7.65/1.49  ------ 
% 7.65/1.49  ------ Parsing...
% 7.65/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  ------ Proving...
% 7.65/1.49  ------ Problem Properties 
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  clauses                                 20
% 7.65/1.49  conjectures                             3
% 7.65/1.49  EPR                                     5
% 7.65/1.49  Horn                                    16
% 7.65/1.49  unary                                   8
% 7.65/1.49  binary                                  10
% 7.65/1.49  lits                                    34
% 7.65/1.49  lits eq                                 6
% 7.65/1.49  fd_pure                                 0
% 7.65/1.49  fd_pseudo                               0
% 7.65/1.49  fd_cond                                 0
% 7.65/1.49  fd_pseudo_cond                          0
% 7.65/1.49  AC symbols                              1
% 7.65/1.49  
% 7.65/1.49  ------ Input Options Time Limit: Unbounded
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ 
% 7.65/1.49  Current options:
% 7.65/1.49  ------ 
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  % SZS status Theorem for theBenchmark.p
% 7.65/1.49  
% 7.65/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.65/1.49  
% 7.65/1.49  fof(f5,axiom,(
% 7.65/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f18,plain,(
% 7.65/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.65/1.49    inference(rectify,[],[f5])).
% 7.65/1.49  
% 7.65/1.49  fof(f21,plain,(
% 7.65/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.65/1.49    inference(ennf_transformation,[],[f18])).
% 7.65/1.49  
% 7.65/1.49  fof(f29,plain,(
% 7.65/1.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.65/1.49    introduced(choice_axiom,[])).
% 7.65/1.49  
% 7.65/1.49  fof(f30,plain,(
% 7.65/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.65/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f29])).
% 7.65/1.49  
% 7.65/1.49  fof(f40,plain,(
% 7.65/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f30])).
% 7.65/1.49  
% 7.65/1.49  fof(f6,axiom,(
% 7.65/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f19,plain,(
% 7.65/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.65/1.49    inference(rectify,[],[f6])).
% 7.65/1.49  
% 7.65/1.49  fof(f22,plain,(
% 7.65/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.65/1.49    inference(ennf_transformation,[],[f19])).
% 7.65/1.49  
% 7.65/1.49  fof(f31,plain,(
% 7.65/1.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 7.65/1.49    introduced(choice_axiom,[])).
% 7.65/1.49  
% 7.65/1.49  fof(f32,plain,(
% 7.65/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.65/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f31])).
% 7.65/1.49  
% 7.65/1.49  fof(f44,plain,(
% 7.65/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.65/1.49    inference(cnf_transformation,[],[f32])).
% 7.65/1.49  
% 7.65/1.49  fof(f7,axiom,(
% 7.65/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f45,plain,(
% 7.65/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f7])).
% 7.65/1.49  
% 7.65/1.49  fof(f2,axiom,(
% 7.65/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f36,plain,(
% 7.65/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f2])).
% 7.65/1.49  
% 7.65/1.49  fof(f8,axiom,(
% 7.65/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f23,plain,(
% 7.65/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.65/1.49    inference(ennf_transformation,[],[f8])).
% 7.65/1.49  
% 7.65/1.49  fof(f46,plain,(
% 7.65/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f23])).
% 7.65/1.49  
% 7.65/1.49  fof(f16,conjecture,(
% 7.65/1.49    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f17,negated_conjecture,(
% 7.65/1.49    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.65/1.49    inference(negated_conjecture,[],[f16])).
% 7.65/1.49  
% 7.65/1.49  fof(f26,plain,(
% 7.65/1.49    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 7.65/1.49    inference(ennf_transformation,[],[f17])).
% 7.65/1.49  
% 7.65/1.49  fof(f27,plain,(
% 7.65/1.49    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 7.65/1.49    inference(flattening,[],[f26])).
% 7.65/1.49  
% 7.65/1.49  fof(f33,plain,(
% 7.65/1.49    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 7.65/1.49    introduced(choice_axiom,[])).
% 7.65/1.49  
% 7.65/1.49  fof(f34,plain,(
% 7.65/1.49    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 7.65/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f33])).
% 7.65/1.49  
% 7.65/1.49  fof(f56,plain,(
% 7.65/1.49    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 7.65/1.49    inference(cnf_transformation,[],[f34])).
% 7.65/1.49  
% 7.65/1.49  fof(f11,axiom,(
% 7.65/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f51,plain,(
% 7.65/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f11])).
% 7.65/1.49  
% 7.65/1.49  fof(f12,axiom,(
% 7.65/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f52,plain,(
% 7.65/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f12])).
% 7.65/1.49  
% 7.65/1.49  fof(f13,axiom,(
% 7.65/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f53,plain,(
% 7.65/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f13])).
% 7.65/1.49  
% 7.65/1.49  fof(f14,axiom,(
% 7.65/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f54,plain,(
% 7.65/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f14])).
% 7.65/1.49  
% 7.65/1.49  fof(f60,plain,(
% 7.65/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.65/1.49    inference(definition_unfolding,[],[f53,f54])).
% 7.65/1.49  
% 7.65/1.49  fof(f61,plain,(
% 7.65/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.65/1.49    inference(definition_unfolding,[],[f52,f60])).
% 7.65/1.49  
% 7.65/1.49  fof(f62,plain,(
% 7.65/1.49    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 7.65/1.49    inference(definition_unfolding,[],[f51,f61])).
% 7.65/1.49  
% 7.65/1.49  fof(f64,plain,(
% 7.65/1.49    r1_tarski(k3_xboole_0(sK2,sK3),k3_enumset1(sK5,sK5,sK5,sK5,sK5))),
% 7.65/1.49    inference(definition_unfolding,[],[f56,f62])).
% 7.65/1.49  
% 7.65/1.49  fof(f59,plain,(
% 7.65/1.49    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 7.65/1.49    inference(cnf_transformation,[],[f34])).
% 7.65/1.49  
% 7.65/1.49  fof(f4,axiom,(
% 7.65/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f20,plain,(
% 7.65/1.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.65/1.49    inference(ennf_transformation,[],[f4])).
% 7.65/1.49  
% 7.65/1.49  fof(f39,plain,(
% 7.65/1.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f20])).
% 7.65/1.49  
% 7.65/1.49  fof(f58,plain,(
% 7.65/1.49    r1_xboole_0(sK4,sK3)),
% 7.65/1.49    inference(cnf_transformation,[],[f34])).
% 7.65/1.49  
% 7.65/1.49  fof(f10,axiom,(
% 7.65/1.49    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f24,plain,(
% 7.65/1.49    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.65/1.49    inference(ennf_transformation,[],[f10])).
% 7.65/1.49  
% 7.65/1.49  fof(f48,plain,(
% 7.65/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.65/1.49    inference(cnf_transformation,[],[f24])).
% 7.65/1.49  
% 7.65/1.49  fof(f3,axiom,(
% 7.65/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f28,plain,(
% 7.65/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.65/1.49    inference(nnf_transformation,[],[f3])).
% 7.65/1.49  
% 7.65/1.49  fof(f38,plain,(
% 7.65/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.65/1.49    inference(cnf_transformation,[],[f28])).
% 7.65/1.49  
% 7.65/1.49  fof(f37,plain,(
% 7.65/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f28])).
% 7.65/1.49  
% 7.65/1.49  fof(f15,axiom,(
% 7.65/1.49    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f25,plain,(
% 7.65/1.49    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 7.65/1.49    inference(ennf_transformation,[],[f15])).
% 7.65/1.49  
% 7.65/1.49  fof(f55,plain,(
% 7.65/1.49    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f25])).
% 7.65/1.49  
% 7.65/1.49  fof(f63,plain,(
% 7.65/1.49    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 7.65/1.49    inference(definition_unfolding,[],[f55,f62])).
% 7.65/1.49  
% 7.65/1.49  fof(f42,plain,(
% 7.65/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f30])).
% 7.65/1.49  
% 7.65/1.49  fof(f57,plain,(
% 7.65/1.49    r2_hidden(sK5,sK4)),
% 7.65/1.49    inference(cnf_transformation,[],[f34])).
% 7.65/1.49  
% 7.65/1.49  cnf(c_7,plain,
% 7.65/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 7.65/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_410,plain,
% 7.65/1.49      ( r2_hidden(sK0(X0_41,X1_41),X0_41) | r1_xboole_0(X0_41,X1_41) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_859,plain,
% 7.65/1.49      ( r2_hidden(sK0(X0_41,X1_41),X0_41) = iProver_top
% 7.65/1.49      | r1_xboole_0(X0_41,X1_41) = iProver_top ),
% 7.65/1.49      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_8,plain,
% 7.65/1.49      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 7.65/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_409,plain,
% 7.65/1.49      ( ~ r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41))
% 7.65/1.49      | ~ r1_xboole_0(X0_41,X1_41) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_10,plain,
% 7.65/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 7.65/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_1,plain,
% 7.65/1.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.65/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_420,plain,
% 7.65/1.49      ( ~ r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41))
% 7.65/1.49      | ~ r1_xboole_0(X1_41,X0_41) ),
% 7.65/1.49      inference(theory_normalisation,[status(thm)],[c_409,c_10,c_1]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_860,plain,
% 7.65/1.49      ( r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41)) != iProver_top
% 7.65/1.49      | r1_xboole_0(X1_41,X0_41) != iProver_top ),
% 7.65/1.49      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_2722,plain,
% 7.65/1.49      ( r1_xboole_0(X0_41,X1_41) != iProver_top
% 7.65/1.49      | r1_xboole_0(k3_xboole_0(X1_41,X0_41),X2_41) = iProver_top ),
% 7.65/1.49      inference(superposition,[status(thm)],[c_859,c_860]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_11,plain,
% 7.65/1.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.65/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_20,negated_conjecture,
% 7.65/1.49      ( r1_tarski(k3_xboole_0(sK2,sK3),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) ),
% 7.65/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_245,plain,
% 7.65/1.49      ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) != X0
% 7.65/1.49      | k3_xboole_0(X1,X0) = X1
% 7.65/1.49      | k3_xboole_0(sK2,sK3) != X1 ),
% 7.65/1.49      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_246,plain,
% 7.65/1.49      ( k3_xboole_0(k3_xboole_0(sK2,sK3),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
% 7.65/1.49      inference(unflattening,[status(thm)],[c_245]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_398,plain,
% 7.65/1.49      ( k3_xboole_0(k3_xboole_0(sK2,sK3),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_246]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_422,plain,
% 7.65/1.49      ( k3_xboole_0(sK2,k3_xboole_0(sK3,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) = k3_xboole_0(sK2,sK3) ),
% 7.65/1.49      inference(theory_normalisation,[status(thm)],[c_398,c_10,c_1]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_2730,plain,
% 7.65/1.49      ( r2_hidden(X0_42,k3_xboole_0(sK2,sK3)) != iProver_top
% 7.65/1.49      | r1_xboole_0(k3_xboole_0(sK3,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),sK2) != iProver_top ),
% 7.65/1.49      inference(superposition,[status(thm)],[c_422,c_860]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_17,negated_conjecture,
% 7.65/1.49      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 7.65/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_4,plain,
% 7.65/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.65/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_413,plain,
% 7.65/1.49      ( ~ r1_xboole_0(X0_41,X1_41) | r1_xboole_0(X1_41,X0_41) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_920,plain,
% 7.65/1.49      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
% 7.65/1.49      | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_413]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_18,negated_conjecture,
% 7.65/1.49      ( r1_xboole_0(sK4,sK3) ),
% 7.65/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_400,negated_conjecture,
% 7.65/1.49      ( r1_xboole_0(sK4,sK3) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_938,plain,
% 7.65/1.49      ( r1_xboole_0(sK3,sK4) ),
% 7.65/1.49      inference(resolution,[status(thm)],[c_413,c_400]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_15,plain,
% 7.65/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.65/1.49      | ~ r1_xboole_0(X0,X2)
% 7.65/1.49      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.65/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_403,plain,
% 7.65/1.49      ( ~ r1_xboole_0(X0_41,X1_41)
% 7.65/1.49      | ~ r1_xboole_0(X0_41,X2_41)
% 7.65/1.49      | r1_xboole_0(X0_41,k2_xboole_0(X1_41,X2_41)) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_15]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_1016,plain,
% 7.65/1.49      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
% 7.65/1.49      | ~ r1_xboole_0(sK3,sK4)
% 7.65/1.49      | ~ r1_xboole_0(sK3,sK2) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_403]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_2,plain,
% 7.65/1.49      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.65/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_415,plain,
% 7.65/1.49      ( r1_xboole_0(X0_41,X1_41)
% 7.65/1.49      | k3_xboole_0(X0_41,X1_41) != k1_xboole_0 ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_418,plain,
% 7.65/1.49      ( r1_xboole_0(X0_41,X1_41)
% 7.65/1.49      | k3_xboole_0(X1_41,X0_41) != k1_xboole_0 ),
% 7.65/1.49      inference(theory_normalisation,[status(thm)],[c_415,c_10,c_1]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_1263,plain,
% 7.65/1.49      ( r1_xboole_0(sK3,sK2) | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_418]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_3,plain,
% 7.65/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.65/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_414,plain,
% 7.65/1.49      ( ~ r1_xboole_0(X0_41,X1_41)
% 7.65/1.49      | k3_xboole_0(X0_41,X1_41) = k1_xboole_0 ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_419,plain,
% 7.65/1.49      ( ~ r1_xboole_0(X0_41,X1_41)
% 7.65/1.49      | k3_xboole_0(X1_41,X0_41) = k1_xboole_0 ),
% 7.65/1.49      inference(theory_normalisation,[status(thm)],[c_414,c_10,c_1]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_426,plain,
% 7.65/1.49      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 7.65/1.49      theory(equality) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_424,plain,( X0_41 = X0_41 ),theory(equality) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_1426,plain,
% 7.65/1.49      ( X0_41 != X1_41 | X1_41 = X0_41 ),
% 7.65/1.49      inference(resolution,[status(thm)],[c_426,c_424]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_4991,plain,
% 7.65/1.49      ( ~ r1_xboole_0(X0_41,X1_41)
% 7.65/1.49      | k1_xboole_0 = k3_xboole_0(X1_41,X0_41) ),
% 7.65/1.49      inference(resolution,[status(thm)],[c_419,c_1426]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_3012,plain,
% 7.65/1.49      ( k3_xboole_0(sK2,sK3) = k3_xboole_0(sK2,k3_xboole_0(sK3,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) ),
% 7.65/1.49      inference(resolution,[status(thm)],[c_1426,c_422]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_3364,plain,
% 7.65/1.49      ( X0_41 != k3_xboole_0(sK2,k3_xboole_0(sK3,k3_enumset1(sK5,sK5,sK5,sK5,sK5)))
% 7.65/1.49      | k3_xboole_0(sK2,sK3) = X0_41 ),
% 7.65/1.49      inference(resolution,[status(thm)],[c_3012,c_426]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_18484,plain,
% 7.65/1.49      ( ~ r1_xboole_0(k3_xboole_0(sK3,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),sK2)
% 7.65/1.49      | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.65/1.49      inference(resolution,[status(thm)],[c_4991,c_3364]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_18497,plain,
% 7.65/1.49      ( k3_xboole_0(sK2,sK3) = k1_xboole_0
% 7.65/1.49      | r1_xboole_0(k3_xboole_0(sK3,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),sK2) != iProver_top ),
% 7.65/1.49      inference(predicate_to_equality,[status(thm)],[c_18484]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_33920,plain,
% 7.65/1.49      ( r1_xboole_0(k3_xboole_0(sK3,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),sK2) != iProver_top ),
% 7.65/1.49      inference(global_propositional_subsumption,
% 7.65/1.49                [status(thm)],
% 7.65/1.49                [c_2730,c_17,c_920,c_938,c_1016,c_1263,c_18497]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_33924,plain,
% 7.65/1.49      ( r1_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK3) != iProver_top ),
% 7.65/1.49      inference(superposition,[status(thm)],[c_2722,c_33920]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_16,plain,
% 7.65/1.49      ( r2_hidden(X0,X1) | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 7.65/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_402,plain,
% 7.65/1.49      ( r2_hidden(X0_42,X0_41)
% 7.65/1.49      | r1_xboole_0(k3_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42),X0_41) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_28342,plain,
% 7.65/1.49      ( r2_hidden(X0_42,sK3)
% 7.65/1.49      | r1_xboole_0(k3_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42),sK3) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_402]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_28347,plain,
% 7.65/1.49      ( r2_hidden(X0_42,sK3) = iProver_top
% 7.65/1.49      | r1_xboole_0(k3_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42),sK3) = iProver_top ),
% 7.65/1.49      inference(predicate_to_equality,[status(thm)],[c_28342]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_28349,plain,
% 7.65/1.49      ( r2_hidden(sK5,sK3) = iProver_top
% 7.65/1.49      | r1_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK3) = iProver_top ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_28347]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_5,plain,
% 7.65/1.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 7.65/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_412,plain,
% 7.65/1.49      ( ~ r2_hidden(X0_42,X0_41)
% 7.65/1.49      | ~ r2_hidden(X0_42,X1_41)
% 7.65/1.49      | ~ r1_xboole_0(X0_41,X1_41) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_7736,plain,
% 7.65/1.49      ( ~ r2_hidden(X0_42,sK3) | ~ r2_hidden(X0_42,sK4) ),
% 7.65/1.49      inference(resolution,[status(thm)],[c_412,c_400]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_7737,plain,
% 7.65/1.49      ( r2_hidden(X0_42,sK3) != iProver_top
% 7.65/1.49      | r2_hidden(X0_42,sK4) != iProver_top ),
% 7.65/1.49      inference(predicate_to_equality,[status(thm)],[c_7736]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_7739,plain,
% 7.65/1.49      ( r2_hidden(sK5,sK3) != iProver_top
% 7.65/1.49      | r2_hidden(sK5,sK4) != iProver_top ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_7737]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_19,negated_conjecture,
% 7.65/1.49      ( r2_hidden(sK5,sK4) ),
% 7.65/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_22,plain,
% 7.65/1.49      ( r2_hidden(sK5,sK4) = iProver_top ),
% 7.65/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(contradiction,plain,
% 7.65/1.49      ( $false ),
% 7.65/1.49      inference(minisat,[status(thm)],[c_33924,c_28349,c_7739,c_22]) ).
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.65/1.49  
% 7.65/1.49  ------                               Statistics
% 7.65/1.49  
% 7.65/1.49  ------ Selected
% 7.65/1.49  
% 7.65/1.49  total_time:                             0.741
% 7.65/1.49  
%------------------------------------------------------------------------------
