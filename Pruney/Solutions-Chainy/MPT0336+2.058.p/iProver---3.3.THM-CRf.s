%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:43 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 180 expanded)
%              Number of clauses        :   59 (  66 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   17
%              Number of atoms          :  251 ( 418 expanded)
%              Number of equality atoms :   82 ( 112 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f54])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f24])).

fof(f29,plain,
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

fof(f30,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    & r1_xboole_0(sK3,sK2)
    & r2_hidden(sK4,sK3)
    & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f29])).

fof(f49,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f60,plain,(
    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f49,f40,f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f40])).

fof(f51,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f27])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f31,f40,f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_273,plain,
    ( r2_hidden(X0_41,X0_40)
    | r1_xboole_0(k2_enumset1(X0_41,X0_41,X0_41,X0_41),X0_40) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_702,plain,
    ( r2_hidden(X0_41,X0_40) = iProver_top
    | r1_xboole_0(k2_enumset1(X0_41,X0_41,X0_41,X0_41),X0_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_241,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | k2_enumset1(sK4,sK4,sK4,sK4) != X0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_242,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)
    | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0) ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_267,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0_40)
    | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_40) ),
    inference(subtyping,[status(esa)],[c_242])).

cnf(c_707,plain,
    ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0_40) != iProver_top
    | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_267])).

cnf(c_3357,plain,
    ( r2_hidden(sK4,X0_40) = iProver_top
    | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_40) = iProver_top ),
    inference(superposition,[status(thm)],[c_702,c_707])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_281,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_694,plain,
    ( k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)) = k1_xboole_0
    | r1_xboole_0(X0_40,X1_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_4093,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_40)) = k1_xboole_0
    | r2_hidden(sK4,X0_40) = iProver_top ),
    inference(superposition,[status(thm)],[c_3357,c_694])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_271,negated_conjecture,
    ( r1_xboole_0(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_704,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_271])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_270,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_705,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_279,plain,
    ( ~ r2_hidden(X0_41,X0_40)
    | ~ r2_hidden(X0_41,X1_40)
    | ~ r1_xboole_0(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_696,plain,
    ( r2_hidden(X0_41,X0_40) != iProver_top
    | r2_hidden(X0_41,X1_40) != iProver_top
    | r1_xboole_0(X1_40,X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_4890,plain,
    ( r2_hidden(sK4,X0_40) != iProver_top
    | r1_xboole_0(sK3,X0_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_705,c_696])).

cnf(c_6582,plain,
    ( r2_hidden(sK4,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_704,c_4890])).

cnf(c_13041,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4093,c_6582])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_283,plain,
    ( k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)) = k4_xboole_0(X1_40,k4_xboole_0(X1_40,X0_40)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_8,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_235,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k4_xboole_0(X3,k4_xboole_0(X3,X1)) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_8])).

cnf(c_236,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_268,plain,
    ( k4_xboole_0(k4_xboole_0(X0_40,X1_40),k4_xboole_0(k4_xboole_0(X0_40,X1_40),X0_40)) = k4_xboole_0(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_236])).

cnf(c_1423,plain,
    ( k4_xboole_0(k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)),k4_xboole_0(k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)),X1_40)) = k4_xboole_0(X1_40,k4_xboole_0(X1_40,X0_40)) ),
    inference(superposition,[status(thm)],[c_283,c_268])).

cnf(c_13106,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13041,c_1423])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_282,plain,
    ( r1_xboole_0(X0_40,X1_40)
    | k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_693,plain,
    ( k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)) != k1_xboole_0
    | r1_xboole_0(X0_40,X1_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_2211,plain,
    ( k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)) != k1_xboole_0
    | r1_xboole_0(X1_40,X0_40) = iProver_top ),
    inference(superposition,[status(thm)],[c_283,c_693])).

cnf(c_13876,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_13106,c_2211])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_280,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X1_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1968,plain,
    ( ~ r1_xboole_0(X0_40,sK2)
    | r1_xboole_0(sK2,X0_40) ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_1969,plain,
    ( r1_xboole_0(X0_40,sK2) != iProver_top
    | r1_xboole_0(sK2,X0_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1968])).

cnf(c_1971,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top
    | r1_xboole_0(sK1,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1969])).

cnf(c_1106,plain,
    ( r1_xboole_0(k2_xboole_0(X0_40,sK3),sK2)
    | ~ r1_xboole_0(sK2,k2_xboole_0(X0_40,sK3)) ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_1107,plain,
    ( r1_xboole_0(k2_xboole_0(X0_40,sK3),sK2) = iProver_top
    | r1_xboole_0(sK2,k2_xboole_0(X0_40,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1106])).

cnf(c_1109,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) = iProver_top
    | r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1107])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_274,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | ~ r1_xboole_0(X0_40,X2_40)
    | r1_xboole_0(X0_40,k2_xboole_0(X1_40,X2_40)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_903,plain,
    ( ~ r1_xboole_0(sK2,X0_40)
    | r1_xboole_0(sK2,k2_xboole_0(X0_40,sK3))
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_904,plain,
    ( r1_xboole_0(sK2,X0_40) != iProver_top
    | r1_xboole_0(sK2,k2_xboole_0(X0_40,sK3)) = iProver_top
    | r1_xboole_0(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_903])).

cnf(c_906,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) = iProver_top
    | r1_xboole_0(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_904])).

cnf(c_816,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_817,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | r1_xboole_0(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_14,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_20,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13876,c_1971,c_1109,c_906,c_817,c_21,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:44:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.10/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/0.98  
% 4.10/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.10/0.98  
% 4.10/0.98  ------  iProver source info
% 4.10/0.98  
% 4.10/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.10/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.10/0.98  git: non_committed_changes: false
% 4.10/0.98  git: last_make_outside_of_git: false
% 4.10/0.98  
% 4.10/0.98  ------ 
% 4.10/0.98  ------ Parsing...
% 4.10/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.10/0.98  
% 4.10/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 4.10/0.98  
% 4.10/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.10/0.98  
% 4.10/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.10/0.98  ------ Proving...
% 4.10/0.98  ------ Problem Properties 
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  clauses                                 18
% 4.10/0.98  conjectures                             3
% 4.10/0.98  EPR                                     4
% 4.10/0.98  Horn                                    15
% 4.10/0.98  unary                                   6
% 4.10/0.98  binary                                  10
% 4.10/0.98  lits                                    32
% 4.10/0.98  lits eq                                 5
% 4.10/0.98  fd_pure                                 0
% 4.10/0.98  fd_pseudo                               0
% 4.10/0.98  fd_cond                                 0
% 4.10/0.98  fd_pseudo_cond                          0
% 4.10/0.98  AC symbols                              0
% 4.10/0.98  
% 4.10/0.98  ------ Input Options Time Limit: Unbounded
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  ------ 
% 4.10/0.98  Current options:
% 4.10/0.98  ------ 
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  ------ Proving...
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  % SZS status Theorem for theBenchmark.p
% 4.10/0.98  
% 4.10/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.10/0.98  
% 4.10/0.98  fof(f13,axiom,(
% 4.10/0.98    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 4.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f23,plain,(
% 4.10/0.98    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 4.10/0.98    inference(ennf_transformation,[],[f13])).
% 4.10/0.98  
% 4.10/0.98  fof(f48,plain,(
% 4.10/0.98    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f23])).
% 4.10/0.98  
% 4.10/0.98  fof(f10,axiom,(
% 4.10/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f45,plain,(
% 4.10/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f10])).
% 4.10/0.98  
% 4.10/0.98  fof(f11,axiom,(
% 4.10/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f46,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f11])).
% 4.10/0.98  
% 4.10/0.98  fof(f12,axiom,(
% 4.10/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f47,plain,(
% 4.10/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f12])).
% 4.10/0.98  
% 4.10/0.98  fof(f53,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 4.10/0.98    inference(definition_unfolding,[],[f46,f47])).
% 4.10/0.98  
% 4.10/0.98  fof(f54,plain,(
% 4.10/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 4.10/0.98    inference(definition_unfolding,[],[f45,f53])).
% 4.10/0.98  
% 4.10/0.98  fof(f59,plain,(
% 4.10/0.98    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 4.10/0.98    inference(definition_unfolding,[],[f48,f54])).
% 4.10/0.98  
% 4.10/0.98  fof(f8,axiom,(
% 4.10/0.98    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 4.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f20,plain,(
% 4.10/0.98    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 4.10/0.98    inference(ennf_transformation,[],[f8])).
% 4.10/0.98  
% 4.10/0.98  fof(f21,plain,(
% 4.10/0.98    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 4.10/0.98    inference(flattening,[],[f20])).
% 4.10/0.98  
% 4.10/0.98  fof(f41,plain,(
% 4.10/0.98    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f21])).
% 4.10/0.98  
% 4.10/0.98  fof(f14,conjecture,(
% 4.10/0.98    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 4.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f15,negated_conjecture,(
% 4.10/0.98    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 4.10/0.98    inference(negated_conjecture,[],[f14])).
% 4.10/0.98  
% 4.10/0.98  fof(f24,plain,(
% 4.10/0.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 4.10/0.98    inference(ennf_transformation,[],[f15])).
% 4.10/0.98  
% 4.10/0.98  fof(f25,plain,(
% 4.10/0.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 4.10/0.98    inference(flattening,[],[f24])).
% 4.10/0.98  
% 4.10/0.98  fof(f29,plain,(
% 4.10/0.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)))),
% 4.10/0.98    introduced(choice_axiom,[])).
% 4.10/0.98  
% 4.10/0.98  fof(f30,plain,(
% 4.10/0.98    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 4.10/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f29])).
% 4.10/0.98  
% 4.10/0.98  fof(f49,plain,(
% 4.10/0.98    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 4.10/0.98    inference(cnf_transformation,[],[f30])).
% 4.10/0.98  
% 4.10/0.98  fof(f7,axiom,(
% 4.10/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f40,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.10/0.98    inference(cnf_transformation,[],[f7])).
% 4.10/0.98  
% 4.10/0.98  fof(f60,plain,(
% 4.10/0.98    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))),
% 4.10/0.98    inference(definition_unfolding,[],[f49,f40,f54])).
% 4.10/0.98  
% 4.10/0.98  fof(f2,axiom,(
% 4.10/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 4.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f26,plain,(
% 4.10/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 4.10/0.98    inference(nnf_transformation,[],[f2])).
% 4.10/0.98  
% 4.10/0.98  fof(f32,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f26])).
% 4.10/0.98  
% 4.10/0.98  fof(f57,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 4.10/0.98    inference(definition_unfolding,[],[f32,f40])).
% 4.10/0.98  
% 4.10/0.98  fof(f51,plain,(
% 4.10/0.98    r1_xboole_0(sK3,sK2)),
% 4.10/0.98    inference(cnf_transformation,[],[f30])).
% 4.10/0.98  
% 4.10/0.98  fof(f50,plain,(
% 4.10/0.98    r2_hidden(sK4,sK3)),
% 4.10/0.98    inference(cnf_transformation,[],[f30])).
% 4.10/0.98  
% 4.10/0.98  fof(f4,axiom,(
% 4.10/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f16,plain,(
% 4.10/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.10/0.98    inference(rectify,[],[f4])).
% 4.10/0.98  
% 4.10/0.98  fof(f18,plain,(
% 4.10/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.10/0.98    inference(ennf_transformation,[],[f16])).
% 4.10/0.98  
% 4.10/0.98  fof(f27,plain,(
% 4.10/0.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 4.10/0.98    introduced(choice_axiom,[])).
% 4.10/0.98  
% 4.10/0.98  fof(f28,plain,(
% 4.10/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 4.10/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f27])).
% 4.10/0.98  
% 4.10/0.98  fof(f37,plain,(
% 4.10/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f28])).
% 4.10/0.98  
% 4.10/0.98  fof(f1,axiom,(
% 4.10/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f31,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f1])).
% 4.10/0.98  
% 4.10/0.98  fof(f55,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 4.10/0.98    inference(definition_unfolding,[],[f31,f40,f40])).
% 4.10/0.98  
% 4.10/0.98  fof(f5,axiom,(
% 4.10/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f19,plain,(
% 4.10/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.10/0.98    inference(ennf_transformation,[],[f5])).
% 4.10/0.98  
% 4.10/0.98  fof(f38,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f19])).
% 4.10/0.98  
% 4.10/0.98  fof(f58,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 4.10/0.98    inference(definition_unfolding,[],[f38,f40])).
% 4.10/0.98  
% 4.10/0.98  fof(f6,axiom,(
% 4.10/0.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f39,plain,(
% 4.10/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f6])).
% 4.10/0.98  
% 4.10/0.98  fof(f33,plain,(
% 4.10/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 4.10/0.98    inference(cnf_transformation,[],[f26])).
% 4.10/0.98  
% 4.10/0.98  fof(f56,plain,(
% 4.10/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.10/0.98    inference(definition_unfolding,[],[f33,f40])).
% 4.10/0.98  
% 4.10/0.98  fof(f3,axiom,(
% 4.10/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 4.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f17,plain,(
% 4.10/0.98    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 4.10/0.98    inference(ennf_transformation,[],[f3])).
% 4.10/0.98  
% 4.10/0.98  fof(f34,plain,(
% 4.10/0.98    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f17])).
% 4.10/0.98  
% 4.10/0.98  fof(f9,axiom,(
% 4.10/0.98    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 4.10/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f22,plain,(
% 4.10/0.98    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 4.10/0.98    inference(ennf_transformation,[],[f9])).
% 4.10/0.98  
% 4.10/0.98  fof(f42,plain,(
% 4.10/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.10/0.98    inference(cnf_transformation,[],[f22])).
% 4.10/0.98  
% 4.10/0.98  fof(f52,plain,(
% 4.10/0.98    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 4.10/0.98    inference(cnf_transformation,[],[f30])).
% 4.10/0.98  
% 4.10/0.98  cnf(c_13,plain,
% 4.10/0.98      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 4.10/0.98      inference(cnf_transformation,[],[f59]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_273,plain,
% 4.10/0.98      ( r2_hidden(X0_41,X0_40)
% 4.10/0.98      | r1_xboole_0(k2_enumset1(X0_41,X0_41,X0_41,X0_41),X0_40) ),
% 4.10/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_702,plain,
% 4.10/0.98      ( r2_hidden(X0_41,X0_40) = iProver_top
% 4.10/0.98      | r1_xboole_0(k2_enumset1(X0_41,X0_41,X0_41,X0_41),X0_40) = iProver_top ),
% 4.10/0.98      inference(predicate_to_equality,[status(thm)],[c_273]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_9,plain,
% 4.10/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 4.10/0.98      inference(cnf_transformation,[],[f41]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_17,negated_conjecture,
% 4.10/0.98      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 4.10/0.98      inference(cnf_transformation,[],[f60]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_241,plain,
% 4.10/0.98      ( ~ r1_xboole_0(X0,X1)
% 4.10/0.98      | r1_xboole_0(X2,X1)
% 4.10/0.98      | k2_enumset1(sK4,sK4,sK4,sK4) != X0
% 4.10/0.98      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X2 ),
% 4.10/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_242,plain,
% 4.10/0.98      ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)
% 4.10/0.98      | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0) ),
% 4.10/0.98      inference(unflattening,[status(thm)],[c_241]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_267,plain,
% 4.10/0.98      ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0_40)
% 4.10/0.98      | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_40) ),
% 4.10/0.98      inference(subtyping,[status(esa)],[c_242]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_707,plain,
% 4.10/0.98      ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0_40) != iProver_top
% 4.10/0.98      | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_40) = iProver_top ),
% 4.10/0.98      inference(predicate_to_equality,[status(thm)],[c_267]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_3357,plain,
% 4.10/0.98      ( r2_hidden(sK4,X0_40) = iProver_top
% 4.10/0.98      | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_40) = iProver_top ),
% 4.10/0.98      inference(superposition,[status(thm)],[c_702,c_707]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_2,plain,
% 4.10/0.98      ( ~ r1_xboole_0(X0,X1)
% 4.10/0.98      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 4.10/0.98      inference(cnf_transformation,[],[f57]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_281,plain,
% 4.10/0.98      ( ~ r1_xboole_0(X0_40,X1_40)
% 4.10/0.98      | k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)) = k1_xboole_0 ),
% 4.10/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_694,plain,
% 4.10/0.98      ( k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)) = k1_xboole_0
% 4.10/0.98      | r1_xboole_0(X0_40,X1_40) != iProver_top ),
% 4.10/0.98      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_4093,plain,
% 4.10/0.98      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_40)) = k1_xboole_0
% 4.10/0.98      | r2_hidden(sK4,X0_40) = iProver_top ),
% 4.10/0.98      inference(superposition,[status(thm)],[c_3357,c_694]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_15,negated_conjecture,
% 4.10/0.98      ( r1_xboole_0(sK3,sK2) ),
% 4.10/0.98      inference(cnf_transformation,[],[f51]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_271,negated_conjecture,
% 4.10/0.98      ( r1_xboole_0(sK3,sK2) ),
% 4.10/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_704,plain,
% 4.10/0.98      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 4.10/0.98      inference(predicate_to_equality,[status(thm)],[c_271]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_16,negated_conjecture,
% 4.10/0.98      ( r2_hidden(sK4,sK3) ),
% 4.10/0.98      inference(cnf_transformation,[],[f50]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_270,negated_conjecture,
% 4.10/0.98      ( r2_hidden(sK4,sK3) ),
% 4.10/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_705,plain,
% 4.10/0.98      ( r2_hidden(sK4,sK3) = iProver_top ),
% 4.10/0.98      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_4,plain,
% 4.10/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 4.10/0.98      inference(cnf_transformation,[],[f37]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_279,plain,
% 4.10/0.98      ( ~ r2_hidden(X0_41,X0_40)
% 4.10/0.98      | ~ r2_hidden(X0_41,X1_40)
% 4.10/0.98      | ~ r1_xboole_0(X0_40,X1_40) ),
% 4.10/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_696,plain,
% 4.10/0.98      ( r2_hidden(X0_41,X0_40) != iProver_top
% 4.10/0.98      | r2_hidden(X0_41,X1_40) != iProver_top
% 4.10/0.98      | r1_xboole_0(X1_40,X0_40) != iProver_top ),
% 4.10/0.98      inference(predicate_to_equality,[status(thm)],[c_279]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_4890,plain,
% 4.10/0.98      ( r2_hidden(sK4,X0_40) != iProver_top
% 4.10/0.98      | r1_xboole_0(sK3,X0_40) != iProver_top ),
% 4.10/0.98      inference(superposition,[status(thm)],[c_705,c_696]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_6582,plain,
% 4.10/0.98      ( r2_hidden(sK4,sK2) != iProver_top ),
% 4.10/0.98      inference(superposition,[status(thm)],[c_704,c_4890]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_13041,plain,
% 4.10/0.98      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)) = k1_xboole_0 ),
% 4.10/0.98      inference(superposition,[status(thm)],[c_4093,c_6582]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_0,plain,
% 4.10/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.10/0.98      inference(cnf_transformation,[],[f55]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_283,plain,
% 4.10/0.98      ( k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)) = k4_xboole_0(X1_40,k4_xboole_0(X1_40,X0_40)) ),
% 4.10/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_7,plain,
% 4.10/0.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 4.10/0.98      inference(cnf_transformation,[],[f58]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_8,plain,
% 4.10/0.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 4.10/0.98      inference(cnf_transformation,[],[f39]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_235,plain,
% 4.10/0.98      ( X0 != X1
% 4.10/0.98      | k4_xboole_0(X0,X2) != X3
% 4.10/0.98      | k4_xboole_0(X3,k4_xboole_0(X3,X1)) = X3 ),
% 4.10/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_8]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_236,plain,
% 4.10/0.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 4.10/0.98      inference(unflattening,[status(thm)],[c_235]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_268,plain,
% 4.10/0.98      ( k4_xboole_0(k4_xboole_0(X0_40,X1_40),k4_xboole_0(k4_xboole_0(X0_40,X1_40),X0_40)) = k4_xboole_0(X0_40,X1_40) ),
% 4.10/0.98      inference(subtyping,[status(esa)],[c_236]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_1423,plain,
% 4.10/0.98      ( k4_xboole_0(k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)),k4_xboole_0(k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)),X1_40)) = k4_xboole_0(X1_40,k4_xboole_0(X1_40,X0_40)) ),
% 4.10/0.98      inference(superposition,[status(thm)],[c_283,c_268]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_13106,plain,
% 4.10/0.98      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 4.10/0.98      inference(superposition,[status(thm)],[c_13041,c_1423]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_1,plain,
% 4.10/0.98      ( r1_xboole_0(X0,X1)
% 4.10/0.98      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 4.10/0.98      inference(cnf_transformation,[],[f56]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_282,plain,
% 4.10/0.98      ( r1_xboole_0(X0_40,X1_40)
% 4.10/0.98      | k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)) != k1_xboole_0 ),
% 4.10/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_693,plain,
% 4.10/0.98      ( k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)) != k1_xboole_0
% 4.10/0.98      | r1_xboole_0(X0_40,X1_40) = iProver_top ),
% 4.10/0.98      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_2211,plain,
% 4.10/0.98      ( k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)) != k1_xboole_0
% 4.10/0.98      | r1_xboole_0(X1_40,X0_40) = iProver_top ),
% 4.10/0.98      inference(superposition,[status(thm)],[c_283,c_693]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_13876,plain,
% 4.10/0.98      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 4.10/0.98      inference(superposition,[status(thm)],[c_13106,c_2211]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_3,plain,
% 4.10/0.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 4.10/0.98      inference(cnf_transformation,[],[f34]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_280,plain,
% 4.10/0.98      ( ~ r1_xboole_0(X0_40,X1_40) | r1_xboole_0(X1_40,X0_40) ),
% 4.10/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_1968,plain,
% 4.10/0.98      ( ~ r1_xboole_0(X0_40,sK2) | r1_xboole_0(sK2,X0_40) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_280]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_1969,plain,
% 4.10/0.98      ( r1_xboole_0(X0_40,sK2) != iProver_top
% 4.10/0.98      | r1_xboole_0(sK2,X0_40) = iProver_top ),
% 4.10/0.98      inference(predicate_to_equality,[status(thm)],[c_1968]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_1971,plain,
% 4.10/0.98      ( r1_xboole_0(sK2,sK1) = iProver_top
% 4.10/0.98      | r1_xboole_0(sK1,sK2) != iProver_top ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_1969]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_1106,plain,
% 4.10/0.98      ( r1_xboole_0(k2_xboole_0(X0_40,sK3),sK2)
% 4.10/0.98      | ~ r1_xboole_0(sK2,k2_xboole_0(X0_40,sK3)) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_280]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_1107,plain,
% 4.10/0.98      ( r1_xboole_0(k2_xboole_0(X0_40,sK3),sK2) = iProver_top
% 4.10/0.98      | r1_xboole_0(sK2,k2_xboole_0(X0_40,sK3)) != iProver_top ),
% 4.10/0.98      inference(predicate_to_equality,[status(thm)],[c_1106]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_1109,plain,
% 4.10/0.98      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) = iProver_top
% 4.10/0.98      | r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) != iProver_top ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_1107]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_12,plain,
% 4.10/0.98      ( ~ r1_xboole_0(X0,X1)
% 4.10/0.98      | ~ r1_xboole_0(X0,X2)
% 4.10/0.98      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 4.10/0.98      inference(cnf_transformation,[],[f42]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_274,plain,
% 4.10/0.98      ( ~ r1_xboole_0(X0_40,X1_40)
% 4.10/0.98      | ~ r1_xboole_0(X0_40,X2_40)
% 4.10/0.98      | r1_xboole_0(X0_40,k2_xboole_0(X1_40,X2_40)) ),
% 4.10/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_903,plain,
% 4.10/0.98      ( ~ r1_xboole_0(sK2,X0_40)
% 4.10/0.98      | r1_xboole_0(sK2,k2_xboole_0(X0_40,sK3))
% 4.10/0.98      | ~ r1_xboole_0(sK2,sK3) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_274]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_904,plain,
% 4.10/0.98      ( r1_xboole_0(sK2,X0_40) != iProver_top
% 4.10/0.98      | r1_xboole_0(sK2,k2_xboole_0(X0_40,sK3)) = iProver_top
% 4.10/0.98      | r1_xboole_0(sK2,sK3) != iProver_top ),
% 4.10/0.98      inference(predicate_to_equality,[status(thm)],[c_903]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_906,plain,
% 4.10/0.98      ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) = iProver_top
% 4.10/0.98      | r1_xboole_0(sK2,sK3) != iProver_top
% 4.10/0.98      | r1_xboole_0(sK2,sK1) != iProver_top ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_904]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_816,plain,
% 4.10/0.98      ( r1_xboole_0(sK2,sK3) | ~ r1_xboole_0(sK3,sK2) ),
% 4.10/0.98      inference(instantiation,[status(thm)],[c_280]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_817,plain,
% 4.10/0.98      ( r1_xboole_0(sK2,sK3) = iProver_top
% 4.10/0.98      | r1_xboole_0(sK3,sK2) != iProver_top ),
% 4.10/0.98      inference(predicate_to_equality,[status(thm)],[c_816]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_14,negated_conjecture,
% 4.10/0.98      ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
% 4.10/0.98      inference(cnf_transformation,[],[f52]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_21,plain,
% 4.10/0.98      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) != iProver_top ),
% 4.10/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(c_20,plain,
% 4.10/0.98      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 4.10/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.10/0.98  
% 4.10/0.98  cnf(contradiction,plain,
% 4.10/0.98      ( $false ),
% 4.10/0.98      inference(minisat,
% 4.10/0.98                [status(thm)],
% 4.10/0.98                [c_13876,c_1971,c_1109,c_906,c_817,c_21,c_20]) ).
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.10/0.98  
% 4.10/0.98  ------                               Statistics
% 4.10/0.98  
% 4.10/0.98  ------ Selected
% 4.10/0.98  
% 4.10/0.98  total_time:                             0.433
% 4.10/0.98  
%------------------------------------------------------------------------------
