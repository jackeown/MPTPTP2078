%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:37 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 452 expanded)
%              Number of clauses        :   78 ( 165 expanded)
%              Number of leaves         :   20 ( 112 expanded)
%              Depth                    :   24
%              Number of atoms          :  300 (1040 expanded)
%              Number of equality atoms :   84 ( 287 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f27])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f23])).

fof(f29,plain,
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

fof(f30,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f29])).

fof(f48,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f52])).

fof(f55,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    r1_xboole_0(sK4,sK3) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f25])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_288,plain,
    ( k3_xboole_0(X0_40,X1_40) = k3_xboole_0(X1_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_282,plain,
    ( r2_hidden(sK1(X0_40,X1_40),k3_xboole_0(X0_40,X1_40))
    | r1_xboole_0(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_8,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_291,plain,
    ( r2_hidden(sK1(X0_40,X1_40),k3_xboole_0(X1_40,X0_40))
    | r1_xboole_0(X0_40,X1_40) ),
    inference(theory_normalisation,[status(thm)],[c_282,c_8,c_1])).

cnf(c_569,plain,
    ( r2_hidden(sK1(X0_40,X1_40),k3_xboole_0(X1_40,X0_40)) = iProver_top
    | r1_xboole_0(X0_40,X1_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_3797,plain,
    ( r2_hidden(sK1(X0_40,X1_40),k3_xboole_0(X0_40,X1_40)) = iProver_top
    | r1_xboole_0(X0_40,X1_40) = iProver_top ),
    inference(superposition,[status(thm)],[c_288,c_569])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | r1_xboole_0(k2_enumset1(X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_277,plain,
    ( r2_hidden(X0_41,X0_40)
    | r2_hidden(X1_41,X0_40)
    | r1_xboole_0(k2_enumset1(X1_41,X1_41,X1_41,X0_41),X0_40) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_573,plain,
    ( r2_hidden(X0_41,X0_40) = iProver_top
    | r2_hidden(X1_41,X0_40) = iProver_top
    | r1_xboole_0(k2_enumset1(X1_41,X1_41,X1_41,X0_41),X0_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_174,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
    | k3_xboole_0(X1,X0) = X1
    | k3_xboole_0(sK2,sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_175,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_174])).

cnf(c_273,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_175])).

cnf(c_292,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = k3_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_273,c_8,c_1])).

cnf(c_281,plain,
    ( k3_xboole_0(k3_xboole_0(X0_40,X1_40),X2_40) = k3_xboole_0(X0_40,k3_xboole_0(X1_40,X2_40)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_283,plain,
    ( ~ r2_hidden(X0_41,k3_xboole_0(X0_40,X1_40))
    | ~ r1_xboole_0(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_290,plain,
    ( ~ r2_hidden(X0_41,k3_xboole_0(X0_40,X1_40))
    | ~ r1_xboole_0(X1_40,X0_40) ),
    inference(theory_normalisation,[status(thm)],[c_283,c_8,c_1])).

cnf(c_568,plain,
    ( r2_hidden(X0_41,k3_xboole_0(X0_40,X1_40)) != iProver_top
    | r1_xboole_0(X1_40,X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_2440,plain,
    ( r2_hidden(X0_41,k3_xboole_0(X0_40,k3_xboole_0(X1_40,X2_40))) != iProver_top
    | r1_xboole_0(X2_40,k3_xboole_0(X0_40,X1_40)) != iProver_top ),
    inference(superposition,[status(thm)],[c_281,c_568])).

cnf(c_18659,plain,
    ( r2_hidden(X0_41,k3_xboole_0(sK2,sK3)) != iProver_top
    | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_292,c_2440])).

cnf(c_19684,plain,
    ( r2_hidden(X0_41,k3_xboole_0(sK2,sK3)) != iProver_top
    | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_573,c_18659])).

cnf(c_295,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_309,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_300,plain,
    ( ~ r2_hidden(X0_41,X0_40)
    | r2_hidden(X1_41,X1_40)
    | X1_41 != X0_41
    | X1_40 != X0_40 ),
    theory(equality)).

cnf(c_1427,plain,
    ( r2_hidden(X0_41,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
    | ~ r2_hidden(X1_41,k3_xboole_0(sK2,sK3))
    | X0_41 != X1_41 ),
    inference(resolution,[status(thm)],[c_300,c_292])).

cnf(c_1428,plain,
    ( X0_41 != X1_41
    | r2_hidden(X0_41,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))) = iProver_top
    | r2_hidden(X1_41,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1427])).

cnf(c_1430,plain,
    ( sK5 != sK5
    | r2_hidden(sK5,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))) = iProver_top
    | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1428])).

cnf(c_299,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X2_40,X3_40)
    | X2_40 != X0_40
    | X3_40 != X1_40 ),
    theory(equality)).

cnf(c_294,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_1411,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X2_40,X1_40)
    | X2_40 != X0_40 ),
    inference(resolution,[status(thm)],[c_299,c_294])).

cnf(c_4573,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))),X0_40)
    | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),X0_40) ),
    inference(resolution,[status(thm)],[c_1411,c_292])).

cnf(c_1407,plain,
    ( r1_xboole_0(X0_40,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
    | ~ r1_xboole_0(X1_40,k3_xboole_0(sK2,sK3))
    | X0_40 != X1_40 ),
    inference(resolution,[status(thm)],[c_299,c_292])).

cnf(c_5068,plain,
    ( r1_xboole_0(X0_40,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
    | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK3))
    | X0_40 != k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(resolution,[status(thm)],[c_4573,c_1407])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_335,plain,
    ( r2_hidden(sK5,sK3)
    | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_286,plain,
    ( ~ r2_hidden(X0_41,X0_40)
    | ~ r2_hidden(X0_41,X1_40)
    | ~ r1_xboole_0(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_708,plain,
    ( ~ r2_hidden(X0_41,sK3)
    | ~ r2_hidden(X0_41,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_710,plain,
    ( ~ r2_hidden(sK5,sK3)
    | ~ r2_hidden(sK5,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_296,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_1201,plain,
    ( X0_40 != X1_40
    | X1_40 = X0_40 ),
    inference(resolution,[status(thm)],[c_296,c_294])).

cnf(c_2570,plain,
    ( k3_xboole_0(sK2,sK3) = k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(resolution,[status(thm)],[c_1201,c_292])).

cnf(c_2582,plain,
    ( ~ r1_xboole_0(X0_40,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
    | r1_xboole_0(X1_40,k3_xboole_0(sK2,sK3))
    | X1_40 != X0_40 ),
    inference(resolution,[status(thm)],[c_2570,c_299])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_284,plain,
    ( r2_hidden(sK0(X0_40,X1_40),X0_40)
    | r1_xboole_0(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_994,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(k3_xboole_0(X1_40,X0_40),X2_40) ),
    inference(resolution,[status(thm)],[c_290,c_284])).

cnf(c_2788,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X2_40,k3_xboole_0(sK2,sK3))
    | X2_40 != k3_xboole_0(X1_40,X0_40) ),
    inference(resolution,[status(thm)],[c_2582,c_994])).

cnf(c_3218,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
    | r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_2788,c_2570])).

cnf(c_3619,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3)
    | r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_3218,c_994])).

cnf(c_6162,plain,
    ( r1_xboole_0(X0_40,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
    | X0_40 != k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5068,c_16,c_15,c_335,c_710,c_3619])).

cnf(c_6195,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))) ),
    inference(resolution,[status(thm)],[c_6162,c_2570])).

cnf(c_6206,plain,
    ( ~ r2_hidden(X0_41,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
    | ~ r2_hidden(X0_41,k3_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_6195,c_286])).

cnf(c_6207,plain,
    ( r2_hidden(X0_41,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))) != iProver_top
    | r2_hidden(X0_41,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6206])).

cnf(c_6209,plain,
    ( r2_hidden(sK5,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))) != iProver_top
    | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6207])).

cnf(c_19687,plain,
    ( r2_hidden(X0_41,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19684,c_309,c_1430,c_6209])).

cnf(c_19694,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3797,c_19687])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_287,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X1_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_18054,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_18055,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top
    | r1_xboole_0(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18054])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_278,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | ~ r1_xboole_0(X0_40,X2_40)
    | r1_xboole_0(X0_40,k2_xboole_0(X1_40,X2_40)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_751,plain,
    ( ~ r1_xboole_0(sK3,X0_40)
    | r1_xboole_0(sK3,k2_xboole_0(X0_40,sK4))
    | ~ r1_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_2406,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
    | ~ r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_2407,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = iProver_top
    | r1_xboole_0(sK3,sK4) != iProver_top
    | r1_xboole_0(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2406])).

cnf(c_1762,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_1763,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) = iProver_top
    | r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1762])).

cnf(c_681,plain,
    ( r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_682,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top
    | r1_xboole_0(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_681])).

cnf(c_14,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_20,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19694,c_18055,c_2407,c_1763,c_682,c_21,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.70/1.11  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.11  
% 2.70/1.11  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.70/1.11  
% 2.70/1.11  ------  iProver source info
% 2.70/1.11  
% 2.70/1.11  git: date: 2020-06-30 10:37:57 +0100
% 2.70/1.11  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.70/1.11  git: non_committed_changes: false
% 2.70/1.11  git: last_make_outside_of_git: false
% 2.70/1.11  
% 2.70/1.11  ------ 
% 2.70/1.11  ------ Parsing...
% 2.70/1.11  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.70/1.11  
% 2.70/1.11  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.70/1.11  
% 2.70/1.11  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.70/1.11  
% 2.70/1.11  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.70/1.11  ------ Proving...
% 2.70/1.11  ------ Problem Properties 
% 2.70/1.11  
% 2.70/1.11  
% 2.70/1.11  clauses                                 17
% 2.70/1.11  conjectures                             3
% 2.70/1.11  EPR                                     4
% 2.70/1.11  Horn                                    13
% 2.70/1.11  unary                                   7
% 2.70/1.11  binary                                  7
% 2.70/1.11  lits                                    30
% 2.70/1.11  lits eq                                 4
% 2.70/1.11  fd_pure                                 0
% 2.70/1.11  fd_pseudo                               0
% 2.70/1.11  fd_cond                                 0
% 2.70/1.11  fd_pseudo_cond                          0
% 2.70/1.11  AC symbols                              1
% 2.70/1.11  
% 2.70/1.11  ------ Input Options Time Limit: Unbounded
% 2.70/1.11  
% 2.70/1.11  
% 2.70/1.11  ------ 
% 2.70/1.11  Current options:
% 2.70/1.11  ------ 
% 2.70/1.11  
% 2.70/1.11  
% 2.70/1.11  
% 2.70/1.11  
% 2.70/1.11  ------ Proving...
% 2.70/1.11  
% 2.70/1.11  
% 2.70/1.11  % SZS status Theorem for theBenchmark.p
% 2.70/1.11  
% 2.70/1.11  % SZS output start CNFRefutation for theBenchmark.p
% 2.70/1.11  
% 2.70/1.11  fof(f2,axiom,(
% 2.70/1.11    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.70/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.11  
% 2.70/1.11  fof(f32,plain,(
% 2.70/1.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.70/1.11    inference(cnf_transformation,[],[f2])).
% 2.70/1.11  
% 2.70/1.11  fof(f5,axiom,(
% 2.70/1.11    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.70/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.11  
% 2.70/1.11  fof(f16,plain,(
% 2.70/1.11    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.70/1.11    inference(rectify,[],[f5])).
% 2.70/1.11  
% 2.70/1.11  fof(f19,plain,(
% 2.70/1.11    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.70/1.11    inference(ennf_transformation,[],[f16])).
% 2.70/1.11  
% 2.70/1.11  fof(f27,plain,(
% 2.70/1.11    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 2.70/1.11    introduced(choice_axiom,[])).
% 2.70/1.11  
% 2.70/1.11  fof(f28,plain,(
% 2.70/1.11    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.70/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f27])).
% 2.70/1.11  
% 2.70/1.11  fof(f37,plain,(
% 2.70/1.11    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.70/1.11    inference(cnf_transformation,[],[f28])).
% 2.70/1.11  
% 2.70/1.11  fof(f6,axiom,(
% 2.70/1.11    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.70/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.11  
% 2.70/1.11  fof(f39,plain,(
% 2.70/1.11    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.70/1.11    inference(cnf_transformation,[],[f6])).
% 2.70/1.11  
% 2.70/1.11  fof(f12,axiom,(
% 2.70/1.11    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 2.70/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.11  
% 2.70/1.11  fof(f22,plain,(
% 2.70/1.11    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 2.70/1.11    inference(ennf_transformation,[],[f12])).
% 2.70/1.11  
% 2.70/1.11  fof(f47,plain,(
% 2.70/1.11    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 2.70/1.11    inference(cnf_transformation,[],[f22])).
% 2.70/1.11  
% 2.70/1.11  fof(f10,axiom,(
% 2.70/1.11    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.70/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.11  
% 2.70/1.11  fof(f45,plain,(
% 2.70/1.11    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.70/1.11    inference(cnf_transformation,[],[f10])).
% 2.70/1.11  
% 2.70/1.11  fof(f11,axiom,(
% 2.70/1.11    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.70/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.11  
% 2.70/1.11  fof(f46,plain,(
% 2.70/1.11    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.70/1.11    inference(cnf_transformation,[],[f11])).
% 2.70/1.11  
% 2.70/1.11  fof(f52,plain,(
% 2.70/1.11    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.70/1.11    inference(definition_unfolding,[],[f45,f46])).
% 2.70/1.11  
% 2.70/1.11  fof(f54,plain,(
% 2.70/1.11    ( ! [X2,X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 2.70/1.11    inference(definition_unfolding,[],[f47,f52])).
% 2.70/1.11  
% 2.70/1.11  fof(f7,axiom,(
% 2.70/1.11    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.70/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.11  
% 2.70/1.11  fof(f20,plain,(
% 2.70/1.11    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.70/1.11    inference(ennf_transformation,[],[f7])).
% 2.70/1.11  
% 2.70/1.11  fof(f40,plain,(
% 2.70/1.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.70/1.11    inference(cnf_transformation,[],[f20])).
% 2.70/1.11  
% 2.70/1.11  fof(f13,conjecture,(
% 2.70/1.11    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.70/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.11  
% 2.70/1.11  fof(f14,negated_conjecture,(
% 2.70/1.11    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.70/1.11    inference(negated_conjecture,[],[f13])).
% 2.70/1.11  
% 2.70/1.11  fof(f23,plain,(
% 2.70/1.11    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 2.70/1.11    inference(ennf_transformation,[],[f14])).
% 2.70/1.11  
% 2.70/1.11  fof(f24,plain,(
% 2.70/1.11    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 2.70/1.11    inference(flattening,[],[f23])).
% 2.70/1.11  
% 2.70/1.11  fof(f29,plain,(
% 2.70/1.11    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 2.70/1.11    introduced(choice_axiom,[])).
% 2.70/1.11  
% 2.70/1.11  fof(f30,plain,(
% 2.70/1.11    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 2.70/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f29])).
% 2.70/1.11  
% 2.70/1.11  fof(f48,plain,(
% 2.70/1.11    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 2.70/1.11    inference(cnf_transformation,[],[f30])).
% 2.70/1.11  
% 2.70/1.11  fof(f9,axiom,(
% 2.70/1.11    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.70/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.11  
% 2.70/1.11  fof(f44,plain,(
% 2.70/1.11    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.70/1.11    inference(cnf_transformation,[],[f9])).
% 2.70/1.11  
% 2.70/1.11  fof(f53,plain,(
% 2.70/1.11    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.70/1.11    inference(definition_unfolding,[],[f44,f52])).
% 2.70/1.11  
% 2.70/1.11  fof(f55,plain,(
% 2.70/1.11    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))),
% 2.70/1.11    inference(definition_unfolding,[],[f48,f53])).
% 2.70/1.11  
% 2.70/1.11  fof(f38,plain,(
% 2.70/1.11    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.70/1.11    inference(cnf_transformation,[],[f28])).
% 2.70/1.11  
% 2.70/1.11  fof(f49,plain,(
% 2.70/1.11    r2_hidden(sK5,sK4)),
% 2.70/1.11    inference(cnf_transformation,[],[f30])).
% 2.70/1.11  
% 2.70/1.11  fof(f50,plain,(
% 2.70/1.11    r1_xboole_0(sK4,sK3)),
% 2.70/1.11    inference(cnf_transformation,[],[f30])).
% 2.70/1.11  
% 2.70/1.11  fof(f4,axiom,(
% 2.70/1.11    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.70/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.11  
% 2.70/1.11  fof(f15,plain,(
% 2.70/1.11    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.70/1.11    inference(rectify,[],[f4])).
% 2.70/1.11  
% 2.70/1.11  fof(f18,plain,(
% 2.70/1.11    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.70/1.11    inference(ennf_transformation,[],[f15])).
% 2.70/1.11  
% 2.70/1.11  fof(f25,plain,(
% 2.70/1.11    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.70/1.11    introduced(choice_axiom,[])).
% 2.70/1.11  
% 2.70/1.11  fof(f26,plain,(
% 2.70/1.11    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.70/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f25])).
% 2.70/1.11  
% 2.70/1.11  fof(f36,plain,(
% 2.70/1.11    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.70/1.11    inference(cnf_transformation,[],[f26])).
% 2.70/1.11  
% 2.70/1.11  fof(f34,plain,(
% 2.70/1.11    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.70/1.11    inference(cnf_transformation,[],[f26])).
% 2.70/1.11  
% 2.70/1.11  fof(f3,axiom,(
% 2.70/1.11    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.70/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.11  
% 2.70/1.11  fof(f17,plain,(
% 2.70/1.11    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.70/1.11    inference(ennf_transformation,[],[f3])).
% 2.70/1.11  
% 2.70/1.11  fof(f33,plain,(
% 2.70/1.11    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.70/1.11    inference(cnf_transformation,[],[f17])).
% 2.70/1.11  
% 2.70/1.11  fof(f8,axiom,(
% 2.70/1.11    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.70/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.11  
% 2.70/1.11  fof(f21,plain,(
% 2.70/1.11    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.70/1.11    inference(ennf_transformation,[],[f8])).
% 2.70/1.11  
% 2.70/1.11  fof(f41,plain,(
% 2.70/1.11    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.70/1.11    inference(cnf_transformation,[],[f21])).
% 2.70/1.11  
% 2.70/1.11  fof(f51,plain,(
% 2.70/1.11    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 2.70/1.11    inference(cnf_transformation,[],[f30])).
% 2.70/1.11  
% 2.70/1.11  cnf(c_1,plain,
% 2.70/1.11      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.70/1.11      inference(cnf_transformation,[],[f32]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_288,plain,
% 2.70/1.11      ( k3_xboole_0(X0_40,X1_40) = k3_xboole_0(X1_40,X0_40) ),
% 2.70/1.11      inference(subtyping,[status(esa)],[c_1]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_7,plain,
% 2.70/1.11      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 2.70/1.11      inference(cnf_transformation,[],[f37]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_282,plain,
% 2.70/1.11      ( r2_hidden(sK1(X0_40,X1_40),k3_xboole_0(X0_40,X1_40))
% 2.70/1.11      | r1_xboole_0(X0_40,X1_40) ),
% 2.70/1.11      inference(subtyping,[status(esa)],[c_7]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_8,plain,
% 2.70/1.11      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 2.70/1.11      inference(cnf_transformation,[],[f39]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_291,plain,
% 2.70/1.11      ( r2_hidden(sK1(X0_40,X1_40),k3_xboole_0(X1_40,X0_40))
% 2.70/1.11      | r1_xboole_0(X0_40,X1_40) ),
% 2.70/1.11      inference(theory_normalisation,[status(thm)],[c_282,c_8,c_1]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_569,plain,
% 2.70/1.11      ( r2_hidden(sK1(X0_40,X1_40),k3_xboole_0(X1_40,X0_40)) = iProver_top
% 2.70/1.11      | r1_xboole_0(X0_40,X1_40) = iProver_top ),
% 2.70/1.11      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_3797,plain,
% 2.70/1.11      ( r2_hidden(sK1(X0_40,X1_40),k3_xboole_0(X0_40,X1_40)) = iProver_top
% 2.70/1.11      | r1_xboole_0(X0_40,X1_40) = iProver_top ),
% 2.70/1.11      inference(superposition,[status(thm)],[c_288,c_569]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_13,plain,
% 2.70/1.11      ( r2_hidden(X0,X1)
% 2.70/1.11      | r2_hidden(X2,X1)
% 2.70/1.11      | r1_xboole_0(k2_enumset1(X2,X2,X2,X0),X1) ),
% 2.70/1.11      inference(cnf_transformation,[],[f54]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_277,plain,
% 2.70/1.11      ( r2_hidden(X0_41,X0_40)
% 2.70/1.11      | r2_hidden(X1_41,X0_40)
% 2.70/1.11      | r1_xboole_0(k2_enumset1(X1_41,X1_41,X1_41,X0_41),X0_40) ),
% 2.70/1.11      inference(subtyping,[status(esa)],[c_13]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_573,plain,
% 2.70/1.11      ( r2_hidden(X0_41,X0_40) = iProver_top
% 2.70/1.11      | r2_hidden(X1_41,X0_40) = iProver_top
% 2.70/1.11      | r1_xboole_0(k2_enumset1(X1_41,X1_41,X1_41,X0_41),X0_40) = iProver_top ),
% 2.70/1.11      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_9,plain,
% 2.70/1.11      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.70/1.11      inference(cnf_transformation,[],[f40]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_17,negated_conjecture,
% 2.70/1.11      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 2.70/1.11      inference(cnf_transformation,[],[f55]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_174,plain,
% 2.70/1.11      ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
% 2.70/1.11      | k3_xboole_0(X1,X0) = X1
% 2.70/1.11      | k3_xboole_0(sK2,sK3) != X1 ),
% 2.70/1.11      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_175,plain,
% 2.70/1.11      ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
% 2.70/1.11      inference(unflattening,[status(thm)],[c_174]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_273,plain,
% 2.70/1.11      ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
% 2.70/1.11      inference(subtyping,[status(esa)],[c_175]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_292,plain,
% 2.70/1.11      ( k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = k3_xboole_0(sK2,sK3) ),
% 2.70/1.11      inference(theory_normalisation,[status(thm)],[c_273,c_8,c_1]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_281,plain,
% 2.70/1.11      ( k3_xboole_0(k3_xboole_0(X0_40,X1_40),X2_40) = k3_xboole_0(X0_40,k3_xboole_0(X1_40,X2_40)) ),
% 2.70/1.11      inference(subtyping,[status(esa)],[c_8]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_6,plain,
% 2.70/1.11      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 2.70/1.11      inference(cnf_transformation,[],[f38]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_283,plain,
% 2.70/1.11      ( ~ r2_hidden(X0_41,k3_xboole_0(X0_40,X1_40))
% 2.70/1.11      | ~ r1_xboole_0(X0_40,X1_40) ),
% 2.70/1.11      inference(subtyping,[status(esa)],[c_6]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_290,plain,
% 2.70/1.11      ( ~ r2_hidden(X0_41,k3_xboole_0(X0_40,X1_40))
% 2.70/1.11      | ~ r1_xboole_0(X1_40,X0_40) ),
% 2.70/1.11      inference(theory_normalisation,[status(thm)],[c_283,c_8,c_1]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_568,plain,
% 2.70/1.11      ( r2_hidden(X0_41,k3_xboole_0(X0_40,X1_40)) != iProver_top
% 2.70/1.11      | r1_xboole_0(X1_40,X0_40) != iProver_top ),
% 2.70/1.11      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_2440,plain,
% 2.70/1.11      ( r2_hidden(X0_41,k3_xboole_0(X0_40,k3_xboole_0(X1_40,X2_40))) != iProver_top
% 2.70/1.11      | r1_xboole_0(X2_40,k3_xboole_0(X0_40,X1_40)) != iProver_top ),
% 2.70/1.11      inference(superposition,[status(thm)],[c_281,c_568]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_18659,plain,
% 2.70/1.11      ( r2_hidden(X0_41,k3_xboole_0(sK2,sK3)) != iProver_top
% 2.70/1.11      | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)) != iProver_top ),
% 2.70/1.11      inference(superposition,[status(thm)],[c_292,c_2440]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_19684,plain,
% 2.70/1.11      ( r2_hidden(X0_41,k3_xboole_0(sK2,sK3)) != iProver_top
% 2.70/1.11      | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) = iProver_top ),
% 2.70/1.11      inference(superposition,[status(thm)],[c_573,c_18659]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_295,plain,( X0_41 = X0_41 ),theory(equality) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_309,plain,
% 2.70/1.11      ( sK5 = sK5 ),
% 2.70/1.11      inference(instantiation,[status(thm)],[c_295]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_300,plain,
% 2.70/1.11      ( ~ r2_hidden(X0_41,X0_40)
% 2.70/1.11      | r2_hidden(X1_41,X1_40)
% 2.70/1.11      | X1_41 != X0_41
% 2.70/1.11      | X1_40 != X0_40 ),
% 2.70/1.11      theory(equality) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_1427,plain,
% 2.70/1.11      ( r2_hidden(X0_41,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
% 2.70/1.11      | ~ r2_hidden(X1_41,k3_xboole_0(sK2,sK3))
% 2.70/1.11      | X0_41 != X1_41 ),
% 2.70/1.11      inference(resolution,[status(thm)],[c_300,c_292]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_1428,plain,
% 2.70/1.11      ( X0_41 != X1_41
% 2.70/1.11      | r2_hidden(X0_41,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))) = iProver_top
% 2.70/1.11      | r2_hidden(X1_41,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 2.70/1.11      inference(predicate_to_equality,[status(thm)],[c_1427]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_1430,plain,
% 2.70/1.11      ( sK5 != sK5
% 2.70/1.11      | r2_hidden(sK5,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))) = iProver_top
% 2.70/1.11      | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 2.70/1.11      inference(instantiation,[status(thm)],[c_1428]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_299,plain,
% 2.70/1.11      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.70/1.11      | r1_xboole_0(X2_40,X3_40)
% 2.70/1.11      | X2_40 != X0_40
% 2.70/1.11      | X3_40 != X1_40 ),
% 2.70/1.11      theory(equality) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_294,plain,( X0_40 = X0_40 ),theory(equality) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_1411,plain,
% 2.70/1.11      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.70/1.11      | r1_xboole_0(X2_40,X1_40)
% 2.70/1.11      | X2_40 != X0_40 ),
% 2.70/1.11      inference(resolution,[status(thm)],[c_299,c_294]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_4573,plain,
% 2.70/1.11      ( r1_xboole_0(k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))),X0_40)
% 2.70/1.11      | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),X0_40) ),
% 2.70/1.11      inference(resolution,[status(thm)],[c_1411,c_292]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_1407,plain,
% 2.70/1.11      ( r1_xboole_0(X0_40,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
% 2.70/1.11      | ~ r1_xboole_0(X1_40,k3_xboole_0(sK2,sK3))
% 2.70/1.11      | X0_40 != X1_40 ),
% 2.70/1.11      inference(resolution,[status(thm)],[c_299,c_292]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_5068,plain,
% 2.70/1.11      ( r1_xboole_0(X0_40,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
% 2.70/1.11      | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK3))
% 2.70/1.11      | X0_40 != k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 2.70/1.11      inference(resolution,[status(thm)],[c_4573,c_1407]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_16,negated_conjecture,
% 2.70/1.11      ( r2_hidden(sK5,sK4) ),
% 2.70/1.11      inference(cnf_transformation,[],[f49]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_15,negated_conjecture,
% 2.70/1.11      ( r1_xboole_0(sK4,sK3) ),
% 2.70/1.11      inference(cnf_transformation,[],[f50]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_335,plain,
% 2.70/1.11      ( r2_hidden(sK5,sK3)
% 2.70/1.11      | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) ),
% 2.70/1.11      inference(instantiation,[status(thm)],[c_277]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_3,plain,
% 2.70/1.11      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 2.70/1.11      inference(cnf_transformation,[],[f36]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_286,plain,
% 2.70/1.11      ( ~ r2_hidden(X0_41,X0_40)
% 2.70/1.11      | ~ r2_hidden(X0_41,X1_40)
% 2.70/1.11      | ~ r1_xboole_0(X0_40,X1_40) ),
% 2.70/1.11      inference(subtyping,[status(esa)],[c_3]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_708,plain,
% 2.70/1.11      ( ~ r2_hidden(X0_41,sK3)
% 2.70/1.11      | ~ r2_hidden(X0_41,sK4)
% 2.70/1.11      | ~ r1_xboole_0(sK4,sK3) ),
% 2.70/1.11      inference(instantiation,[status(thm)],[c_286]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_710,plain,
% 2.70/1.11      ( ~ r2_hidden(sK5,sK3)
% 2.70/1.11      | ~ r2_hidden(sK5,sK4)
% 2.70/1.11      | ~ r1_xboole_0(sK4,sK3) ),
% 2.70/1.11      inference(instantiation,[status(thm)],[c_708]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_296,plain,
% 2.70/1.11      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 2.70/1.11      theory(equality) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_1201,plain,
% 2.70/1.11      ( X0_40 != X1_40 | X1_40 = X0_40 ),
% 2.70/1.11      inference(resolution,[status(thm)],[c_296,c_294]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_2570,plain,
% 2.70/1.11      ( k3_xboole_0(sK2,sK3) = k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 2.70/1.11      inference(resolution,[status(thm)],[c_1201,c_292]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_2582,plain,
% 2.70/1.11      ( ~ r1_xboole_0(X0_40,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
% 2.70/1.11      | r1_xboole_0(X1_40,k3_xboole_0(sK2,sK3))
% 2.70/1.11      | X1_40 != X0_40 ),
% 2.70/1.11      inference(resolution,[status(thm)],[c_2570,c_299]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_5,plain,
% 2.70/1.11      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 2.70/1.11      inference(cnf_transformation,[],[f34]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_284,plain,
% 2.70/1.11      ( r2_hidden(sK0(X0_40,X1_40),X0_40) | r1_xboole_0(X0_40,X1_40) ),
% 2.70/1.11      inference(subtyping,[status(esa)],[c_5]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_994,plain,
% 2.70/1.11      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.70/1.11      | r1_xboole_0(k3_xboole_0(X1_40,X0_40),X2_40) ),
% 2.70/1.11      inference(resolution,[status(thm)],[c_290,c_284]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_2788,plain,
% 2.70/1.11      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.70/1.11      | r1_xboole_0(X2_40,k3_xboole_0(sK2,sK3))
% 2.70/1.11      | X2_40 != k3_xboole_0(X1_40,X0_40) ),
% 2.70/1.11      inference(resolution,[status(thm)],[c_2582,c_994]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_3218,plain,
% 2.70/1.11      ( ~ r1_xboole_0(k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)),sK2)
% 2.70/1.11      | r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK3)) ),
% 2.70/1.11      inference(resolution,[status(thm)],[c_2788,c_2570]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_3619,plain,
% 2.70/1.11      ( ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3)
% 2.70/1.11      | r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,sK3)) ),
% 2.70/1.11      inference(resolution,[status(thm)],[c_3218,c_994]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_6162,plain,
% 2.70/1.11      ( r1_xboole_0(X0_40,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
% 2.70/1.11      | X0_40 != k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 2.70/1.11      inference(global_propositional_subsumption,
% 2.70/1.11                [status(thm)],
% 2.70/1.11                [c_5068,c_16,c_15,c_335,c_710,c_3619]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_6195,plain,
% 2.70/1.11      ( r1_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))) ),
% 2.70/1.11      inference(resolution,[status(thm)],[c_6162,c_2570]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_6206,plain,
% 2.70/1.11      ( ~ r2_hidden(X0_41,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))))
% 2.70/1.11      | ~ r2_hidden(X0_41,k3_xboole_0(sK2,sK3)) ),
% 2.70/1.11      inference(resolution,[status(thm)],[c_6195,c_286]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_6207,plain,
% 2.70/1.11      ( r2_hidden(X0_41,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))) != iProver_top
% 2.70/1.11      | r2_hidden(X0_41,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 2.70/1.11      inference(predicate_to_equality,[status(thm)],[c_6206]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_6209,plain,
% 2.70/1.11      ( r2_hidden(sK5,k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)))) != iProver_top
% 2.70/1.11      | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 2.70/1.11      inference(instantiation,[status(thm)],[c_6207]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_19687,plain,
% 2.70/1.11      ( r2_hidden(X0_41,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 2.70/1.11      inference(global_propositional_subsumption,
% 2.70/1.11                [status(thm)],
% 2.70/1.11                [c_19684,c_309,c_1430,c_6209]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_19694,plain,
% 2.70/1.11      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 2.70/1.11      inference(superposition,[status(thm)],[c_3797,c_19687]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_2,plain,
% 2.70/1.11      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 2.70/1.11      inference(cnf_transformation,[],[f33]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_287,plain,
% 2.70/1.11      ( ~ r1_xboole_0(X0_40,X1_40) | r1_xboole_0(X1_40,X0_40) ),
% 2.70/1.11      inference(subtyping,[status(esa)],[c_2]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_18054,plain,
% 2.70/1.11      ( r1_xboole_0(sK3,sK2) | ~ r1_xboole_0(sK2,sK3) ),
% 2.70/1.11      inference(instantiation,[status(thm)],[c_287]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_18055,plain,
% 2.70/1.11      ( r1_xboole_0(sK3,sK2) = iProver_top
% 2.70/1.11      | r1_xboole_0(sK2,sK3) != iProver_top ),
% 2.70/1.11      inference(predicate_to_equality,[status(thm)],[c_18054]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_12,plain,
% 2.70/1.11      ( ~ r1_xboole_0(X0,X1)
% 2.70/1.11      | ~ r1_xboole_0(X0,X2)
% 2.70/1.11      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 2.70/1.11      inference(cnf_transformation,[],[f41]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_278,plain,
% 2.70/1.11      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.70/1.11      | ~ r1_xboole_0(X0_40,X2_40)
% 2.70/1.11      | r1_xboole_0(X0_40,k2_xboole_0(X1_40,X2_40)) ),
% 2.70/1.11      inference(subtyping,[status(esa)],[c_12]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_751,plain,
% 2.70/1.11      ( ~ r1_xboole_0(sK3,X0_40)
% 2.70/1.11      | r1_xboole_0(sK3,k2_xboole_0(X0_40,sK4))
% 2.70/1.11      | ~ r1_xboole_0(sK3,sK4) ),
% 2.70/1.11      inference(instantiation,[status(thm)],[c_278]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_2406,plain,
% 2.70/1.11      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
% 2.70/1.11      | ~ r1_xboole_0(sK3,sK4)
% 2.70/1.11      | ~ r1_xboole_0(sK3,sK2) ),
% 2.70/1.11      inference(instantiation,[status(thm)],[c_751]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_2407,plain,
% 2.70/1.11      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = iProver_top
% 2.70/1.11      | r1_xboole_0(sK3,sK4) != iProver_top
% 2.70/1.11      | r1_xboole_0(sK3,sK2) != iProver_top ),
% 2.70/1.11      inference(predicate_to_equality,[status(thm)],[c_2406]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_1762,plain,
% 2.70/1.11      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
% 2.70/1.11      | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
% 2.70/1.11      inference(instantiation,[status(thm)],[c_287]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_1763,plain,
% 2.70/1.11      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) = iProver_top
% 2.70/1.11      | r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != iProver_top ),
% 2.70/1.11      inference(predicate_to_equality,[status(thm)],[c_1762]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_681,plain,
% 2.70/1.11      ( r1_xboole_0(sK3,sK4) | ~ r1_xboole_0(sK4,sK3) ),
% 2.70/1.11      inference(instantiation,[status(thm)],[c_287]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_682,plain,
% 2.70/1.11      ( r1_xboole_0(sK3,sK4) = iProver_top
% 2.70/1.11      | r1_xboole_0(sK4,sK3) != iProver_top ),
% 2.70/1.11      inference(predicate_to_equality,[status(thm)],[c_681]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_14,negated_conjecture,
% 2.70/1.11      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 2.70/1.11      inference(cnf_transformation,[],[f51]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_21,plain,
% 2.70/1.11      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) != iProver_top ),
% 2.70/1.11      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(c_20,plain,
% 2.70/1.11      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 2.70/1.11      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.70/1.11  
% 2.70/1.11  cnf(contradiction,plain,
% 2.70/1.11      ( $false ),
% 2.70/1.11      inference(minisat,
% 2.70/1.11                [status(thm)],
% 2.70/1.11                [c_19694,c_18055,c_2407,c_1763,c_682,c_21,c_20]) ).
% 2.70/1.11  
% 2.70/1.11  
% 2.70/1.11  % SZS output end CNFRefutation for theBenchmark.p
% 2.70/1.11  
% 2.70/1.11  ------                               Statistics
% 2.70/1.11  
% 2.70/1.11  ------ Selected
% 2.70/1.11  
% 2.70/1.11  total_time:                             0.536
% 2.70/1.11  
%------------------------------------------------------------------------------
