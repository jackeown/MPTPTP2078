%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:14 EST 2020

% Result     : Theorem 7.86s
% Output     : CNFRefutation 7.86s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 141 expanded)
%              Number of clauses        :   54 (  61 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :  209 ( 300 expanded)
%              Number of equality atoms :   72 (  95 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f31,f31])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK1,k3_xboole_0(sK2,sK3))
      & r1_tarski(sK1,sK3)
      & ~ r1_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( r1_xboole_0(sK1,k3_xboole_0(sK2,sK3))
    & r1_tarski(sK1,sK3)
    & ~ r1_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22])).

fof(f35,plain,(
    r1_xboole_0(sK1,k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(definition_unfolding,[],[f35,f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f31,f31])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f20])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f34,plain,(
    r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_103,plain,
    ( k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)) = k4_xboole_0(X1_36,k4_xboole_0(X1_36,X0_36)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_97,plain,
    ( r1_tarski(k4_xboole_0(X0_36,X1_36),X0_36) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_303,plain,
    ( r1_tarski(k4_xboole_0(X0_36,X1_36),X0_36) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_97])).

cnf(c_555,plain,
    ( r1_tarski(k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)),X1_36) = iProver_top ),
    inference(superposition,[status(thm)],[c_103,c_303])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_98,plain,
    ( ~ r1_tarski(X0_36,X1_36)
    | k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)) = X0_36 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_302,plain,
    ( k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)) = X0_36
    | r1_tarski(X0_36,X1_36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_98])).

cnf(c_1086,plain,
    ( k4_xboole_0(k4_xboole_0(X0_36,X1_36),k4_xboole_0(k4_xboole_0(X0_36,X1_36),X0_36)) = k4_xboole_0(X0_36,X1_36) ),
    inference(superposition,[status(thm)],[c_303,c_302])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_95,negated_conjecture,
    ( r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_305,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_95])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_102,plain,
    ( ~ r1_xboole_0(X0_36,X1_36)
    | r1_xboole_0(X1_36,X0_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_298,plain,
    ( r1_xboole_0(X0_36,X1_36) != iProver_top
    | r1_xboole_0(X1_36,X0_36) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_102])).

cnf(c_685,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_305,c_298])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,X0)),k4_xboole_0(X3,k4_xboole_0(X3,X1))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_99,plain,
    ( ~ r1_tarski(X0_36,X1_36)
    | ~ r1_tarski(X2_36,X3_36)
    | r1_tarski(k4_xboole_0(X2_36,k4_xboole_0(X2_36,X0_36)),k4_xboole_0(X3_36,k4_xboole_0(X3_36,X1_36))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_301,plain,
    ( r1_tarski(X0_36,X1_36) != iProver_top
    | r1_tarski(X2_36,X3_36) != iProver_top
    | r1_tarski(k4_xboole_0(X2_36,k4_xboole_0(X2_36,X0_36)),k4_xboole_0(X3_36,k4_xboole_0(X3_36,X1_36))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_96,plain,
    ( ~ r1_tarski(X0_36,X1_36)
    | ~ r1_xboole_0(X1_36,X2_36)
    | r1_xboole_0(X0_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_304,plain,
    ( r1_tarski(X0_36,X1_36) != iProver_top
    | r1_xboole_0(X1_36,X2_36) != iProver_top
    | r1_xboole_0(X0_36,X2_36) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_96])).

cnf(c_1928,plain,
    ( r1_tarski(X0_36,X1_36) != iProver_top
    | r1_tarski(X2_36,X3_36) != iProver_top
    | r1_xboole_0(k4_xboole_0(X3_36,k4_xboole_0(X3_36,X1_36)),X4_36) != iProver_top
    | r1_xboole_0(k4_xboole_0(X2_36,k4_xboole_0(X2_36,X0_36)),X4_36) = iProver_top ),
    inference(superposition,[status(thm)],[c_301,c_304])).

cnf(c_19529,plain,
    ( r1_tarski(X0_36,sK3) != iProver_top
    | r1_tarski(X1_36,sK2) != iProver_top
    | r1_xboole_0(k4_xboole_0(X1_36,k4_xboole_0(X1_36,X0_36)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_685,c_1928])).

cnf(c_22418,plain,
    ( r1_tarski(X0_36,sK3) != iProver_top
    | r1_tarski(k4_xboole_0(X0_36,X1_36),sK2) != iProver_top
    | r1_xboole_0(k4_xboole_0(X0_36,X1_36),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1086,c_19529])).

cnf(c_30946,plain,
    ( r1_tarski(X0_36,sK3) != iProver_top
    | r1_xboole_0(k4_xboole_0(X0_36,k4_xboole_0(X0_36,sK2)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_555,c_22418])).

cnf(c_31094,plain,
    ( r1_tarski(sK1,sK3) != iProver_top
    | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_30946])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_101,plain,
    ( ~ r2_hidden(X0_37,k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)))
    | ~ r1_xboole_0(X0_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_22903,plain,
    ( ~ r2_hidden(sK0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36)))
    | ~ r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36) ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_22904,plain,
    ( r2_hidden(sK0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36))) != iProver_top
    | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22903])).

cnf(c_22906,plain,
    ( r2_hidden(sK0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))) != iProver_top
    | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_22904])).

cnf(c_8416,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_2433,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36)
    | k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_2439,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
    | k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2433])).

cnf(c_110,plain,
    ( ~ r2_hidden(X0_37,X0_36)
    | r2_hidden(X1_37,X1_36)
    | X1_37 != X0_37
    | X1_36 != X0_36 ),
    theory(equality)).

cnf(c_497,plain,
    ( r2_hidden(X0_37,X0_36)
    | ~ r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | X0_37 != sK0(sK1,sK2)
    | X0_36 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_641,plain,
    ( r2_hidden(sK0(sK1,sK2),X0_36)
    | ~ r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | sK0(sK1,sK2) != sK0(sK1,sK2)
    | X0_36 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_1232,plain,
    ( r2_hidden(sK0(sK1,sK2),k4_xboole_0(X0_36,X1_36))
    | ~ r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | sK0(sK1,sK2) != sK0(sK1,sK2)
    | k4_xboole_0(X0_36,X1_36) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_641])).

cnf(c_2432,plain,
    ( r2_hidden(sK0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36)))
    | ~ r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | sK0(sK1,sK2) != sK0(sK1,sK2)
    | k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_2434,plain,
    ( sK0(sK1,sK2) != sK0(sK1,sK2)
    | k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | r2_hidden(sK0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36))) = iProver_top
    | r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2432])).

cnf(c_2436,plain,
    ( sK0(sK1,sK2) != sK0(sK1,sK2)
    | k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | r2_hidden(sK0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))) = iProver_top
    | r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2434])).

cnf(c_106,plain,
    ( X0_37 = X0_37 ),
    theory(equality)).

cnf(c_642,plain,
    ( sK0(sK1,sK2) = sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_106])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_100,plain,
    ( r2_hidden(sK0(X0_36,X1_36),k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)))
    | r1_xboole_0(X0_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_395,plain,
    ( r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | r1_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_396,plain,
    ( r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top
    | r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_12,plain,
    ( r1_tarski(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,plain,
    ( r1_xboole_0(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31094,c_22906,c_8416,c_2439,c_2436,c_642,c_396,c_12,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.86/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.86/1.50  
% 7.86/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.86/1.50  
% 7.86/1.50  ------  iProver source info
% 7.86/1.50  
% 7.86/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.86/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.86/1.50  git: non_committed_changes: false
% 7.86/1.50  git: last_make_outside_of_git: false
% 7.86/1.50  
% 7.86/1.50  ------ 
% 7.86/1.50  ------ Parsing...
% 7.86/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.86/1.50  
% 7.86/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.86/1.50  
% 7.86/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.86/1.50  
% 7.86/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.86/1.50  ------ Proving...
% 7.86/1.50  ------ Problem Properties 
% 7.86/1.50  
% 7.86/1.50  
% 7.86/1.50  clauses                                 11
% 7.86/1.50  conjectures                             3
% 7.86/1.50  EPR                                     4
% 7.86/1.50  Horn                                    10
% 7.86/1.50  unary                                   5
% 7.86/1.50  binary                                  4
% 7.86/1.50  lits                                    19
% 7.86/1.50  lits eq                                 2
% 7.86/1.50  fd_pure                                 0
% 7.86/1.50  fd_pseudo                               0
% 7.86/1.50  fd_cond                                 0
% 7.86/1.50  fd_pseudo_cond                          0
% 7.86/1.50  AC symbols                              0
% 7.86/1.50  
% 7.86/1.50  ------ Input Options Time Limit: Unbounded
% 7.86/1.50  
% 7.86/1.50  
% 7.86/1.50  ------ 
% 7.86/1.50  Current options:
% 7.86/1.50  ------ 
% 7.86/1.50  
% 7.86/1.50  
% 7.86/1.50  
% 7.86/1.50  
% 7.86/1.50  ------ Proving...
% 7.86/1.50  
% 7.86/1.50  
% 7.86/1.50  % SZS status Theorem for theBenchmark.p
% 7.86/1.50  
% 7.86/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.86/1.50  
% 7.86/1.50  fof(f1,axiom,(
% 7.86/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.86/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.50  
% 7.86/1.50  fof(f24,plain,(
% 7.86/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.86/1.50    inference(cnf_transformation,[],[f1])).
% 7.86/1.50  
% 7.86/1.50  fof(f7,axiom,(
% 7.86/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.86/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.50  
% 7.86/1.50  fof(f31,plain,(
% 7.86/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.86/1.50    inference(cnf_transformation,[],[f7])).
% 7.86/1.50  
% 7.86/1.50  fof(f36,plain,(
% 7.86/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.86/1.50    inference(definition_unfolding,[],[f24,f31,f31])).
% 7.86/1.50  
% 7.86/1.50  fof(f6,axiom,(
% 7.86/1.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.86/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.50  
% 7.86/1.50  fof(f30,plain,(
% 7.86/1.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.86/1.50    inference(cnf_transformation,[],[f6])).
% 7.86/1.50  
% 7.86/1.50  fof(f5,axiom,(
% 7.86/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.86/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.50  
% 7.86/1.50  fof(f16,plain,(
% 7.86/1.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.86/1.50    inference(ennf_transformation,[],[f5])).
% 7.86/1.50  
% 7.86/1.50  fof(f29,plain,(
% 7.86/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.86/1.50    inference(cnf_transformation,[],[f16])).
% 7.86/1.50  
% 7.86/1.50  fof(f40,plain,(
% 7.86/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.86/1.50    inference(definition_unfolding,[],[f29,f31])).
% 7.86/1.50  
% 7.86/1.50  fof(f9,conjecture,(
% 7.86/1.50    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 7.86/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.50  
% 7.86/1.50  fof(f10,negated_conjecture,(
% 7.86/1.50    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 7.86/1.50    inference(negated_conjecture,[],[f9])).
% 7.86/1.50  
% 7.86/1.50  fof(f19,plain,(
% 7.86/1.50    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 7.86/1.50    inference(ennf_transformation,[],[f10])).
% 7.86/1.50  
% 7.86/1.50  fof(f22,plain,(
% 7.86/1.50    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK1,k3_xboole_0(sK2,sK3)) & r1_tarski(sK1,sK3) & ~r1_xboole_0(sK1,sK2))),
% 7.86/1.50    introduced(choice_axiom,[])).
% 7.86/1.50  
% 7.86/1.50  fof(f23,plain,(
% 7.86/1.50    r1_xboole_0(sK1,k3_xboole_0(sK2,sK3)) & r1_tarski(sK1,sK3) & ~r1_xboole_0(sK1,sK2)),
% 7.86/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22])).
% 7.86/1.50  
% 7.86/1.50  fof(f35,plain,(
% 7.86/1.50    r1_xboole_0(sK1,k3_xboole_0(sK2,sK3))),
% 7.86/1.50    inference(cnf_transformation,[],[f23])).
% 7.86/1.50  
% 7.86/1.50  fof(f41,plain,(
% 7.86/1.50    r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),
% 7.86/1.50    inference(definition_unfolding,[],[f35,f31])).
% 7.86/1.50  
% 7.86/1.50  fof(f2,axiom,(
% 7.86/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.86/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.50  
% 7.86/1.50  fof(f12,plain,(
% 7.86/1.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.86/1.50    inference(ennf_transformation,[],[f2])).
% 7.86/1.50  
% 7.86/1.50  fof(f25,plain,(
% 7.86/1.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.86/1.50    inference(cnf_transformation,[],[f12])).
% 7.86/1.50  
% 7.86/1.50  fof(f4,axiom,(
% 7.86/1.50    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 7.86/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.50  
% 7.86/1.50  fof(f14,plain,(
% 7.86/1.50    ! [X0,X1,X2,X3] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 7.86/1.50    inference(ennf_transformation,[],[f4])).
% 7.86/1.50  
% 7.86/1.50  fof(f15,plain,(
% 7.86/1.50    ! [X0,X1,X2,X3] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 7.86/1.50    inference(flattening,[],[f14])).
% 7.86/1.50  
% 7.86/1.50  fof(f28,plain,(
% 7.86/1.50    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 7.86/1.50    inference(cnf_transformation,[],[f15])).
% 7.86/1.50  
% 7.86/1.50  fof(f39,plain,(
% 7.86/1.50    ( ! [X2,X0,X3,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 7.86/1.50    inference(definition_unfolding,[],[f28,f31,f31])).
% 7.86/1.50  
% 7.86/1.50  fof(f8,axiom,(
% 7.86/1.50    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 7.86/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.50  
% 7.86/1.50  fof(f17,plain,(
% 7.86/1.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.86/1.50    inference(ennf_transformation,[],[f8])).
% 7.86/1.50  
% 7.86/1.50  fof(f18,plain,(
% 7.86/1.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 7.86/1.50    inference(flattening,[],[f17])).
% 7.86/1.50  
% 7.86/1.50  fof(f32,plain,(
% 7.86/1.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.86/1.50    inference(cnf_transformation,[],[f18])).
% 7.86/1.50  
% 7.86/1.50  fof(f3,axiom,(
% 7.86/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.86/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.50  
% 7.86/1.50  fof(f11,plain,(
% 7.86/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.86/1.50    inference(rectify,[],[f3])).
% 7.86/1.50  
% 7.86/1.50  fof(f13,plain,(
% 7.86/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.86/1.50    inference(ennf_transformation,[],[f11])).
% 7.86/1.50  
% 7.86/1.50  fof(f20,plain,(
% 7.86/1.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.86/1.50    introduced(choice_axiom,[])).
% 7.86/1.50  
% 7.86/1.50  fof(f21,plain,(
% 7.86/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.86/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f20])).
% 7.86/1.50  
% 7.86/1.50  fof(f27,plain,(
% 7.86/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.86/1.50    inference(cnf_transformation,[],[f21])).
% 7.86/1.50  
% 7.86/1.50  fof(f37,plain,(
% 7.86/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.86/1.50    inference(definition_unfolding,[],[f27,f31])).
% 7.86/1.50  
% 7.86/1.50  fof(f26,plain,(
% 7.86/1.50    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 7.86/1.50    inference(cnf_transformation,[],[f21])).
% 7.86/1.50  
% 7.86/1.50  fof(f38,plain,(
% 7.86/1.50    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 7.86/1.50    inference(definition_unfolding,[],[f26,f31])).
% 7.86/1.50  
% 7.86/1.50  fof(f34,plain,(
% 7.86/1.50    r1_tarski(sK1,sK3)),
% 7.86/1.50    inference(cnf_transformation,[],[f23])).
% 7.86/1.50  
% 7.86/1.50  fof(f33,plain,(
% 7.86/1.50    ~r1_xboole_0(sK1,sK2)),
% 7.86/1.50    inference(cnf_transformation,[],[f23])).
% 7.86/1.50  
% 7.86/1.50  cnf(c_0,plain,
% 7.86/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.86/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_103,plain,
% 7.86/1.50      ( k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)) = k4_xboole_0(X1_36,k4_xboole_0(X1_36,X0_36)) ),
% 7.86/1.50      inference(subtyping,[status(esa)],[c_0]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_6,plain,
% 7.86/1.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.86/1.50      inference(cnf_transformation,[],[f30]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_97,plain,
% 7.86/1.50      ( r1_tarski(k4_xboole_0(X0_36,X1_36),X0_36) ),
% 7.86/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_303,plain,
% 7.86/1.50      ( r1_tarski(k4_xboole_0(X0_36,X1_36),X0_36) = iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_97]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_555,plain,
% 7.86/1.50      ( r1_tarski(k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)),X1_36) = iProver_top ),
% 7.86/1.50      inference(superposition,[status(thm)],[c_103,c_303]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_5,plain,
% 7.86/1.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.86/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_98,plain,
% 7.86/1.50      ( ~ r1_tarski(X0_36,X1_36)
% 7.86/1.50      | k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)) = X0_36 ),
% 7.86/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_302,plain,
% 7.86/1.50      ( k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)) = X0_36
% 7.86/1.50      | r1_tarski(X0_36,X1_36) != iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_98]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1086,plain,
% 7.86/1.50      ( k4_xboole_0(k4_xboole_0(X0_36,X1_36),k4_xboole_0(k4_xboole_0(X0_36,X1_36),X0_36)) = k4_xboole_0(X0_36,X1_36) ),
% 7.86/1.50      inference(superposition,[status(thm)],[c_303,c_302]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_8,negated_conjecture,
% 7.86/1.50      ( r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 7.86/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_95,negated_conjecture,
% 7.86/1.50      ( r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 7.86/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_305,plain,
% 7.86/1.50      ( r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_95]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1,plain,
% 7.86/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.86/1.50      inference(cnf_transformation,[],[f25]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_102,plain,
% 7.86/1.50      ( ~ r1_xboole_0(X0_36,X1_36) | r1_xboole_0(X1_36,X0_36) ),
% 7.86/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_298,plain,
% 7.86/1.50      ( r1_xboole_0(X0_36,X1_36) != iProver_top
% 7.86/1.50      | r1_xboole_0(X1_36,X0_36) = iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_102]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_685,plain,
% 7.86/1.50      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK1) = iProver_top ),
% 7.86/1.50      inference(superposition,[status(thm)],[c_305,c_298]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_4,plain,
% 7.86/1.50      ( ~ r1_tarski(X0,X1)
% 7.86/1.50      | ~ r1_tarski(X2,X3)
% 7.86/1.50      | r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,X0)),k4_xboole_0(X3,k4_xboole_0(X3,X1))) ),
% 7.86/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_99,plain,
% 7.86/1.50      ( ~ r1_tarski(X0_36,X1_36)
% 7.86/1.50      | ~ r1_tarski(X2_36,X3_36)
% 7.86/1.50      | r1_tarski(k4_xboole_0(X2_36,k4_xboole_0(X2_36,X0_36)),k4_xboole_0(X3_36,k4_xboole_0(X3_36,X1_36))) ),
% 7.86/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_301,plain,
% 7.86/1.50      ( r1_tarski(X0_36,X1_36) != iProver_top
% 7.86/1.50      | r1_tarski(X2_36,X3_36) != iProver_top
% 7.86/1.50      | r1_tarski(k4_xboole_0(X2_36,k4_xboole_0(X2_36,X0_36)),k4_xboole_0(X3_36,k4_xboole_0(X3_36,X1_36))) = iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_99]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_7,plain,
% 7.86/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 7.86/1.50      inference(cnf_transformation,[],[f32]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_96,plain,
% 7.86/1.50      ( ~ r1_tarski(X0_36,X1_36)
% 7.86/1.50      | ~ r1_xboole_0(X1_36,X2_36)
% 7.86/1.50      | r1_xboole_0(X0_36,X2_36) ),
% 7.86/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_304,plain,
% 7.86/1.50      ( r1_tarski(X0_36,X1_36) != iProver_top
% 7.86/1.50      | r1_xboole_0(X1_36,X2_36) != iProver_top
% 7.86/1.50      | r1_xboole_0(X0_36,X2_36) = iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_96]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1928,plain,
% 7.86/1.50      ( r1_tarski(X0_36,X1_36) != iProver_top
% 7.86/1.50      | r1_tarski(X2_36,X3_36) != iProver_top
% 7.86/1.50      | r1_xboole_0(k4_xboole_0(X3_36,k4_xboole_0(X3_36,X1_36)),X4_36) != iProver_top
% 7.86/1.50      | r1_xboole_0(k4_xboole_0(X2_36,k4_xboole_0(X2_36,X0_36)),X4_36) = iProver_top ),
% 7.86/1.50      inference(superposition,[status(thm)],[c_301,c_304]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_19529,plain,
% 7.86/1.50      ( r1_tarski(X0_36,sK3) != iProver_top
% 7.86/1.50      | r1_tarski(X1_36,sK2) != iProver_top
% 7.86/1.50      | r1_xboole_0(k4_xboole_0(X1_36,k4_xboole_0(X1_36,X0_36)),sK1) = iProver_top ),
% 7.86/1.50      inference(superposition,[status(thm)],[c_685,c_1928]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_22418,plain,
% 7.86/1.50      ( r1_tarski(X0_36,sK3) != iProver_top
% 7.86/1.50      | r1_tarski(k4_xboole_0(X0_36,X1_36),sK2) != iProver_top
% 7.86/1.50      | r1_xboole_0(k4_xboole_0(X0_36,X1_36),sK1) = iProver_top ),
% 7.86/1.50      inference(superposition,[status(thm)],[c_1086,c_19529]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_30946,plain,
% 7.86/1.50      ( r1_tarski(X0_36,sK3) != iProver_top
% 7.86/1.50      | r1_xboole_0(k4_xboole_0(X0_36,k4_xboole_0(X0_36,sK2)),sK1) = iProver_top ),
% 7.86/1.50      inference(superposition,[status(thm)],[c_555,c_22418]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_31094,plain,
% 7.86/1.50      ( r1_tarski(sK1,sK3) != iProver_top
% 7.86/1.50      | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) = iProver_top ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_30946]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2,plain,
% 7.86/1.50      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 7.86/1.50      | ~ r1_xboole_0(X1,X2) ),
% 7.86/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_101,plain,
% 7.86/1.50      ( ~ r2_hidden(X0_37,k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)))
% 7.86/1.50      | ~ r1_xboole_0(X0_36,X1_36) ),
% 7.86/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_22903,plain,
% 7.86/1.50      ( ~ r2_hidden(sK0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36)))
% 7.86/1.50      | ~ r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_101]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_22904,plain,
% 7.86/1.50      ( r2_hidden(sK0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36))) != iProver_top
% 7.86/1.50      | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36) != iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_22903]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_22906,plain,
% 7.86/1.50      ( r2_hidden(sK0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))) != iProver_top
% 7.86/1.50      | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) != iProver_top ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_22904]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_8416,plain,
% 7.86/1.50      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_97]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2433,plain,
% 7.86/1.50      ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36)
% 7.86/1.50      | k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_98]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2439,plain,
% 7.86/1.50      ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
% 7.86/1.50      | k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_2433]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_110,plain,
% 7.86/1.50      ( ~ r2_hidden(X0_37,X0_36)
% 7.86/1.50      | r2_hidden(X1_37,X1_36)
% 7.86/1.50      | X1_37 != X0_37
% 7.86/1.50      | X1_36 != X0_36 ),
% 7.86/1.50      theory(equality) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_497,plain,
% 7.86/1.50      ( r2_hidden(X0_37,X0_36)
% 7.86/1.50      | ~ r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 7.86/1.50      | X0_37 != sK0(sK1,sK2)
% 7.86/1.50      | X0_36 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_110]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_641,plain,
% 7.86/1.50      ( r2_hidden(sK0(sK1,sK2),X0_36)
% 7.86/1.50      | ~ r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 7.86/1.50      | sK0(sK1,sK2) != sK0(sK1,sK2)
% 7.86/1.50      | X0_36 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_497]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1232,plain,
% 7.86/1.50      ( r2_hidden(sK0(sK1,sK2),k4_xboole_0(X0_36,X1_36))
% 7.86/1.50      | ~ r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 7.86/1.50      | sK0(sK1,sK2) != sK0(sK1,sK2)
% 7.86/1.50      | k4_xboole_0(X0_36,X1_36) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_641]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2432,plain,
% 7.86/1.50      ( r2_hidden(sK0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36)))
% 7.86/1.50      | ~ r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 7.86/1.50      | sK0(sK1,sK2) != sK0(sK1,sK2)
% 7.86/1.50      | k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_1232]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2434,plain,
% 7.86/1.50      ( sK0(sK1,sK2) != sK0(sK1,sK2)
% 7.86/1.50      | k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 7.86/1.50      | r2_hidden(sK0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0_36))) = iProver_top
% 7.86/1.50      | r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_2432]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2436,plain,
% 7.86/1.50      ( sK0(sK1,sK2) != sK0(sK1,sK2)
% 7.86/1.50      | k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 7.86/1.50      | r2_hidden(sK0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))) = iProver_top
% 7.86/1.50      | r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_2434]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_106,plain,( X0_37 = X0_37 ),theory(equality) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_642,plain,
% 7.86/1.50      ( sK0(sK1,sK2) = sK0(sK1,sK2) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_106]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_3,plain,
% 7.86/1.50      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 7.86/1.50      | r1_xboole_0(X0,X1) ),
% 7.86/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_100,plain,
% 7.86/1.50      ( r2_hidden(sK0(X0_36,X1_36),k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)))
% 7.86/1.50      | r1_xboole_0(X0_36,X1_36) ),
% 7.86/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_395,plain,
% 7.86/1.50      ( r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 7.86/1.50      | r1_xboole_0(sK1,sK2) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_100]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_396,plain,
% 7.86/1.50      ( r2_hidden(sK0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top
% 7.86/1.50      | r1_xboole_0(sK1,sK2) = iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_395]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_9,negated_conjecture,
% 7.86/1.50      ( r1_tarski(sK1,sK3) ),
% 7.86/1.50      inference(cnf_transformation,[],[f34]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_12,plain,
% 7.86/1.50      ( r1_tarski(sK1,sK3) = iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_10,negated_conjecture,
% 7.86/1.50      ( ~ r1_xboole_0(sK1,sK2) ),
% 7.86/1.50      inference(cnf_transformation,[],[f33]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_11,plain,
% 7.86/1.50      ( r1_xboole_0(sK1,sK2) != iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(contradiction,plain,
% 7.86/1.50      ( $false ),
% 7.86/1.50      inference(minisat,
% 7.86/1.50                [status(thm)],
% 7.86/1.50                [c_31094,c_22906,c_8416,c_2439,c_2436,c_642,c_396,c_12,
% 7.86/1.50                 c_11]) ).
% 7.86/1.50  
% 7.86/1.50  
% 7.86/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.86/1.50  
% 7.86/1.50  ------                               Statistics
% 7.86/1.50  
% 7.86/1.50  ------ Selected
% 7.86/1.50  
% 7.86/1.50  total_time:                             0.852
% 7.86/1.50  
%------------------------------------------------------------------------------
