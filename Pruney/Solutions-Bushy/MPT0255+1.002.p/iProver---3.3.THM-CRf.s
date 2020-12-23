%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0255+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:50 EST 2020

% Result     : Theorem 0.49s
% Output     : CNFRefutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :   10
%              Number of atoms          :   42 (  42 expanded)
%              Number of equality atoms :   24 (  24 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    inference(negated_conjecture,[],[f6])).

fof(f9,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ),
    inference(ennf_transformation,[],[f7])).

fof(f10,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
   => k2_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f17,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f18,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),sK2) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f17,f13])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_4,negated_conjecture,
    ( k2_xboole_0(k2_tarski(sK0,sK1),sK2) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_41,negated_conjecture,
    ( k2_xboole_0(k2_tarski(sK0,sK1),sK2) = o_0_0_xboole_0 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_45,plain,
    ( k2_xboole_0(X0_35,X1_35) = k2_xboole_0(X1_35,X0_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_236,plain,
    ( k2_xboole_0(sK2,k2_tarski(sK0,sK1)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_41,c_45])).

cnf(c_3,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_42,plain,
    ( v1_xboole_0(X0_35)
    | ~ v1_xboole_0(k2_xboole_0(X1_35,X0_35)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_117,plain,
    ( v1_xboole_0(X0_35) = iProver_top
    | v1_xboole_0(k2_xboole_0(X1_35,X0_35)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_290,plain,
    ( v1_xboole_0(k2_tarski(sK0,sK1)) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_236,c_117])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_43,plain,
    ( ~ v1_xboole_0(k2_tarski(X0_36,X0_37)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_57,plain,
    ( v1_xboole_0(k2_tarski(X0_36,X0_37)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_59,plain,
    ( v1_xboole_0(k2_tarski(sK0,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_1,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_11,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_290,c_59,c_11])).


%------------------------------------------------------------------------------
