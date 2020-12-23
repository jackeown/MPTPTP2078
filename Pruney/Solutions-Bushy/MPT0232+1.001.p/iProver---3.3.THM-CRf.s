%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0232+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:47 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   30 (  78 expanded)
%              Number of clauses        :   13 (  22 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :   12
%              Number of atoms          :   44 ( 125 expanded)
%              Number of equality atoms :   29 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k1_tarski(X2)
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
      & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
    & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f13,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f17,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)) ),
    inference(definition_unfolding,[],[f13,f12])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)) ) ),
    inference(definition_unfolding,[],[f11,f12])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,plain,(
    k2_tarski(sK0,sK1) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,(
    k2_tarski(sK0,sK1) != k2_tarski(sK2,sK2) ),
    inference(definition_unfolding,[],[f14,f12])).

cnf(c_3,negated_conjecture,
    ( r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_94,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_95,plain,
    ( X0 = X1
    | r1_tarski(k2_tarski(X1,X2),k2_tarski(X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_194,plain,
    ( sK2 = sK0 ),
    inference(superposition,[status(thm)],[c_94,c_95])).

cnf(c_268,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_194,c_94])).

cnf(c_0,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_195,plain,
    ( X0 = X1
    | r1_tarski(k2_tarski(X2,X1),k2_tarski(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_95])).

cnf(c_334,plain,
    ( sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_268,c_195])).

cnf(c_2,negated_conjecture,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK2,sK2) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_269,plain,
    ( k2_tarski(sK0,sK0) != k2_tarski(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_194,c_2])).

cnf(c_396,plain,
    ( k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_334,c_269])).

cnf(c_397,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_396])).


%------------------------------------------------------------------------------
