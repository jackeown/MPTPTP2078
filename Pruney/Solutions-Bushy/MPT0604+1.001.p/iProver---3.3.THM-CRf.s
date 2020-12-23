%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0604+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:42 EST 2020

% Result     : Theorem 0.56s
% Output     : CNFRefutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   16 (  20 expanded)
%              Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   17 (  21 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] : k3_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X1))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f8,f9])).

fof(f3,conjecture,(
    ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0] : k1_tarski(X0) != k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    inference(ennf_transformation,[],[f4])).

fof(f6,plain,
    ( ? [X0] : k1_tarski(X0) != k3_relat_1(k1_tarski(k4_tarski(X0,X0)))
   => k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0))) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).

fof(f10,plain,(
    k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,plain,(
    k3_relat_1(k2_tarski(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))) != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f10,f9,f9])).

cnf(c_0,plain,
    ( k3_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_2,plain,
    ( k3_relat_1(k2_tarski(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))) = k2_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1,negated_conjecture,
    ( k3_relat_1(k2_tarski(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))) != k2_tarski(sK0,sK0) ),
    inference(cnf_transformation,[],[f12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2,c_1])).


%------------------------------------------------------------------------------
