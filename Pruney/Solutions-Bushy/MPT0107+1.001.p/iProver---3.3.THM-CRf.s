%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0107+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:29 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  36 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f6])).

fof(f10,plain,(
    ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f7])).

fof(f11,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1)
   => k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f18,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f19,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)) ),
    inference(definition_unfolding,[],[f18,f13])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_4,negated_conjecture,
    ( k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_1,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_35,plain,
    ( X0 != X1
    | k3_xboole_0(X0,X2) != X3
    | k4_xboole_0(X3,X1) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_36,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_35])).

cnf(c_56,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_4,c_2,c_3,c_36])).

cnf(c_57,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_56])).


%------------------------------------------------------------------------------
