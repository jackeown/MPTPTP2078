%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0053+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:21 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f6,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) != k1_xboole_0
   => k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).

fof(f12,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

cnf(c_1,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_30,plain,
    ( X0 != X1
    | k2_xboole_0(X0,X2) != X3
    | k4_xboole_0(X1,X3) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_31,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_30])).

cnf(c_2,negated_conjecture,
    ( k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

cnf(c_37,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_31,c_2])).


%------------------------------------------------------------------------------
