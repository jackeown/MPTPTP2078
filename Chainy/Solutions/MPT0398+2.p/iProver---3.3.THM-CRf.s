%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0398+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:38 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    9
%              Number of atoms          :   28 (  30 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f556,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f931,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f556])).

fof(f2164,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f931])).

fof(f560,conjecture,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f561,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f560])).

fof(f936,plain,(
    ? [X0] : ~ r1_setfam_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f561])).

fof(f1274,plain,
    ( ? [X0] : ~ r1_setfam_1(k1_xboole_0,X0)
   => ~ r1_setfam_1(k1_xboole_0,sK100) ),
    introduced(choice_axiom,[])).

fof(f1275,plain,(
    ~ r1_setfam_1(k1_xboole_0,sK100) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK100])],[f936,f1274])).

fof(f2168,plain,(
    ~ r1_setfam_1(k1_xboole_0,sK100) ),
    inference(cnf_transformation,[],[f1275])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1286,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2650,plain,(
    ~ r1_setfam_1(o_0_0_xboole_0,sK100) ),
    inference(definition_unfolding,[],[f2168,f1286])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1412,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f2273,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f1412,f1286])).

cnf(c_871,plain,
    ( r1_setfam_1(X0,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2164])).

cnf(c_875,negated_conjecture,
    ( ~ r1_setfam_1(o_0_0_xboole_0,sK100) ),
    inference(cnf_transformation,[],[f2650])).

cnf(c_9079,plain,
    ( ~ r1_tarski(X0,X1)
    | sK100 != X1
    | o_0_0_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_871,c_875])).

cnf(c_9080,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,sK100) ),
    inference(unflattening,[status(thm)],[c_9079])).

cnf(c_133,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2273])).

cnf(c_9084,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9080,c_133])).

%------------------------------------------------------------------------------
