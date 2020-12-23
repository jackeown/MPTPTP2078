%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0097+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:20 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    9
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f139,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(negated_conjecture,[],[f138])).

fof(f238,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(ennf_transformation,[],[f139])).

fof(f294,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)
   => ~ r1_xboole_0(k4_xboole_0(sK15,k3_xboole_0(sK15,sK16)),sK16) ),
    introduced(choice_axiom,[])).

fof(f295,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK15,k3_xboole_0(sK15,sK16)),sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f238,f294])).

fof(f475,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK15,k3_xboole_0(sK15,sK16)),sK16) ),
    inference(cnf_transformation,[],[f295])).

fof(f87,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f420,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

fof(f554,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK16) ),
    inference(definition_unfolding,[],[f475,f420])).

fof(f86,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f419,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f532,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f419,f420])).

fof(f123,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f459,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_176,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK16) ),
    inference(cnf_transformation,[],[f554])).

cnf(c_5358,plain,
    ( r1_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK16) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_176])).

cnf(c_121,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f532])).

cnf(c_5580,plain,
    ( r1_xboole_0(k4_xboole_0(sK15,sK16),sK16) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5358,c_121])).

cnf(c_160,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f459])).

cnf(c_5373,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_160])).

cnf(c_5582,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5580,c_5373])).

%------------------------------------------------------------------------------
