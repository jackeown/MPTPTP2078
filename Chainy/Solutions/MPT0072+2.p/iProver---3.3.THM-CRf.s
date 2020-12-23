%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0072+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:18 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   24 (  32 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  41 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f344,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

fof(f87,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f367,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f250,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f440,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f344,f367,f250,f250])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f211,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f274,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f211])).

fof(f403,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f274,f367,f250])).

fof(f107,conjecture,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f108,negated_conjecture,(
    ~ ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f107])).

fof(f181,plain,(
    ? [X0] : ~ r1_xboole_0(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f108])).

fof(f241,plain,
    ( ? [X0] : ~ r1_xboole_0(X0,k1_xboole_0)
   => ~ r1_xboole_0(sK15,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f242,plain,(
    ~ r1_xboole_0(sK15,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f181,f241])).

fof(f387,plain,(
    ~ r1_xboole_0(sK15,k1_xboole_0) ),
    inference(cnf_transformation,[],[f242])).

fof(f461,plain,(
    ~ r1_xboole_0(sK15,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f387,f250])).

cnf(c_99,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f440])).

cnf(c_5566,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK15,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_99])).

cnf(c_28,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f403])).

cnf(c_5145,plain,
    ( r1_xboole_0(sK15,o_0_0_xboole_0)
    | k4_xboole_0(sK15,k4_xboole_0(sK15,o_0_0_xboole_0)) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_141,negated_conjecture,
    ( ~ r1_xboole_0(sK15,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f461])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5566,c_5145,c_141])).

%------------------------------------------------------------------------------
