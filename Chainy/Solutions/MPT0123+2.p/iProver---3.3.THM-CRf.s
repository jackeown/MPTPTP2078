%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0123+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:23 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   16 (  40 expanded)
%              Number of clauses        :    4 (   5 expanded)
%              Number of leaves         :    4 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   17 (  41 expanded)
%              Number of equality atoms :   16 (  40 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f505,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f114])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f501,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f665,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f505,f501,f501,f501])).

fof(f65,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f65])).

fof(f207,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f66])).

fof(f339,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k3_xboole_0(sK13,k3_xboole_0(sK14,sK15)) != k3_xboole_0(k3_xboole_0(sK13,sK14),k3_xboole_0(sK13,sK15)) ),
    introduced(choice_axiom,[])).

fof(f340,plain,(
    k3_xboole_0(sK13,k3_xboole_0(sK14,sK15)) != k3_xboole_0(k3_xboole_0(sK13,sK14),k3_xboole_0(sK13,sK15)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f207,f339])).

fof(f452,plain,(
    k3_xboole_0(sK13,k3_xboole_0(sK14,sK15)) != k3_xboole_0(k3_xboole_0(sK13,sK14),k3_xboole_0(sK13,sK15)) ),
    inference(cnf_transformation,[],[f340])).

fof(f619,plain,(
    k4_xboole_0(sK13,k4_xboole_0(sK13,k4_xboole_0(sK14,k4_xboole_0(sK14,sK15)))) != k4_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k4_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k4_xboole_0(sK13,k4_xboole_0(sK13,sK15)))) ),
    inference(definition_unfolding,[],[f452,f501,f501,f501,f501,f501])).

cnf(c_156,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f665])).

cnf(c_104,negated_conjecture,
    ( k4_xboole_0(sK13,k4_xboole_0(sK13,k4_xboole_0(sK14,k4_xboole_0(sK14,sK15)))) != k4_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k4_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k4_xboole_0(sK13,k4_xboole_0(sK13,sK15)))) ),
    inference(cnf_transformation,[],[f619])).

cnf(c_8105,plain,
    ( k4_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k4_xboole_0(sK13,k4_xboole_0(sK13,k4_xboole_0(sK14,sK15)))) != k4_xboole_0(sK13,k4_xboole_0(sK13,k4_xboole_0(sK14,k4_xboole_0(sK14,sK15)))) ),
    inference(superposition,[status(thm)],[c_156,c_104])).

cnf(c_8507,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_156,c_8105])).

%------------------------------------------------------------------------------
