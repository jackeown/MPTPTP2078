%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0058+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:16 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f320,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f72])).

fof(f83,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f153,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f83])).

fof(f332,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f153])).

fof(f91,conjecture,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f92,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(negated_conjecture,[],[f91])).

fof(f154,plain,(
    ? [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) != X0 ),
    inference(ennf_transformation,[],[f92])).

fof(f212,plain,
    ( ? [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) != X0
   => k2_xboole_0(k3_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK16)) != sK15 ),
    introduced(choice_axiom,[])).

fof(f213,plain,(
    k2_xboole_0(k3_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK16)) != sK15 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f154,f212])).

fof(f340,plain,(
    k2_xboole_0(k3_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK16)) != sK15 ),
    inference(cnf_transformation,[],[f213])).

fof(f86,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f335,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f408,plain,(
    k2_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),k4_xboole_0(sK15,sK16)) != sK15 ),
    inference(definition_unfolding,[],[f340,f335])).

fof(f89,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f338,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f89])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f216,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_104,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f320])).

cnf(c_5099,plain,
    ( r1_tarski(k4_xboole_0(sK15,sK16),sK15) ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(c_116,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(cnf_transformation,[],[f332])).

cnf(c_4706,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,sK16),sK15)
    | k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))) = sK15 ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_123,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),k4_xboole_0(sK15,sK16)) != sK15 ),
    inference(cnf_transformation,[],[f408])).

cnf(c_121,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f338])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f216])).

cnf(c_2051,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))) != sK15 ),
    inference(theory_normalisation,[status(thm)],[c_123,c_121,c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5099,c_4706,c_2051])).

%------------------------------------------------------------------------------
