%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0872+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:55 EST 2020

% Result     : Theorem 5.32s
% Output     : CNFRefutation 5.32s
% Verified   : 
% Statistics : Number of formulae       :   14 (  16 expanded)
%              Number of clauses        :    2 (   2 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    7
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1316,conjecture,(
    ! [X0,X1,X2,X3] : k3_mcart_1(k4_tarski(X0,X1),X2,X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1317,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k3_mcart_1(k4_tarski(X0,X1),X2,X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f1316])).

fof(f2665,plain,(
    ? [X0,X1,X2,X3] : k3_mcart_1(k4_tarski(X0,X1),X2,X3) != k4_mcart_1(X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f1317])).

fof(f3676,plain,
    ( ? [X0,X1,X2,X3] : k3_mcart_1(k4_tarski(X0,X1),X2,X3) != k4_mcart_1(X0,X1,X2,X3)
   => k3_mcart_1(k4_tarski(sK378,sK379),sK380,sK381) != k4_mcart_1(sK378,sK379,sK380,sK381) ),
    introduced(choice_axiom,[])).

fof(f3677,plain,(
    k3_mcart_1(k4_tarski(sK378,sK379),sK380,sK381) != k4_mcart_1(sK378,sK379,sK380,sK381) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK378,sK379,sK380,sK381])],[f2665,f3676])).

fof(f5989,plain,(
    k3_mcart_1(k4_tarski(sK378,sK379),sK380,sK381) != k4_mcart_1(sK378,sK379,sK380,sK381) ),
    inference(cnf_transformation,[],[f3677])).

fof(f1275,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5885,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1275])).

fof(f1274,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5884,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1274])).

fof(f6015,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f5885,f5884])).

fof(f6725,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK378,sK379),sK380),sK381) != k4_tarski(k4_tarski(k4_tarski(sK378,sK379),sK380),sK381) ),
    inference(definition_unfolding,[],[f5989,f5884,f6015])).

cnf(c_2284,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(sK378,sK379),sK380),sK381) != k4_tarski(k4_tarski(k4_tarski(sK378,sK379),sK380),sK381) ),
    inference(cnf_transformation,[],[f6725])).

cnf(c_11369,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2284])).

%------------------------------------------------------------------------------
