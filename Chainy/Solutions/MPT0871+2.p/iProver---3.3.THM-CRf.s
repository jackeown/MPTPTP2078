%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0871+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:55 EST 2020

% Result     : Theorem 5.52s
% Output     : CNFRefutation 5.52s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of clauses        :    2 (   2 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    7
%              Number of atoms          :   15 (  15 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1315,conjecture,(
    ! [X0,X1,X2,X3] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1316,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f1315])).

fof(f2664,plain,(
    ? [X0,X1,X2,X3] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) != k4_mcart_1(X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f1316])).

fof(f3675,plain,
    ( ? [X0,X1,X2,X3] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) != k4_mcart_1(X0,X1,X2,X3)
   => k4_tarski(k4_tarski(k4_tarski(sK378,sK379),sK380),sK381) != k4_mcart_1(sK378,sK379,sK380,sK381) ),
    introduced(choice_axiom,[])).

fof(f3676,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK378,sK379),sK380),sK381) != k4_mcart_1(sK378,sK379,sK380,sK381) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK378,sK379,sK380,sK381])],[f2664,f3675])).

fof(f5987,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK378,sK379),sK380),sK381) != k4_mcart_1(sK378,sK379,sK380,sK381) ),
    inference(cnf_transformation,[],[f3676])).

fof(f1275,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5884,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1275])).

fof(f1274,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5883,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1274])).

fof(f6013,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f5884,f5883])).

fof(f6722,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK378,sK379),sK380),sK381) != k4_tarski(k4_tarski(k4_tarski(sK378,sK379),sK380),sK381) ),
    inference(definition_unfolding,[],[f5987,f6013])).

cnf(c_2283,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(sK378,sK379),sK380),sK381) != k4_tarski(k4_tarski(k4_tarski(sK378,sK379),sK380),sK381) ),
    inference(cnf_transformation,[],[f6722])).

cnf(c_11367,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2283])).

%------------------------------------------------------------------------------
