%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0879+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:56 EST 2020

% Result     : Theorem 19.78s
% Output     : CNFRefutation 19.78s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    8
%              Number of atoms          :   18 (  18 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1325,conjecture,(
    ! [X0,X1,X2] : k1_tarski(k3_mcart_1(X0,X1,X2)) = k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1326,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_tarski(k3_mcart_1(X0,X1,X2)) = k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) ),
    inference(negated_conjecture,[],[f1325])).

fof(f2681,plain,(
    ? [X0,X1,X2] : k1_tarski(k3_mcart_1(X0,X1,X2)) != k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) ),
    inference(ennf_transformation,[],[f1326])).

fof(f3696,plain,
    ( ? [X0,X1,X2] : k1_tarski(k3_mcart_1(X0,X1,X2)) != k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2))
   => k1_tarski(k3_mcart_1(sK379,sK380,sK381)) != k3_zfmisc_1(k1_tarski(sK379),k1_tarski(sK380),k1_tarski(sK381)) ),
    introduced(choice_axiom,[])).

fof(f3697,plain,(
    k1_tarski(k3_mcart_1(sK379,sK380,sK381)) != k3_zfmisc_1(k1_tarski(sK379),k1_tarski(sK380),k1_tarski(sK381)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK379,sK380,sK381])],[f2681,f3696])).

fof(f6029,plain,(
    k1_tarski(k3_mcart_1(sK379,sK380,sK381)) != k3_zfmisc_1(k1_tarski(sK379),k1_tarski(sK380),k1_tarski(sK381)) ),
    inference(cnf_transformation,[],[f3697])).

fof(f1274,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5904,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1274])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5905,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f6784,plain,(
    k1_tarski(k4_tarski(k4_tarski(sK379,sK380),sK381)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK379),k1_tarski(sK380)),k1_tarski(sK381)) ),
    inference(definition_unfolding,[],[f6029,f5904,f5905])).

fof(f393,axiom,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4270,plain,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f393])).

cnf(c_2303,negated_conjecture,
    ( k1_tarski(k4_tarski(k4_tarski(sK379,sK380),sK381)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK379),k1_tarski(sK380)),k1_tarski(sK381)) ),
    inference(cnf_transformation,[],[f6784])).

cnf(c_550,plain,
    ( k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4270])).

cnf(c_69429,plain,
    ( k1_tarski(k4_tarski(k4_tarski(sK379,sK380),sK381)) != k1_tarski(k4_tarski(k4_tarski(sK379,sK380),sK381)) ),
    inference(demodulation,[status(thm)],[c_2303,c_550])).

cnf(c_69430,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_69429])).

%------------------------------------------------------------------------------
