%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0879+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:19 EST 2020

% Result     : Theorem 0.35s
% Output     : CNFRefutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    9
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2)) ),
    inference(ennf_transformation,[],[f5])).

fof(f7,plain,
    ( ? [X0,X1,X2] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) != k1_tarski(k3_mcart_1(X0,X1,X2))
   => k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f12,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)) != k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f12,f10,f9])).

fof(f3,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_1,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)) != k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_8,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)) != k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_0,plain,
    ( k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_tarski(X0_35),k1_tarski(X1_35)) = k1_tarski(k4_tarski(X0_35,X1_35)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_16,plain,
    ( k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) != k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(demodulation,[status(thm)],[c_8,c_9])).

cnf(c_17,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_16])).


%------------------------------------------------------------------------------
