%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0905+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:23 EST 2020

% Result     : Theorem 0.65s
% Output     : CNFRefutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   28 (  30 expanded)
%              Number of equality atoms :   27 (  29 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2,X3] : k1_tarski(k4_mcart_1(X0,X1,X2,X3)) = k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k1_tarski(k4_mcart_1(X0,X1,X2,X3)) = k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] : k1_tarski(k4_mcart_1(X0,X1,X2,X3)) != k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) ),
    inference(ennf_transformation,[],[f7])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] : k1_tarski(k4_mcart_1(X0,X1,X2,X3)) != k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3))
   => k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f16,plain,(
    k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f12,f11])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f19,plain,(
    k1_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) != k3_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(definition_unfolding,[],[f16,f17,f15])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_tarski(k3_mcart_1(X0,X1,X2)) = k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X2,X0,X1] : k1_tarski(k3_mcart_1(X0,X1,X2)) = k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_tarski(k4_tarski(k4_tarski(X0,X1),X2)) = k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f14,f11])).

fof(f3,axiom,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_2,negated_conjecture,
    ( k1_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) != k3_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_11,negated_conjecture,
    ( k1_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) != k3_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1,plain,
    ( k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(k4_tarski(X0,X1),X2)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_12,plain,
    ( k3_zfmisc_1(k1_tarski(X0_37),k1_tarski(X1_37),k1_tarski(X2_37)) = k1_tarski(k4_tarski(k4_tarski(X0_37,X1_37),X2_37)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_0,plain,
    ( k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_13,plain,
    ( k2_zfmisc_1(k1_tarski(X0_37),k1_tarski(X1_37)) = k1_tarski(k4_tarski(X0_37,X1_37)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_23,plain,
    ( k1_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) != k1_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) ),
    inference(demodulation,[status(thm)],[c_11,c_12,c_13])).

cnf(c_24,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_23])).


%------------------------------------------------------------------------------
