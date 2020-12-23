%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0882+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:19 EST 2020

% Result     : Theorem 0.49s
% Output     : CNFRefutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   23 (  25 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    6 (   7 expanded)
%              Depth                    :    9
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :   24 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3)) ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) != k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3)) ),
    inference(ennf_transformation,[],[f6])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) != k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3))
   => k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK2,sK3)) != k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK3)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK2,sK3)) != k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f15,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK2,sK3)) != k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK2,sK3)) != k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK3)) ),
    inference(definition_unfolding,[],[f15,f11,f10,f10])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_3,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK2,sK3)) != k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK3)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_13,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK2,sK3)) != k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK3)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2,plain,
    ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_14,plain,
    ( k2_tarski(k4_tarski(X0_37,X1_37),k4_tarski(X0_37,X2_37)) = k2_zfmisc_1(k1_tarski(X0_37),k2_tarski(X1_37,X2_37)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_0,plain,
    ( k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_16,plain,
    ( k2_zfmisc_1(k1_tarski(X0_37),k1_tarski(X1_37)) = k1_tarski(k4_tarski(X0_37,X1_37)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_25,plain,
    ( k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k2_tarski(sK2,sK3)) != k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k2_tarski(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_13,c_14,c_16])).

cnf(c_26,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_25])).


%------------------------------------------------------------------------------
