%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0905+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:57 EST 2020

% Result     : Theorem 22.90s
% Output     : CNFRefutation 22.90s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1372,conjecture,(
    ! [X0,X1,X2,X3] : k1_tarski(k4_mcart_1(X0,X1,X2,X3)) = k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1373,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k1_tarski(k4_mcart_1(X0,X1,X2,X3)) = k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) ),
    inference(negated_conjecture,[],[f1372])).

fof(f2764,plain,(
    ? [X0,X1,X2,X3] : k1_tarski(k4_mcart_1(X0,X1,X2,X3)) != k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) ),
    inference(ennf_transformation,[],[f1373])).

fof(f3818,plain,
    ( ? [X0,X1,X2,X3] : k1_tarski(k4_mcart_1(X0,X1,X2,X3)) != k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3))
   => k1_tarski(k4_mcart_1(sK414,sK415,sK416,sK417)) != k4_zfmisc_1(k1_tarski(sK414),k1_tarski(sK415),k1_tarski(sK416),k1_tarski(sK417)) ),
    introduced(choice_axiom,[])).

fof(f3819,plain,(
    k1_tarski(k4_mcart_1(sK414,sK415,sK416,sK417)) != k4_zfmisc_1(k1_tarski(sK414),k1_tarski(sK415),k1_tarski(sK416),k1_tarski(sK417)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK414,sK415,sK416,sK417])],[f2764,f3818])).

fof(f6250,plain,(
    k1_tarski(k4_mcart_1(sK414,sK415,sK416,sK417)) != k4_zfmisc_1(k1_tarski(sK414),k1_tarski(sK415),k1_tarski(sK416),k1_tarski(sK417)) ),
    inference(cnf_transformation,[],[f3819])).

fof(f1278,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6028,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1278])).

fof(f1276,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6026,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1276])).

fof(f6270,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f6028,f6026])).

fof(f1279,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6029,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1279])).

fof(f1277,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6027,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1277])).

fof(f6269,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f6029,f6027])).

fof(f7104,plain,(
    k1_tarski(k4_tarski(k4_tarski(k4_tarski(sK414,sK415),sK416),sK417)) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK414),k1_tarski(sK415)),k1_tarski(sK416)),k1_tarski(sK417)) ),
    inference(definition_unfolding,[],[f6250,f6270,f6269])).

fof(f393,axiom,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4386,plain,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f393])).

cnf(c_2407,negated_conjecture,
    ( k1_tarski(k4_tarski(k4_tarski(k4_tarski(sK414,sK415),sK416),sK417)) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK414),k1_tarski(sK415)),k1_tarski(sK416)),k1_tarski(sK417)) ),
    inference(cnf_transformation,[],[f7104])).

cnf(c_550,plain,
    ( k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4386])).

cnf(c_74074,plain,
    ( k1_tarski(k4_tarski(k4_tarski(k4_tarski(sK414,sK415),sK416),sK417)) != k1_tarski(k4_tarski(k4_tarski(k4_tarski(sK414,sK415),sK416),sK417)) ),
    inference(demodulation,[status(thm)],[c_2407,c_550])).

cnf(c_74075,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_74074])).

%------------------------------------------------------------------------------
