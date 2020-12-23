%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0880+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:56 EST 2020

% Result     : Theorem 39.31s
% Output     : CNFRefutation 39.31s
% Verified   : 
% Statistics : Number of formulae       :   34 (  93 expanded)
%              Number of clauses        :    8 (  14 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   36 (  96 expanded)
%              Number of equality atoms :   35 (  95 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f394,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4273,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f394])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4020,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3924,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3864,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f6046,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f3924,f3864])).

fof(f6047,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f4020,f6046])).

fof(f6393,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(k4_tarski(X0,X2)),k1_tarski(k4_tarski(X1,X2))),k4_xboole_0(k1_tarski(k4_tarski(X0,X2)),k4_xboole_0(k1_tarski(k4_tarski(X0,X2)),k1_tarski(k4_tarski(X1,X2))))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f4273,f6047,f6047])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3921,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3713,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f1327,conjecture,(
    ! [X0,X1,X2,X3] : k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1328,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) ),
    inference(negated_conjecture,[],[f1327])).

fof(f2684,plain,(
    ? [X0,X1,X2,X3] : k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) ),
    inference(ennf_transformation,[],[f1328])).

fof(f3699,plain,
    ( ? [X0,X1,X2,X3] : k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3))
   => k2_tarski(k3_mcart_1(sK380,sK382,sK383),k3_mcart_1(sK381,sK382,sK383)) != k3_zfmisc_1(k2_tarski(sK380,sK381),k1_tarski(sK382),k1_tarski(sK383)) ),
    introduced(choice_axiom,[])).

fof(f3700,plain,(
    k2_tarski(k3_mcart_1(sK380,sK382,sK383),k3_mcart_1(sK381,sK382,sK383)) != k3_zfmisc_1(k2_tarski(sK380,sK381),k1_tarski(sK382),k1_tarski(sK383)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK380,sK381,sK382,sK383])],[f2684,f3699])).

fof(f6033,plain,(
    k2_tarski(k3_mcart_1(sK380,sK382,sK383),k3_mcart_1(sK381,sK382,sK383)) != k3_zfmisc_1(k2_tarski(sK380,sK381),k1_tarski(sK382),k1_tarski(sK383)) ),
    inference(cnf_transformation,[],[f3700])).

fof(f1274,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5905,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1274])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5906,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f6789,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK380,sK382),sK383)),k1_tarski(k4_tarski(k4_tarski(sK381,sK382),sK383))),k4_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK380,sK382),sK383)),k4_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK380,sK382),sK383)),k1_tarski(k4_tarski(k4_tarski(sK381,sK382),sK383))))) != k2_zfmisc_1(k2_zfmisc_1(k5_xboole_0(k5_xboole_0(k1_tarski(sK380),k1_tarski(sK381)),k4_xboole_0(k1_tarski(sK380),k4_xboole_0(k1_tarski(sK380),k1_tarski(sK381)))),k1_tarski(sK382)),k1_tarski(sK383)) ),
    inference(definition_unfolding,[],[f6033,f6047,f5905,f5905,f5906,f6047])).

cnf(c_551,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X1))),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X1))))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f6393])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3921])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3713])).

cnf(c_69802,plain,
    ( k5_xboole_0(k1_tarski(k4_tarski(X0,X1)),k5_xboole_0(k1_tarski(k4_tarski(X2,X1)),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k4_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X1)))))) = k2_zfmisc_1(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2))))),k1_tarski(X1)) ),
    inference(theory_normalisation,[status(thm)],[c_551,c_211,c_7])).

cnf(c_2306,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK380,sK382),sK383)),k1_tarski(k4_tarski(k4_tarski(sK381,sK382),sK383))),k4_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK380,sK382),sK383)),k4_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK380,sK382),sK383)),k1_tarski(k4_tarski(k4_tarski(sK381,sK382),sK383))))) != k2_zfmisc_1(k2_zfmisc_1(k5_xboole_0(k5_xboole_0(k1_tarski(sK380),k1_tarski(sK381)),k4_xboole_0(k1_tarski(sK380),k4_xboole_0(k1_tarski(sK380),k1_tarski(sK381)))),k1_tarski(sK382)),k1_tarski(sK383)) ),
    inference(cnf_transformation,[],[f6789])).

cnf(c_69688,negated_conjecture,
    ( k5_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK380,sK382),sK383)),k5_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK381,sK382),sK383)),k4_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK380,sK382),sK383)),k4_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK380,sK382),sK383)),k1_tarski(k4_tarski(k4_tarski(sK381,sK382),sK383)))))) != k2_zfmisc_1(k2_zfmisc_1(k5_xboole_0(k1_tarski(sK380),k5_xboole_0(k1_tarski(sK381),k4_xboole_0(k1_tarski(sK380),k4_xboole_0(k1_tarski(sK380),k1_tarski(sK381))))),k1_tarski(sK382)),k1_tarski(sK383)) ),
    inference(theory_normalisation,[status(thm)],[c_2306,c_211,c_7])).

cnf(c_122082,plain,
    ( k2_zfmisc_1(k5_xboole_0(k1_tarski(k4_tarski(sK380,sK382)),k5_xboole_0(k1_tarski(k4_tarski(sK381,sK382)),k4_xboole_0(k1_tarski(k4_tarski(sK380,sK382)),k4_xboole_0(k1_tarski(k4_tarski(sK380,sK382)),k1_tarski(k4_tarski(sK381,sK382)))))),k1_tarski(sK383)) != k2_zfmisc_1(k2_zfmisc_1(k5_xboole_0(k1_tarski(sK380),k5_xboole_0(k1_tarski(sK381),k4_xboole_0(k1_tarski(sK380),k4_xboole_0(k1_tarski(sK380),k1_tarski(sK381))))),k1_tarski(sK382)),k1_tarski(sK383)) ),
    inference(superposition,[status(thm)],[c_69802,c_69688])).

cnf(c_122789,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_69802,c_122082])).

%------------------------------------------------------------------------------
