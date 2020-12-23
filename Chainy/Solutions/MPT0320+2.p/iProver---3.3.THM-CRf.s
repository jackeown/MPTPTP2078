%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0320+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:35 EST 2020

% Result     : Theorem 8.01s
% Output     : CNFRefutation 8.01s
% Verified   : 
% Statistics : Number of formulae       :   33 (  84 expanded)
%              Number of clauses        :    9 (  13 expanded)
%              Number of leaves         :    8 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  97 expanded)
%              Number of equality atoms :   44 (  96 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f343,conjecture,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) = k2_zfmisc_1(X2,k2_tarski(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) = k2_zfmisc_1(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f344,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) = k2_zfmisc_1(X2,k2_tarski(X0,X1))
        & k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) = k2_zfmisc_1(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f343])).

fof(f578,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) != k2_zfmisc_1(X2,k2_tarski(X0,X1))
      | k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) != k2_zfmisc_1(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f344])).

fof(f780,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) != k2_zfmisc_1(X2,k2_tarski(X0,X1))
        | k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) != k2_zfmisc_1(k2_tarski(X0,X1),X2) )
   => ( k2_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k2_zfmisc_1(sK52,k1_tarski(sK51))) != k2_zfmisc_1(sK52,k2_tarski(sK50,sK51))
      | k2_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k2_zfmisc_1(k1_tarski(sK51),sK52)) != k2_zfmisc_1(k2_tarski(sK50,sK51),sK52) ) ),
    introduced(choice_axiom,[])).

fof(f781,plain,
    ( k2_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k2_zfmisc_1(sK52,k1_tarski(sK51))) != k2_zfmisc_1(sK52,k2_tarski(sK50,sK51))
    | k2_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k2_zfmisc_1(k1_tarski(sK51),sK52)) != k2_zfmisc_1(k2_tarski(sK50,sK51),sK52) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK50,sK51,sK52])],[f578,f780])).

fof(f1299,plain,
    ( k2_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k2_zfmisc_1(sK52,k1_tarski(sK51))) != k2_zfmisc_1(sK52,k2_tarski(sK50,sK51))
    | k2_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k2_zfmisc_1(k1_tarski(sK51),sK52)) != k2_zfmisc_1(k2_tarski(sK50,sK51),sK52) ),
    inference(cnf_transformation,[],[f781])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1124,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1028,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f968,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1422,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1028,f968])).

fof(f1423,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f1124,f1422])).

fof(f1721,plain,
    ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k2_zfmisc_1(sK52,k1_tarski(sK51))),k4_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k4_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k2_zfmisc_1(sK52,k1_tarski(sK51))))) != k2_zfmisc_1(sK52,k5_xboole_0(k5_xboole_0(k1_tarski(sK50),k1_tarski(sK51)),k4_xboole_0(k1_tarski(sK50),k4_xboole_0(k1_tarski(sK50),k1_tarski(sK51)))))
    | k5_xboole_0(k5_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k2_zfmisc_1(k1_tarski(sK51),sK52)),k4_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k4_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k2_zfmisc_1(k1_tarski(sK51),sK52)))) != k2_zfmisc_1(k5_xboole_0(k5_xboole_0(k1_tarski(sK50),k1_tarski(sK51)),k4_xboole_0(k1_tarski(sK50),k4_xboole_0(k1_tarski(sK50),k1_tarski(sK51)))),sK52) ),
    inference(definition_unfolding,[],[f1299,f1422,f1423,f1422,f1423])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1025,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f817,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f330,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1277,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f330])).

fof(f1710,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)),k4_xboole_0(k2_zfmisc_1(X2,X0),k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(X2,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f1277,f1422,f1422])).

fof(f1276,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f330])).

fof(f1711,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)),k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2) ),
    inference(definition_unfolding,[],[f1276,f1422,f1422])).

cnf(c_474,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k2_zfmisc_1(k1_tarski(sK51),sK52)),k4_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k4_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k2_zfmisc_1(k1_tarski(sK51),sK52)))) != k2_zfmisc_1(k5_xboole_0(k5_xboole_0(k1_tarski(sK50),k1_tarski(sK51)),k4_xboole_0(k1_tarski(sK50),k4_xboole_0(k1_tarski(sK50),k1_tarski(sK51)))),sK52)
    | k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k2_zfmisc_1(sK52,k1_tarski(sK51))),k4_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k4_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k2_zfmisc_1(sK52,k1_tarski(sK51))))) != k2_zfmisc_1(sK52,k5_xboole_0(k5_xboole_0(k1_tarski(sK50),k1_tarski(sK51)),k4_xboole_0(k1_tarski(sK50),k4_xboole_0(k1_tarski(sK50),k1_tarski(sK51))))) ),
    inference(cnf_transformation,[],[f1721])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1025])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f817])).

cnf(c_10020,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k5_xboole_0(k2_zfmisc_1(k1_tarski(sK51),sK52),k4_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k4_xboole_0(k2_zfmisc_1(k1_tarski(sK50),sK52),k2_zfmisc_1(k1_tarski(sK51),sK52))))) != k2_zfmisc_1(k5_xboole_0(k1_tarski(sK50),k5_xboole_0(k1_tarski(sK51),k4_xboole_0(k1_tarski(sK50),k4_xboole_0(k1_tarski(sK50),k1_tarski(sK51))))),sK52)
    | k5_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k5_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK51)),k4_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k4_xboole_0(k2_zfmisc_1(sK52,k1_tarski(sK50)),k2_zfmisc_1(sK52,k1_tarski(sK51)))))) != k2_zfmisc_1(sK52,k5_xboole_0(k1_tarski(sK50),k5_xboole_0(k1_tarski(sK51),k4_xboole_0(k1_tarski(sK50),k4_xboole_0(k1_tarski(sK50),k1_tarski(sK51)))))) ),
    inference(theory_normalisation,[status(thm)],[c_474,c_211,c_7])).

cnf(c_451,plain,
    ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)),k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)))) = k2_zfmisc_1(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f1710])).

cnf(c_10024,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k5_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(theory_normalisation,[status(thm)],[c_451,c_211,c_7])).

cnf(c_452,plain,
    ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)),k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(X0,k4_xboole_0(X0,X2))),X1) ),
    inference(cnf_transformation,[],[f1711])).

cnf(c_10023,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k5_xboole_0(k2_zfmisc_1(X2,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2)))),X1) ),
    inference(theory_normalisation,[status(thm)],[c_452,c_211,c_7])).

cnf(c_18203,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10020,c_10024,c_10023])).

%------------------------------------------------------------------------------
