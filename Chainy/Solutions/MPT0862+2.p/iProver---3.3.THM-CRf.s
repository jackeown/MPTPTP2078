%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0862+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:55 EST 2020

% Result     : Theorem 27.44s
% Output     : CNFRefutation 27.44s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 122 expanded)
%              Number of clauses        :   20 (  31 expanded)
%              Number of leaves         :   11 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 228 expanded)
%              Number of equality atoms :   78 ( 181 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1300,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1301,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f1300])).

fof(f2640,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f1301])).

fof(f3647,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ( k2_mcart_1(X0) != X3
            & k2_mcart_1(X0) != X2 )
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) )
   => ( ( ( k2_mcart_1(sK375) != sK378
          & k2_mcart_1(sK375) != sK377 )
        | k1_mcart_1(sK375) != sK376 )
      & r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),k2_tarski(sK377,sK378))) ) ),
    introduced(choice_axiom,[])).

fof(f3648,plain,
    ( ( ( k2_mcart_1(sK375) != sK378
        & k2_mcart_1(sK375) != sK377 )
      | k1_mcart_1(sK375) != sK376 )
    & r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),k2_tarski(sK377,sK378))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK375,sK376,sK377,sK378])],[f2640,f3647])).

fof(f5940,plain,(
    r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),k2_tarski(sK377,sK378))) ),
    inference(cnf_transformation,[],[f3648])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3974,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3878,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3818,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f5961,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f3878,f3818])).

fof(f5962,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f3974,f5961])).

fof(f6662,plain,(
    r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),k5_xboole_0(k5_xboole_0(k1_tarski(sK377),k1_tarski(sK378)),k4_xboole_0(k1_tarski(sK377),k4_xboole_0(k1_tarski(sK377),k1_tarski(sK378)))))) ),
    inference(definition_unfolding,[],[f5940,f5962])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3875,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3667,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3745,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f5975,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f3745,f3818])).

fof(f1298,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2638,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f1298])).

fof(f5937,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X0) = X3
      | k2_mcart_1(X0) = X2
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(cnf_transformation,[],[f2638])).

fof(f6658,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X0) = X3
      | k2_mcart_1(X0) = X2
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3)))))) ) ),
    inference(definition_unfolding,[],[f5937,f5962])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3882,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f6108,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f3882,f5961])).

fof(f1294,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2634,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f1294])).

fof(f5928,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f2634])).

fof(f5942,plain,
    ( k2_mcart_1(sK375) != sK378
    | k1_mcart_1(sK375) != sK376 ),
    inference(cnf_transformation,[],[f3648])).

fof(f5941,plain,
    ( k2_mcart_1(sK375) != sK377
    | k1_mcart_1(sK375) != sK376 ),
    inference(cnf_transformation,[],[f3648])).

cnf(c_2264,negated_conjecture,
    ( r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),k5_xboole_0(k5_xboole_0(k1_tarski(sK377),k1_tarski(sK378)),k4_xboole_0(k1_tarski(sK377),k4_xboole_0(k1_tarski(sK377),k1_tarski(sK378)))))) ),
    inference(cnf_transformation,[],[f6662])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3875])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3667])).

cnf(c_32027,negated_conjecture,
    ( r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),k5_xboole_0(k1_tarski(sK378),k5_xboole_0(k1_tarski(sK377),k4_xboole_0(k1_tarski(sK377),k4_xboole_0(k1_tarski(sK377),k1_tarski(sK378))))))) ),
    inference(theory_normalisation,[status(thm)],[c_2264,c_211,c_7])).

cnf(c_65223,plain,
    ( r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),k5_xboole_0(k1_tarski(sK378),k5_xboole_0(k1_tarski(sK377),k4_xboole_0(k1_tarski(sK377),k4_xboole_0(k1_tarski(sK377),k1_tarski(sK378))))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32027])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5975])).

cnf(c_70798,plain,
    ( r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),k5_xboole_0(k1_tarski(sK378),k4_xboole_0(k1_tarski(sK377),k1_tarski(sK378))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_65223,c_1])).

cnf(c_2258,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))
    | k2_mcart_1(X0) = X2
    | k2_mcart_1(X0) = X3 ),
    inference(cnf_transformation,[],[f6658])).

cnf(c_32031,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3)))))))
    | k2_mcart_1(X0) = X2
    | k2_mcart_1(X0) = X3 ),
    inference(theory_normalisation,[status(thm)],[c_2258,c_211,c_7])).

cnf(c_65227,plain,
    ( k2_mcart_1(X0) = X1
    | k2_mcart_1(X0) = X2
    | r2_hidden(X0,k2_zfmisc_1(X3,k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32031])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6108])).

cnf(c_32283,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_74055,plain,
    ( k2_mcart_1(X0) = X1
    | k2_mcart_1(X0) = X2
    | r2_hidden(X0,k2_zfmisc_1(X3,k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_65227,c_32283])).

cnf(c_84506,plain,
    ( k2_mcart_1(sK375) = sK377
    | k2_mcart_1(sK375) = sK378 ),
    inference(superposition,[status(thm)],[c_70798,c_74055])).

cnf(c_2251,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
    | k1_mcart_1(X0) = X1 ),
    inference(cnf_transformation,[],[f5928])).

cnf(c_65234,plain,
    ( k1_mcart_1(X0) = X1
    | r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2251])).

cnf(c_84402,plain,
    ( k1_mcart_1(sK375) = sK376 ),
    inference(superposition,[status(thm)],[c_70798,c_65234])).

cnf(c_2262,negated_conjecture,
    ( k2_mcart_1(sK375) != sK378
    | k1_mcart_1(sK375) != sK376 ),
    inference(cnf_transformation,[],[f5942])).

cnf(c_2263,negated_conjecture,
    ( k2_mcart_1(sK375) != sK377
    | k1_mcart_1(sK375) != sK376 ),
    inference(cnf_transformation,[],[f5941])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_84506,c_84402,c_2262,c_2263])).

%------------------------------------------------------------------------------
