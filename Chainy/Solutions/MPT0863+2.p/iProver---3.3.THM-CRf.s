%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0863+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:55 EST 2020

% Result     : Theorem 30.71s
% Output     : CNFRefutation 30.71s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 437 expanded)
%              Number of clauses        :   28 ( 101 expanded)
%              Number of leaves         :   11 ( 127 expanded)
%              Depth                    :   13
%              Number of atoms          :  140 ( 823 expanded)
%              Number of equality atoms :  113 ( 696 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1301,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
     => ( ( k2_mcart_1(X0) = X4
          | k2_mcart_1(X0) = X3 )
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1302,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
       => ( ( k2_mcart_1(X0) = X4
            | k2_mcart_1(X0) = X3 )
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1301])).

fof(f2642,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ( ( k2_mcart_1(X0) != X4
          & k2_mcart_1(X0) != X3 )
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) ) ),
    inference(ennf_transformation,[],[f1302])).

fof(f3649,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ( ( k2_mcart_1(X0) != X4
            & k2_mcart_1(X0) != X3 )
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) )
   => ( ( ( k2_mcart_1(sK375) != sK379
          & k2_mcart_1(sK375) != sK378 )
        | ( k1_mcart_1(sK375) != sK377
          & k1_mcart_1(sK375) != sK376 ) )
      & r2_hidden(sK375,k2_zfmisc_1(k2_tarski(sK376,sK377),k2_tarski(sK378,sK379))) ) ),
    introduced(choice_axiom,[])).

fof(f3650,plain,
    ( ( ( k2_mcart_1(sK375) != sK379
        & k2_mcart_1(sK375) != sK378 )
      | ( k1_mcart_1(sK375) != sK377
        & k1_mcart_1(sK375) != sK376 ) )
    & r2_hidden(sK375,k2_zfmisc_1(k2_tarski(sK376,sK377),k2_tarski(sK378,sK379))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK375,sK376,sK377,sK378,sK379])],[f2642,f3649])).

fof(f5944,plain,(
    r2_hidden(sK375,k2_zfmisc_1(k2_tarski(sK376,sK377),k2_tarski(sK378,sK379))) ),
    inference(cnf_transformation,[],[f3650])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3976,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3880,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3820,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f5967,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f3880,f3820])).

fof(f5968,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f3976,f5967])).

fof(f6670,plain,(
    r2_hidden(sK375,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(k1_tarski(sK376),k1_tarski(sK377)),k4_xboole_0(k1_tarski(sK376),k4_xboole_0(k1_tarski(sK376),k1_tarski(sK377)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK378),k1_tarski(sK379)),k4_xboole_0(k1_tarski(sK378),k4_xboole_0(k1_tarski(sK378),k1_tarski(sK379)))))) ),
    inference(definition_unfolding,[],[f5944,f5968,f5968])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3877,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3669,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3747,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f5981,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f3747,f3820])).

fof(f1297,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2638,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) )
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f1297])).

fof(f5936,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(X0) = X2
      | k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(cnf_transformation,[],[f2638])).

fof(f6663,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(X0) = X2
      | k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2)))),X3)) ) ),
    inference(definition_unfolding,[],[f5936,f5968])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3884,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f6114,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f3884,f5967])).

fof(f1298,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2639,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f1298])).

fof(f5939,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X0) = X3
      | k2_mcart_1(X0) = X2
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(cnf_transformation,[],[f2639])).

fof(f6664,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X0) = X3
      | k2_mcart_1(X0) = X2
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3)))))) ) ),
    inference(definition_unfolding,[],[f5939,f5968])).

fof(f5948,plain,
    ( k2_mcart_1(sK375) != sK379
    | k1_mcart_1(sK375) != sK377 ),
    inference(cnf_transformation,[],[f3650])).

fof(f5946,plain,
    ( k2_mcart_1(sK375) != sK378
    | k1_mcart_1(sK375) != sK377 ),
    inference(cnf_transformation,[],[f3650])).

fof(f5947,plain,
    ( k2_mcart_1(sK375) != sK379
    | k1_mcart_1(sK375) != sK376 ),
    inference(cnf_transformation,[],[f3650])).

fof(f5945,plain,
    ( k2_mcart_1(sK375) != sK378
    | k1_mcart_1(sK375) != sK376 ),
    inference(cnf_transformation,[],[f3650])).

cnf(c_2268,negated_conjecture,
    ( r2_hidden(sK375,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(k1_tarski(sK376),k1_tarski(sK377)),k4_xboole_0(k1_tarski(sK376),k4_xboole_0(k1_tarski(sK376),k1_tarski(sK377)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK378),k1_tarski(sK379)),k4_xboole_0(k1_tarski(sK378),k4_xboole_0(k1_tarski(sK378),k1_tarski(sK379)))))) ),
    inference(cnf_transformation,[],[f6670])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3877])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3669])).

cnf(c_32061,negated_conjecture,
    ( r2_hidden(sK375,k2_zfmisc_1(k5_xboole_0(k1_tarski(sK377),k5_xboole_0(k1_tarski(sK376),k4_xboole_0(k1_tarski(sK376),k4_xboole_0(k1_tarski(sK376),k1_tarski(sK377))))),k5_xboole_0(k1_tarski(sK379),k5_xboole_0(k1_tarski(sK378),k4_xboole_0(k1_tarski(sK378),k4_xboole_0(k1_tarski(sK378),k1_tarski(sK379))))))) ),
    inference(theory_normalisation,[status(thm)],[c_2268,c_211,c_7])).

cnf(c_65295,plain,
    ( r2_hidden(sK375,k2_zfmisc_1(k5_xboole_0(k1_tarski(sK377),k5_xboole_0(k1_tarski(sK376),k4_xboole_0(k1_tarski(sK376),k4_xboole_0(k1_tarski(sK376),k1_tarski(sK377))))),k5_xboole_0(k1_tarski(sK379),k5_xboole_0(k1_tarski(sK378),k4_xboole_0(k1_tarski(sK378),k4_xboole_0(k1_tarski(sK378),k1_tarski(sK379))))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32061])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5981])).

cnf(c_74684,plain,
    ( r2_hidden(sK375,k2_zfmisc_1(k5_xboole_0(k1_tarski(sK377),k4_xboole_0(k1_tarski(sK376),k1_tarski(sK377))),k5_xboole_0(k1_tarski(sK379),k4_xboole_0(k1_tarski(sK378),k1_tarski(sK379))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_65295,c_1])).

cnf(c_2257,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2)))),X3))
    | k1_mcart_1(X0) = X1
    | k1_mcart_1(X0) = X2 ),
    inference(cnf_transformation,[],[f6663])).

cnf(c_32068,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),X3))
    | k1_mcart_1(X0) = X1
    | k1_mcart_1(X0) = X2 ),
    inference(theory_normalisation,[status(thm)],[c_2257,c_211,c_7])).

cnf(c_65302,plain,
    ( k1_mcart_1(X0) = X1
    | k1_mcart_1(X0) = X2
    | r2_hidden(X0,k2_zfmisc_1(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32068])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6114])).

cnf(c_32319,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_74142,plain,
    ( k1_mcart_1(X0) = X1
    | k1_mcart_1(X0) = X2
    | r2_hidden(X0,k2_zfmisc_1(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),X3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_65302,c_32319])).

cnf(c_91323,plain,
    ( k1_mcart_1(sK375) = sK376
    | k1_mcart_1(sK375) = sK377 ),
    inference(superposition,[status(thm)],[c_74684,c_74142])).

cnf(c_2258,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3))))))
    | k2_mcart_1(X0) = X2
    | k2_mcart_1(X0) = X3 ),
    inference(cnf_transformation,[],[f6664])).

cnf(c_32067,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X3)))))))
    | k2_mcart_1(X0) = X2
    | k2_mcart_1(X0) = X3 ),
    inference(theory_normalisation,[status(thm)],[c_2258,c_211,c_7])).

cnf(c_65301,plain,
    ( k2_mcart_1(X0) = X1
    | k2_mcart_1(X0) = X2
    | r2_hidden(X0,k2_zfmisc_1(X3,k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32067])).

cnf(c_74135,plain,
    ( k2_mcart_1(X0) = X1
    | k2_mcart_1(X0) = X2
    | r2_hidden(X0,k2_zfmisc_1(X3,k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_65301,c_32319])).

cnf(c_89940,plain,
    ( k2_mcart_1(sK375) = sK378
    | k2_mcart_1(sK375) = sK379 ),
    inference(superposition,[status(thm)],[c_74684,c_74135])).

cnf(c_2264,negated_conjecture,
    ( k2_mcart_1(sK375) != sK379
    | k1_mcart_1(sK375) != sK377 ),
    inference(cnf_transformation,[],[f5948])).

cnf(c_90529,plain,
    ( k2_mcart_1(sK375) = sK379
    | k1_mcart_1(sK375) != sK377
    | sK378 != sK379 ),
    inference(superposition,[status(thm)],[c_89940,c_2264])).

cnf(c_2266,negated_conjecture,
    ( k2_mcart_1(sK375) != sK378
    | k1_mcart_1(sK375) != sK377 ),
    inference(cnf_transformation,[],[f5946])).

cnf(c_90789,plain,
    ( k1_mcart_1(sK375) != sK377 ),
    inference(global_propositional_subsumption,[status(thm)],[c_90529,c_2266,c_2264,c_89940])).

cnf(c_2265,negated_conjecture,
    ( k2_mcart_1(sK375) != sK379
    | k1_mcart_1(sK375) != sK376 ),
    inference(cnf_transformation,[],[f5947])).

cnf(c_90528,plain,
    ( k2_mcart_1(sK375) = sK379
    | k1_mcart_1(sK375) != sK376
    | sK378 != sK379 ),
    inference(superposition,[status(thm)],[c_89940,c_2265])).

cnf(c_2267,negated_conjecture,
    ( k2_mcart_1(sK375) != sK378
    | k1_mcart_1(sK375) != sK376 ),
    inference(cnf_transformation,[],[f5945])).

cnf(c_90786,plain,
    ( k1_mcart_1(sK375) != sK376 ),
    inference(global_propositional_subsumption,[status(thm)],[c_90528,c_2267,c_2265,c_89940])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_91323,c_90789,c_90786])).

%------------------------------------------------------------------------------
