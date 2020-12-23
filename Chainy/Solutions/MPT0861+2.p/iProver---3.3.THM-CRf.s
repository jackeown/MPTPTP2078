%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0861+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:55 EST 2020

% Result     : Theorem 27.46s
% Output     : CNFRefutation 27.46s
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
fof(f1299,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
     => ( k2_mcart_1(X0) = X3
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1300,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
       => ( k2_mcart_1(X0) = X3
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1299])).

fof(f2638,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) != X3
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) ) ),
    inference(ennf_transformation,[],[f1300])).

fof(f3645,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( k2_mcart_1(X0) != X3
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) )
   => ( ( k2_mcart_1(sK375) != sK378
        | ( k1_mcart_1(sK375) != sK377
          & k1_mcart_1(sK375) != sK376 ) )
      & r2_hidden(sK375,k2_zfmisc_1(k2_tarski(sK376,sK377),k1_tarski(sK378))) ) ),
    introduced(choice_axiom,[])).

fof(f3646,plain,
    ( ( k2_mcart_1(sK375) != sK378
      | ( k1_mcart_1(sK375) != sK377
        & k1_mcart_1(sK375) != sK376 ) )
    & r2_hidden(sK375,k2_zfmisc_1(k2_tarski(sK376,sK377),k1_tarski(sK378))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK375,sK376,sK377,sK378])],[f2638,f3645])).

fof(f5936,plain,(
    r2_hidden(sK375,k2_zfmisc_1(k2_tarski(sK376,sK377),k1_tarski(sK378))) ),
    inference(cnf_transformation,[],[f3646])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3972,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3876,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3816,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f5957,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f3876,f3816])).

fof(f5958,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f3972,f5957])).

fof(f6656,plain,(
    r2_hidden(sK375,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(k1_tarski(sK376),k1_tarski(sK377)),k4_xboole_0(k1_tarski(sK376),k4_xboole_0(k1_tarski(sK376),k1_tarski(sK377)))),k1_tarski(sK378))) ),
    inference(definition_unfolding,[],[f5936,f5958])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3873,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3665,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3743,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f5971,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f3743,f3816])).

fof(f1297,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2636,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) )
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f1297])).

fof(f5932,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(X0) = X2
      | k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(cnf_transformation,[],[f2636])).

fof(f6653,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(X0) = X2
      | k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2)))),X3)) ) ),
    inference(definition_unfolding,[],[f5932,f5958])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3880,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f6104,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f3880,f5957])).

fof(f1295,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2634,plain,(
    ! [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f1295])).

fof(f5929,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) = X2
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f2634])).

fof(f5938,plain,
    ( k2_mcart_1(sK375) != sK378
    | k1_mcart_1(sK375) != sK377 ),
    inference(cnf_transformation,[],[f3646])).

fof(f5937,plain,
    ( k2_mcart_1(sK375) != sK378
    | k1_mcart_1(sK375) != sK376 ),
    inference(cnf_transformation,[],[f3646])).

cnf(c_2262,negated_conjecture,
    ( r2_hidden(sK375,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(k1_tarski(sK376),k1_tarski(sK377)),k4_xboole_0(k1_tarski(sK376),k4_xboole_0(k1_tarski(sK376),k1_tarski(sK377)))),k1_tarski(sK378))) ),
    inference(cnf_transformation,[],[f6656])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3873])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3665])).

cnf(c_31997,negated_conjecture,
    ( r2_hidden(sK375,k2_zfmisc_1(k5_xboole_0(k1_tarski(sK377),k5_xboole_0(k1_tarski(sK376),k4_xboole_0(k1_tarski(sK376),k4_xboole_0(k1_tarski(sK376),k1_tarski(sK377))))),k1_tarski(sK378))) ),
    inference(theory_normalisation,[status(thm)],[c_2262,c_211,c_7])).

cnf(c_65157,plain,
    ( r2_hidden(sK375,k2_zfmisc_1(k5_xboole_0(k1_tarski(sK377),k5_xboole_0(k1_tarski(sK376),k4_xboole_0(k1_tarski(sK376),k4_xboole_0(k1_tarski(sK376),k1_tarski(sK377))))),k1_tarski(sK378))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31997])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5971])).

cnf(c_70730,plain,
    ( r2_hidden(sK375,k2_zfmisc_1(k5_xboole_0(k1_tarski(sK377),k4_xboole_0(k1_tarski(sK376),k1_tarski(sK377))),k1_tarski(sK378))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_65157,c_1])).

cnf(c_2257,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2)))),X3))
    | k1_mcart_1(X0) = X1
    | k1_mcart_1(X0) = X2 ),
    inference(cnf_transformation,[],[f6653])).

cnf(c_32000,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),X3))
    | k1_mcart_1(X0) = X1
    | k1_mcart_1(X0) = X2 ),
    inference(theory_normalisation,[status(thm)],[c_2257,c_211,c_7])).

cnf(c_65160,plain,
    ( k1_mcart_1(X0) = X1
    | k1_mcart_1(X0) = X2
    | r2_hidden(X0,k2_zfmisc_1(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32000])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6104])).

cnf(c_32251,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_73993,plain,
    ( k1_mcart_1(X0) = X1
    | k1_mcart_1(X0) = X2
    | r2_hidden(X0,k2_zfmisc_1(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),X3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_65160,c_32251])).

cnf(c_91246,plain,
    ( k1_mcart_1(sK375) = sK376
    | k1_mcart_1(sK375) = sK377 ),
    inference(superposition,[status(thm)],[c_70730,c_73993])).

cnf(c_2252,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
    | k2_mcart_1(X0) = X2 ),
    inference(cnf_transformation,[],[f5929])).

cnf(c_65165,plain,
    ( k2_mcart_1(X0) = X1
    | r2_hidden(X0,k2_zfmisc_1(X2,k1_tarski(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2252])).

cnf(c_84074,plain,
    ( k2_mcart_1(sK375) = sK378 ),
    inference(superposition,[status(thm)],[c_70730,c_65165])).

cnf(c_2260,negated_conjecture,
    ( k2_mcart_1(sK375) != sK378
    | k1_mcart_1(sK375) != sK377 ),
    inference(cnf_transformation,[],[f5938])).

cnf(c_2261,negated_conjecture,
    ( k2_mcart_1(sK375) != sK378
    | k1_mcart_1(sK375) != sK376 ),
    inference(cnf_transformation,[],[f5937])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_91246,c_84074,c_2260,c_2261])).

%------------------------------------------------------------------------------
