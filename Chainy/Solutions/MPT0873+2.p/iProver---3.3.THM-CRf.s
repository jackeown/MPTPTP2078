%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0873+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:55 EST 2020

% Result     : Theorem 27.76s
% Output     : CNFRefutation 27.76s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 144 expanded)
%              Number of clauses        :   19 (  34 expanded)
%              Number of leaves         :    6 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   92 ( 310 expanded)
%              Number of equality atoms :   91 ( 309 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1317,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1318,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
       => ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 ) ) ),
    inference(negated_conjecture,[],[f1317])).

fof(f2666,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f1318])).

fof(f3677,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) )
   => ( ( sK381 != sK385
        | sK380 != sK384
        | sK379 != sK383
        | sK378 != sK382 )
      & k4_mcart_1(sK378,sK379,sK380,sK381) = k4_mcart_1(sK382,sK383,sK384,sK385) ) ),
    introduced(choice_axiom,[])).

fof(f3678,plain,
    ( ( sK381 != sK385
      | sK380 != sK384
      | sK379 != sK383
      | sK378 != sK382 )
    & k4_mcart_1(sK378,sK379,sK380,sK381) = k4_mcart_1(sK382,sK383,sK384,sK385) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK378,sK379,sK380,sK381,sK382,sK383,sK384,sK385])],[f2666,f3677])).

fof(f5991,plain,(
    k4_mcart_1(sK378,sK379,sK380,sK381) = k4_mcart_1(sK382,sK383,sK384,sK385) ),
    inference(cnf_transformation,[],[f3678])).

fof(f1275,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5886,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1275])).

fof(f1274,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5885,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1274])).

fof(f6018,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f5886,f5885])).

fof(f6729,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK378,sK379),sK380),sK381) = k4_tarski(k4_tarski(k4_tarski(sK382,sK383),sK384),sK385) ),
    inference(definition_unfolding,[],[f5991,f6018,f6018])).

fof(f1323,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6001,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1323])).

fof(f1312,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2663,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1312])).

fof(f5981,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f2663])).

fof(f6721,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k4_tarski(k4_tarski(X0,X1),X2) != k4_tarski(k4_tarski(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f5981,f5885,f5885])).

fof(f5982,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f2663])).

fof(f6720,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k4_tarski(k4_tarski(X0,X1),X2) != k4_tarski(k4_tarski(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f5982,f5885,f5885])).

fof(f6002,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f1323])).

fof(f5992,plain,
    ( sK381 != sK385
    | sK380 != sK384
    | sK379 != sK383
    | sK378 != sK382 ),
    inference(cnf_transformation,[],[f3678])).

cnf(c_2286,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(sK378,sK379),sK380),sK381) = k4_tarski(k4_tarski(k4_tarski(sK382,sK383),sK384),sK385) ),
    inference(cnf_transformation,[],[f6729])).

cnf(c_2296,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6001])).

cnf(c_88688,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK378,sK379),sK380),sK381)) = k4_tarski(k4_tarski(sK382,sK383),sK384) ),
    inference(superposition,[status(thm)],[c_2286,c_2296])).

cnf(c_88838,plain,
    ( k4_tarski(k4_tarski(sK382,sK383),sK384) = k4_tarski(k4_tarski(sK378,sK379),sK380) ),
    inference(demodulation,[status(thm)],[c_88688,c_2296])).

cnf(c_2277,plain,
    ( X0 = X1
    | k4_tarski(k4_tarski(X0,X2),X3) != k4_tarski(k4_tarski(X1,X4),X5) ),
    inference(cnf_transformation,[],[f6721])).

cnf(c_91507,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != k4_tarski(k4_tarski(sK378,sK379),sK380)
    | sK382 = X0 ),
    inference(superposition,[status(thm)],[c_88838,c_2277])).

cnf(c_94902,plain,
    ( sK382 = sK378 ),
    inference(equality_resolution,[status(thm)],[c_91507])).

cnf(c_2276,plain,
    ( X0 = X1
    | k4_tarski(k4_tarski(X2,X0),X3) != k4_tarski(k4_tarski(X4,X1),X5) ),
    inference(cnf_transformation,[],[f6720])).

cnf(c_91503,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != k4_tarski(k4_tarski(sK378,sK379),sK380)
    | sK383 = X1 ),
    inference(superposition,[status(thm)],[c_88838,c_2276])).

cnf(c_94506,plain,
    ( sK383 = sK379 ),
    inference(equality_resolution,[status(thm)],[c_91503])).

cnf(c_2295,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f6002])).

cnf(c_91497,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(sK378,sK379),sK380)) = sK384 ),
    inference(superposition,[status(thm)],[c_88838,c_2295])).

cnf(c_91539,plain,
    ( sK384 = sK380 ),
    inference(demodulation,[status(thm)],[c_91497,c_2295])).

cnf(c_88689,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK378,sK379),sK380),sK381)) = sK385 ),
    inference(superposition,[status(thm)],[c_2286,c_2295])).

cnf(c_88709,plain,
    ( sK385 = sK381 ),
    inference(demodulation,[status(thm)],[c_88689,c_2295])).

cnf(c_2285,negated_conjecture,
    ( sK378 != sK382
    | sK379 != sK383
    | sK380 != sK384
    | sK381 != sK385 ),
    inference(cnf_transformation,[],[f5992])).

cnf(c_89512,plain,
    ( sK382 != sK378
    | sK383 != sK379
    | sK384 != sK380
    | sK381 != sK381 ),
    inference(demodulation,[status(thm)],[c_88709,c_2285])).

cnf(c_89516,plain,
    ( sK382 != sK378
    | sK383 != sK379
    | sK384 != sK380 ),
    inference(equality_resolution_simp,[status(thm)],[c_89512])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_94902,c_94506,c_91539,c_89516])).

%------------------------------------------------------------------------------
