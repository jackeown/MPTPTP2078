%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0852+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:54 EST 2020

% Result     : Theorem 27.28s
% Output     : CNFRefutation 27.28s
% Verified   : 
% Statistics : Number of formulae       :   20 (  43 expanded)
%              Number of clauses        :    9 (  11 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   29 (  77 expanded)
%              Number of equality atoms :   28 (  76 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1299,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1300,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f1299])).

fof(f2631,plain,(
    ? [X0] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f1300])).

fof(f3639,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(sK382,sK383) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f3638,plain,
    ( ? [X0] :
        ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( k4_tarski(k1_mcart_1(sK381),k2_mcart_1(sK381)) != sK381
      & ? [X2,X1] : k4_tarski(X1,X2) = sK381 ) ),
    introduced(choice_axiom,[])).

fof(f3640,plain,
    ( k4_tarski(k1_mcart_1(sK381),k2_mcart_1(sK381)) != sK381
    & k4_tarski(sK382,sK383) = sK381 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK381,sK382,sK383])],[f2631,f3639,f3638])).

fof(f5917,plain,(
    k4_tarski(sK382,sK383) = sK381 ),
    inference(cnf_transformation,[],[f3640])).

fof(f1298,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5916,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f1298])).

fof(f5918,plain,(
    k4_tarski(k1_mcart_1(sK381),k2_mcart_1(sK381)) != sK381 ),
    inference(cnf_transformation,[],[f3640])).

fof(f5915,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1298])).

cnf(c_2262,negated_conjecture,
    ( k4_tarski(sK382,sK383) = sK381 ),
    inference(cnf_transformation,[],[f5917])).

cnf(c_2259,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f5916])).

cnf(c_86068,plain,
    ( k2_mcart_1(sK381) = sK383 ),
    inference(superposition,[status(thm)],[c_2262,c_2259])).

cnf(c_2261,negated_conjecture,
    ( k4_tarski(k1_mcart_1(sK381),k2_mcart_1(sK381)) != sK381 ),
    inference(cnf_transformation,[],[f5918])).

cnf(c_86173,plain,
    ( k4_tarski(k1_mcart_1(sK381),sK383) != sK381 ),
    inference(demodulation,[status(thm)],[c_86068,c_2261])).

cnf(c_2260,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5915])).

cnf(c_86070,plain,
    ( k1_mcart_1(sK381) = sK382 ),
    inference(superposition,[status(thm)],[c_2262,c_2260])).

cnf(c_86192,plain,
    ( sK381 != sK381 ),
    inference(light_normalisation,[status(thm)],[c_86173,c_2262,c_86070])).

cnf(c_86193,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_86192])).

%------------------------------------------------------------------------------
