%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0869+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:55 EST 2020

% Result     : Theorem 27.85s
% Output     : CNFRefutation 27.85s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 180 expanded)
%              Number of clauses        :   25 (  59 expanded)
%              Number of leaves         :    6 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :   89 ( 393 expanded)
%              Number of equality atoms :   76 ( 302 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1310,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1311,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
       => ( X2 = X5
          & X1 = X4
          & X0 = X3 ) ) ),
    inference(negated_conjecture,[],[f1310])).

fof(f2657,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1311])).

fof(f3665,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) )
   => ( ( sK378 != sK381
        | sK377 != sK380
        | sK376 != sK379 )
      & k3_mcart_1(sK376,sK377,sK378) = k3_mcart_1(sK379,sK380,sK381) ) ),
    introduced(choice_axiom,[])).

fof(f3666,plain,
    ( ( sK378 != sK381
      | sK377 != sK380
      | sK376 != sK379 )
    & k3_mcart_1(sK376,sK377,sK378) = k3_mcart_1(sK379,sK380,sK381) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK376,sK377,sK378,sK379,sK380,sK381])],[f2657,f3665])).

fof(f5970,plain,(
    k3_mcart_1(sK376,sK377,sK378) = k3_mcart_1(sK379,sK380,sK381) ),
    inference(cnf_transformation,[],[f3666])).

fof(f1274,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5875,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1274])).

fof(f6699,plain,(
    k4_tarski(k4_tarski(sK376,sK377),sK378) = k4_tarski(k4_tarski(sK379,sK380),sK381) ),
    inference(definition_unfolding,[],[f5970,f5875,f5875])).

fof(f827,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1993,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = k2_relat_1(X2)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f827])).

fof(f1994,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = k2_relat_1(X2)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1993])).

fof(f4952,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(X2)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1994])).

fof(f6900,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(k1_tarski(k4_tarski(X0,X1)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f4952])).

fof(f695,axiom,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4796,plain,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f695])).

fof(f389,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4234,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f389])).

fof(f5971,plain,
    ( sK378 != sK381
    | sK377 != sK380
    | sK376 != sK379 ),
    inference(cnf_transformation,[],[f3666])).

fof(f4951,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k1_relat_1(X2)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1994])).

fof(f6901,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f4951])).

cnf(c_2276,negated_conjecture,
    ( k4_tarski(k4_tarski(sK376,sK377),sK378) = k4_tarski(k4_tarski(sK379,sK380),sK381) ),
    inference(cnf_transformation,[],[f6699])).

cnf(c_1258,plain,
    ( ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1)))
    | k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X1) ),
    inference(cnf_transformation,[],[f6900])).

cnf(c_1103,plain,
    ( v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f4796])).

cnf(c_18750,plain,
    ( k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1258,c_1103])).

cnf(c_84490,plain,
    ( k2_relat_1(k1_tarski(k4_tarski(k4_tarski(sK376,sK377),sK378))) = k1_tarski(sK381) ),
    inference(superposition,[status(thm)],[c_2276,c_18750])).

cnf(c_84491,plain,
    ( k1_tarski(sK378) = k1_tarski(sK381) ),
    inference(demodulation,[status(thm)],[c_84490,c_18750])).

cnf(c_543,plain,
    ( k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f4234])).

cnf(c_84800,plain,
    ( k3_tarski(k1_tarski(sK378)) = sK381 ),
    inference(superposition,[status(thm)],[c_84491,c_543])).

cnf(c_84801,plain,
    ( sK381 = sK378 ),
    inference(demodulation,[status(thm)],[c_84800,c_543])).

cnf(c_2275,negated_conjecture,
    ( sK376 != sK379
    | sK377 != sK380
    | sK378 != sK381 ),
    inference(cnf_transformation,[],[f5971])).

cnf(c_84863,plain,
    ( sK379 != sK376
    | sK380 != sK377
    | sK378 != sK378 ),
    inference(demodulation,[status(thm)],[c_84801,c_2275])).

cnf(c_84867,plain,
    ( sK379 != sK376
    | sK380 != sK377 ),
    inference(equality_resolution_simp,[status(thm)],[c_84863])).

cnf(c_1259,plain,
    ( ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1)))
    | k1_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6901])).

cnf(c_18746,plain,
    ( k1_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1259,c_1103])).

cnf(c_84420,plain,
    ( k1_relat_1(k1_tarski(k4_tarski(k4_tarski(sK376,sK377),sK378))) = k1_tarski(k4_tarski(sK379,sK380)) ),
    inference(superposition,[status(thm)],[c_2276,c_18746])).

cnf(c_84421,plain,
    ( k1_tarski(k4_tarski(sK376,sK377)) = k1_tarski(k4_tarski(sK379,sK380)) ),
    inference(demodulation,[status(thm)],[c_84420,c_18746])).

cnf(c_84449,plain,
    ( k1_relat_1(k1_tarski(k4_tarski(sK376,sK377))) = k1_tarski(sK379) ),
    inference(superposition,[status(thm)],[c_84421,c_18746])).

cnf(c_84450,plain,
    ( k1_tarski(sK376) = k1_tarski(sK379) ),
    inference(demodulation,[status(thm)],[c_84449,c_18746])).

cnf(c_84798,plain,
    ( k3_tarski(k1_tarski(sK376)) = sK379 ),
    inference(superposition,[status(thm)],[c_84450,c_543])).

cnf(c_84807,plain,
    ( sK379 = sK376 ),
    inference(demodulation,[status(thm)],[c_84798,c_543])).

cnf(c_84489,plain,
    ( k2_relat_1(k1_tarski(k4_tarski(sK376,sK377))) = k1_tarski(sK380) ),
    inference(superposition,[status(thm)],[c_84421,c_18750])).

cnf(c_84494,plain,
    ( k1_tarski(sK377) = k1_tarski(sK380) ),
    inference(demodulation,[status(thm)],[c_84489,c_18750])).

cnf(c_84799,plain,
    ( k3_tarski(k1_tarski(sK377)) = sK380 ),
    inference(superposition,[status(thm)],[c_84494,c_543])).

cnf(c_84804,plain,
    ( sK380 = sK377 ),
    inference(demodulation,[status(thm)],[c_84799,c_543])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_84867,c_84807,c_84804])).

%------------------------------------------------------------------------------
