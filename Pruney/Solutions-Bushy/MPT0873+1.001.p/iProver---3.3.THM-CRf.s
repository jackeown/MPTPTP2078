%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0873+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:18 EST 2020

% Result     : Theorem 1.00s
% Output     : CNFRefutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 157 expanded)
%              Number of clauses        :   21 (  44 expanded)
%              Number of leaves         :    5 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  101 ( 444 expanded)
%              Number of equality atoms :  100 ( 443 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
       => ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f9])).

fof(f17,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f19,plain,(
    k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) = k4_tarski(k3_mcart_1(sK4,sK5,sK6),sK7) ),
    inference(definition_unfolding,[],[f17,f11,f11])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f10])).

cnf(c_6,negated_conjecture,
    ( k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) = k4_tarski(k3_mcart_1(sK4,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_3,plain,
    ( X0 = X1
    | k4_tarski(X2,X0) != k4_tarski(X3,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_163,plain,
    ( k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) != k4_tarski(X0,X1)
    | sK7 = X1 ),
    inference(superposition,[status(thm)],[c_6,c_3])).

cnf(c_174,plain,
    ( sK7 = sK3 ),
    inference(equality_resolution,[status(thm)],[c_163])).

cnf(c_329,plain,
    ( k4_tarski(k3_mcart_1(sK4,sK5,sK6),sK3) = k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) ),
    inference(demodulation,[status(thm)],[c_174,c_6])).

cnf(c_4,plain,
    ( X0 = X1
    | k4_tarski(X1,X2) != k4_tarski(X0,X3) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_473,plain,
    ( k3_mcart_1(sK4,sK5,sK6) = X0
    | k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) != k4_tarski(X0,X1) ),
    inference(superposition,[status(thm)],[c_329,c_4])).

cnf(c_616,plain,
    ( k3_mcart_1(sK4,sK5,sK6) = k3_mcart_1(sK0,sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_473])).

cnf(c_2,plain,
    ( X0 = X1
    | k3_mcart_1(X0,X2,X3) != k3_mcart_1(X1,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_861,plain,
    ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(sK0,sK1,sK2)
    | sK4 = X0 ),
    inference(superposition,[status(thm)],[c_616,c_2])).

cnf(c_1168,plain,
    ( sK4 = sK0 ),
    inference(equality_resolution,[status(thm)],[c_861])).

cnf(c_1,plain,
    ( X0 = X1
    | k3_mcart_1(X2,X0,X3) != k3_mcart_1(X4,X1,X5) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_859,plain,
    ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(sK0,sK1,sK2)
    | sK5 = X1 ),
    inference(superposition,[status(thm)],[c_616,c_1])).

cnf(c_1028,plain,
    ( sK5 = sK1 ),
    inference(equality_resolution,[status(thm)],[c_859])).

cnf(c_0,plain,
    ( X0 = X1
    | k3_mcart_1(X2,X3,X0) != k3_mcart_1(X4,X5,X1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_857,plain,
    ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(sK0,sK1,sK2)
    | sK6 = X2 ),
    inference(superposition,[status(thm)],[c_616,c_0])).

cnf(c_1014,plain,
    ( sK6 = sK2 ),
    inference(equality_resolution,[status(thm)],[c_857])).

cnf(c_5,negated_conjecture,
    ( sK0 != sK4
    | sK1 != sK5
    | sK2 != sK6
    | sK3 != sK7 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_328,plain,
    ( sK4 != sK0
    | sK5 != sK1
    | sK6 != sK2
    | sK3 != sK3 ),
    inference(demodulation,[status(thm)],[c_174,c_5])).

cnf(c_332,plain,
    ( sK4 != sK0
    | sK5 != sK1
    | sK6 != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_328])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1168,c_1028,c_1014,c_332])).


%------------------------------------------------------------------------------
