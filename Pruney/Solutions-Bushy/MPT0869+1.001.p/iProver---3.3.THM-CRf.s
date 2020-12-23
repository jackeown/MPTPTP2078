%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0869+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:18 EST 2020

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 109 expanded)
%              Number of clauses        :   28 (  38 expanded)
%              Number of leaves         :    6 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :   94 ( 272 expanded)
%              Number of equality atoms :   93 ( 271 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
       => ( X2 = X5
          & X1 = X4
          & X0 = X3 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) )
   => ( ( sK2 != sK5
        | sK1 != sK4
        | sK0 != sK3 )
      & k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ( sK2 != sK5
      | sK1 != sK4
      | sK0 != sK3 )
    & k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f6,f7])).

fof(f12,plain,(
    k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,plain,(
    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f12,f9,f9])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f8])).

cnf(c_3,negated_conjecture,
    ( k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_0,plain,
    ( X0 = X1
    | k4_tarski(X2,X0) != k4_tarski(X3,X1) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_125,plain,
    ( k4_tarski(k4_tarski(sK0,sK1),sK2) != k4_tarski(X0,X1)
    | sK5 = X1 ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_136,plain,
    ( sK5 = sK2 ),
    inference(equality_resolution,[status(thm)],[c_125])).

cnf(c_213,plain,
    ( k4_tarski(k4_tarski(sK3,sK4),sK2) = k4_tarski(k4_tarski(sK0,sK1),sK2) ),
    inference(demodulation,[status(thm)],[c_136,c_3])).

cnf(c_1,plain,
    ( X0 = X1
    | k4_tarski(X0,X2) != k4_tarski(X1,X3) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_282,plain,
    ( k4_tarski(k4_tarski(sK0,sK1),sK2) != k4_tarski(X0,X1)
    | k4_tarski(sK3,sK4) = X0 ),
    inference(superposition,[status(thm)],[c_213,c_1])).

cnf(c_339,plain,
    ( k4_tarski(sK3,sK4) = k4_tarski(sK0,sK1) ),
    inference(equality_resolution,[status(thm)],[c_282])).

cnf(c_349,plain,
    ( k4_tarski(X0,X1) != k4_tarski(sK0,sK1)
    | sK4 = X1 ),
    inference(superposition,[status(thm)],[c_339,c_0])).

cnf(c_451,plain,
    ( sK4 = sK1 ),
    inference(equality_resolution,[status(thm)],[c_349])).

cnf(c_2,negated_conjecture,
    ( sK0 != sK3
    | sK1 != sK4
    | sK2 != sK5 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_212,plain,
    ( sK3 != sK0
    | sK4 != sK1
    | sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_136,c_2])).

cnf(c_216,plain,
    ( sK3 != sK0
    | sK4 != sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_212])).

cnf(c_9,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_60,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_146,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_148,plain,
    ( sK3 != sK3
    | sK3 = sK0
    | sK0 != sK3 ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_8,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_110,plain,
    ( k4_tarski(sK3,X0) = k4_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_55,plain,
    ( k4_tarski(sK3,X0) != k4_tarski(X1,X2)
    | sK3 = X1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_109,plain,
    ( k4_tarski(sK3,X0) != k4_tarski(sK3,X0)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_31,plain,
    ( k4_tarski(sK0,X0) != k4_tarski(sK3,X1)
    | sK0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_102,plain,
    ( k4_tarski(sK0,sK1) != k4_tarski(sK3,sK4)
    | sK0 = sK3 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_43,plain,
    ( k4_tarski(k4_tarski(sK0,X0),X1) != k4_tarski(k4_tarski(sK3,X2),X3)
    | k4_tarski(sK0,X0) = k4_tarski(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_99,plain,
    ( k4_tarski(k4_tarski(sK0,sK1),sK2) != k4_tarski(k4_tarski(sK3,sK4),sK5)
    | k4_tarski(sK0,sK1) = k4_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_461,plain,
    ( k4_tarski(sK3,sK0) = k4_tarski(sK3,sK0) ),
    inference(grounding,[status(thm)],[c_110:[bind(X0,$fot(sK0))]])).

cnf(c_462,plain,
    ( k4_tarski(sK3,sK0) != k4_tarski(sK3,sK0)
    | sK3 = sK3 ),
    inference(grounding,[status(thm)],[c_109:[bind(X0,$fot(sK0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_451,c_216,c_148,c_461,c_462,c_102,c_99,c_3])).


%------------------------------------------------------------------------------
