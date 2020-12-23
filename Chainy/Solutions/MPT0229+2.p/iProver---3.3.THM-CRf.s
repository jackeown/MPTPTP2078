%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0229+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:29 EST 2020

% Result     : Theorem 7.87s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :   18 (  23 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    9
%              Number of atoms          :   30 (  42 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f313,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f314,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f313])).

fof(f448,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f314])).

fof(f565,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK28 != sK29
      & r1_tarski(k1_tarski(sK28),k1_tarski(sK29)) ) ),
    introduced(choice_axiom,[])).

fof(f566,plain,
    ( sK28 != sK29
    & r1_tarski(k1_tarski(sK28),k1_tarski(sK29)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28,sK29])],[f448,f565])).

fof(f979,plain,(
    r1_tarski(k1_tarski(sK28),k1_tarski(sK29)) ),
    inference(cnf_transformation,[],[f566])).

fof(f316,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f449,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f316])).

fof(f982,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f449])).

fof(f980,plain,(
    sK28 != sK29 ),
    inference(cnf_transformation,[],[f566])).

cnf(c_401,negated_conjecture,
    ( r1_tarski(k1_tarski(sK28),k1_tarski(sK29)) ),
    inference(cnf_transformation,[],[f979])).

cnf(c_12481,plain,
    ( r1_tarski(k1_tarski(sK28),k1_tarski(sK29)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_403,plain,
    ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f982])).

cnf(c_12480,plain,
    ( X0 = X1
    | r1_tarski(k1_tarski(X1),k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_15871,plain,
    ( sK29 = sK28 ),
    inference(superposition,[status(thm)],[c_12481,c_12480])).

cnf(c_400,negated_conjecture,
    ( sK28 != sK29 ),
    inference(cnf_transformation,[],[f980])).

cnf(c_16134,plain,
    ( sK28 != sK28 ),
    inference(demodulation,[status(thm)],[c_15871,c_400])).

cnf(c_16135,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_16134])).

%------------------------------------------------------------------------------
