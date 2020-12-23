%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0216+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:45 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   30 (  46 expanded)
%              Number of clauses        :   18 (  20 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :   11
%              Number of atoms          :   53 (  87 expanded)
%              Number of equality atoms :   52 (  86 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k1_tarski(X0)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X1,X2) = k1_tarski(X0)
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( X1 != X2
      & k2_tarski(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( X1 != X2
        & k2_tarski(X1,X2) = k1_tarski(X0) )
   => ( sK1 != sK2
      & k2_tarski(sK1,sK2) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( sK1 != sK2
    & k2_tarski(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f11,plain,(
    k2_tarski(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( X0 = X1
      | k2_tarski(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | k2_tarski(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f8])).

cnf(c_3,negated_conjecture,
    ( k2_tarski(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_1,plain,
    ( X0 = X1
    | k2_tarski(X0,X2) != k1_tarski(X1) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_86,plain,
    ( k1_tarski(X0) != k1_tarski(sK0)
    | sK1 = X0 ),
    inference(superposition,[status(thm)],[c_3,c_1])).

cnf(c_132,plain,
    ( sK0 = sK1 ),
    inference(equality_resolution,[status(thm)],[c_86])).

cnf(c_135,plain,
    ( k2_tarski(sK1,sK2) = k1_tarski(sK1) ),
    inference(demodulation,[status(thm)],[c_132,c_3])).

cnf(c_0,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_84,plain,
    ( X0 = X1
    | k2_tarski(X2,X1) != k1_tarski(X0) ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_269,plain,
    ( k1_tarski(X0) != k1_tarski(sK1)
    | sK2 = X0 ),
    inference(superposition,[status(thm)],[c_135,c_84])).

cnf(c_278,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | sK2 = sK1 ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_11,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_28,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_29,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_10,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_15,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_13,plain,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1) ),
    theory(equality)).

cnf(c_14,plain,
    ( k1_tarski(sK1) = k1_tarski(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_278,c_29,c_15,c_14,c_2])).


%------------------------------------------------------------------------------
