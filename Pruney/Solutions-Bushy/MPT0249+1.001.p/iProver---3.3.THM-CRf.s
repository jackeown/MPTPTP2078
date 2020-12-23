%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0249+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:49 EST 2020

% Result     : Theorem 0.95s
% Output     : CNFRefutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 118 expanded)
%              Number of clauses        :   24 (  52 expanded)
%              Number of leaves         :    5 (  30 expanded)
%              Depth                    :   16
%              Number of atoms          :   96 ( 397 expanded)
%              Number of equality atoms :   95 ( 396 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f6,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f16,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_tarski(X0) = X2
      | k1_tarski(X0) = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f19,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f7])).

fof(f8,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = X1
      | k1_xboole_0 = X1
      | k1_tarski(X0) = X1
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f18,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f17,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f7])).

cnf(c_11,negated_conjecture,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) != k1_tarski(X2)
    | k1_tarski(X2) = X1
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_131,plain,
    ( k1_tarski(X0) != k1_tarski(sK0)
    | k1_tarski(X0) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_8,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_30,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_36,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_31,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_71,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_72,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_133,plain,
    ( k1_tarski(X0) = sK2
    | k1_tarski(X0) != k1_tarski(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_131,c_8,c_36,c_72])).

cnf(c_134,plain,
    ( k1_tarski(X0) != k1_tarski(sK0)
    | k1_tarski(X0) = sK2 ),
    inference(renaming,[status(thm)],[c_133])).

cnf(c_138,plain,
    ( k1_tarski(sK0) = sK2 ),
    inference(equality_resolution,[status(thm)],[c_134])).

cnf(c_185,plain,
    ( k2_xboole_0(sK1,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_138,c_11])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,X1) != k1_tarski(X2)
    | k1_tarski(X2) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f8])).

cnf(c_257,plain,
    ( k1_tarski(X0) = sK1
    | k1_tarski(X0) != sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_185,c_7])).

cnf(c_9,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_73,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_74,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_326,plain,
    ( k1_tarski(X0) != sK2
    | k1_tarski(X0) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_257,c_9,c_36,c_74])).

cnf(c_327,plain,
    ( k1_tarski(X0) = sK1
    | k1_tarski(X0) != sK2 ),
    inference(renaming,[status(thm)],[c_326])).

cnf(c_331,plain,
    ( k1_tarski(sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_138,c_327])).

cnf(c_332,plain,
    ( sK1 = sK2 ),
    inference(light_normalisation,[status(thm)],[c_331,c_138])).

cnf(c_10,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_332,c_10])).


%------------------------------------------------------------------------------
