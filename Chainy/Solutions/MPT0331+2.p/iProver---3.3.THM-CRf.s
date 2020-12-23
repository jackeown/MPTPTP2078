%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0331+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:36 EST 2020

% Result     : Theorem 15.23s
% Output     : CNFRefutation 15.80s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 104 expanded)
%              Number of clauses        :   21 (  31 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :   71 ( 157 expanded)
%              Number of equality atoms :   49 ( 106 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f409,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f844,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f409])).

fof(f1463,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f844])).

fof(f357,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f358,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f357])).

fof(f613,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f358])).

fof(f828,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( k4_xboole_0(sK56,k2_tarski(sK54,sK55)) != sK56
      & ~ r2_hidden(sK55,sK56)
      & ~ r2_hidden(sK54,sK56) ) ),
    introduced(choice_axiom,[])).

fof(f829,plain,
    ( k4_xboole_0(sK56,k2_tarski(sK54,sK55)) != sK56
    & ~ r2_hidden(sK55,sK56)
    & ~ r2_hidden(sK54,sK56) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK54,sK55,sK56])],[f613,f828])).

fof(f1384,plain,(
    ~ r2_hidden(sK54,sK56) ),
    inference(cnf_transformation,[],[f829])).

fof(f1386,plain,(
    k4_xboole_0(sK56,k2_tarski(sK54,sK55)) != sK56 ),
    inference(cnf_transformation,[],[f829])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1176,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1080,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1020,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1512,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1080,f1020])).

fof(f1513,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f1176,f1512])).

fof(f1834,plain,(
    k4_xboole_0(sK56,k5_xboole_0(k5_xboole_0(k1_tarski(sK54),k1_tarski(sK55)),k4_xboole_0(k1_tarski(sK54),k4_xboole_0(k1_tarski(sK54),k1_tarski(sK55))))) != sK56 ),
    inference(definition_unfolding,[],[f1386,f1513])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1077,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f869,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1084,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f1656,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1084,f1512])).

fof(f103,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1013,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f103])).

fof(f1610,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f1013,f1512])).

fof(f1385,plain,(
    ~ r2_hidden(sK55,sK56) ),
    inference(cnf_transformation,[],[f829])).

cnf(c_585,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
    inference(cnf_transformation,[],[f1463])).

cnf(c_14490,plain,
    ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_509,negated_conjecture,
    ( ~ r2_hidden(sK54,sK56) ),
    inference(cnf_transformation,[],[f1384])).

cnf(c_14516,plain,
    ( r2_hidden(sK54,sK56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_39654,plain,
    ( k4_xboole_0(sK56,k1_tarski(sK54)) = sK56 ),
    inference(superposition,[status(thm)],[c_14490,c_14516])).

cnf(c_507,negated_conjecture,
    ( k4_xboole_0(sK56,k5_xboole_0(k5_xboole_0(k1_tarski(sK54),k1_tarski(sK55)),k4_xboole_0(k1_tarski(sK54),k4_xboole_0(k1_tarski(sK54),k1_tarski(sK55))))) != sK56 ),
    inference(cnf_transformation,[],[f1834])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1077])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f869])).

cnf(c_7108,negated_conjecture,
    ( k4_xboole_0(sK56,k5_xboole_0(k1_tarski(sK54),k5_xboole_0(k1_tarski(sK55),k4_xboole_0(k1_tarski(sK54),k4_xboole_0(k1_tarski(sK54),k1_tarski(sK55)))))) != sK56 ),
    inference(theory_normalisation,[status(thm)],[c_507,c_211,c_7])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1656])).

cnf(c_7238,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_148,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1610])).

cnf(c_7264,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(theory_normalisation,[status(thm)],[c_148,c_211,c_7])).

cnf(c_15499,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_7264,c_7238])).

cnf(c_15571,plain,
    ( k4_xboole_0(k4_xboole_0(sK56,k1_tarski(sK54)),k1_tarski(sK55)) != sK56 ),
    inference(demodulation,[status(thm)],[c_7108,c_7238,c_15499])).

cnf(c_41510,plain,
    ( k4_xboole_0(sK56,k1_tarski(sK55)) != sK56 ),
    inference(demodulation,[status(thm)],[c_39654,c_15571])).

cnf(c_508,negated_conjecture,
    ( ~ r2_hidden(sK55,sK56) ),
    inference(cnf_transformation,[],[f1385])).

cnf(c_14517,plain,
    ( r2_hidden(sK55,sK56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_39653,plain,
    ( k4_xboole_0(sK56,k1_tarski(sK55)) = sK56 ),
    inference(superposition,[status(thm)],[c_14490,c_14517])).

cnf(c_41511,plain,
    ( sK56 != sK56 ),
    inference(light_normalisation,[status(thm)],[c_41510,c_39653])).

cnf(c_41512,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_41511])).

%------------------------------------------------------------------------------
