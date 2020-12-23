%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0004+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:10 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 160 expanded)
%              Number of clauses        :   27 (  49 expanded)
%              Number of leaves         :    9 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  131 ( 405 expanded)
%              Number of equality atoms :   45 ( 110 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).

fof(f84,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f29,conjecture,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f34,plain,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))
     => r2_hidden(sK11,k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,
    ( ? [X0,X1] :
        ( ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) )
   => ( ( r1_xboole_0(sK9,sK10)
        & ? [X2] : r2_hidden(X2,k3_xboole_0(sK9,sK10)) )
      | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK9,sK10))
        & ~ r1_xboole_0(sK9,sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,
    ( ( r1_xboole_0(sK9,sK10)
      & r2_hidden(sK11,k3_xboole_0(sK9,sK10)) )
    | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK9,sK10))
      & ~ r1_xboole_0(sK9,sK10) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f42,f77,f76])).

fof(f131,plain,(
    ! [X3] :
      ( r1_xboole_0(sK9,sK10)
      | ~ r2_hidden(X3,k3_xboole_0(sK9,sK10)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f111,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f136,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f111,f85])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f134,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = o_0_0_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f105,f85])).

fof(f129,plain,(
    ! [X3] :
      ( r2_hidden(sK11,k3_xboole_0(sK9,sK10))
      | ~ r2_hidden(X3,k3_xboole_0(sK9,sK10)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f133,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != o_0_0_xboole_0 ) ),
    inference(definition_unfolding,[],[f106,f85])).

fof(f128,plain,
    ( r2_hidden(sK11,k3_xboole_0(sK9,sK10))
    | ~ r1_xboole_0(sK9,sK10) ),
    inference(cnf_transformation,[],[f78])).

fof(f83,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f18,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f108,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f135,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f108,f85])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2012,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_47,negated_conjecture,
    ( r1_xboole_0(sK9,sK10)
    | ~ r2_hidden(X0,k3_xboole_0(sK9,sK10)) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_1972,plain,
    ( r1_xboole_0(sK9,sK10) = iProver_top
    | r2_hidden(X0,k3_xboole_0(sK9,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_2621,plain,
    ( r1_xboole_0(sK9,sK10) = iProver_top
    | v1_xboole_0(k3_xboole_0(sK9,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2012,c_1972])).

cnf(c_30,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f136])).

cnf(c_1989,plain,
    ( o_0_0_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2725,plain,
    ( k3_xboole_0(sK9,sK10) = o_0_0_xboole_0
    | r1_xboole_0(sK9,sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_2621,c_1989])).

cnf(c_25,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f134])).

cnf(c_1991,plain,
    ( k3_xboole_0(X0,X1) = o_0_0_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3198,plain,
    ( k3_xboole_0(sK9,sK10) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_2725,c_1991])).

cnf(c_49,negated_conjecture,
    ( ~ r2_hidden(X0,k3_xboole_0(sK9,sK10))
    | r2_hidden(sK11,k3_xboole_0(sK9,sK10)) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_1971,plain,
    ( r2_hidden(X0,k3_xboole_0(sK9,sK10)) != iProver_top
    | r2_hidden(sK11,k3_xboole_0(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_3209,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top
    | r2_hidden(sK11,o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3198,c_1971])).

cnf(c_24,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_3059,plain,
    ( r1_xboole_0(sK9,sK10)
    | k3_xboole_0(sK9,sK10) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_3060,plain,
    ( k3_xboole_0(sK9,sK10) != o_0_0_xboole_0
    | r1_xboole_0(sK9,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3059])).

cnf(c_50,negated_conjecture,
    ( ~ r1_xboole_0(sK9,sK10)
    | r2_hidden(sK11,k3_xboole_0(sK9,sK10)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1970,plain,
    ( r1_xboole_0(sK9,sK10) != iProver_top
    | r2_hidden(sK11,k3_xboole_0(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_3211,plain,
    ( r1_xboole_0(sK9,sK10) != iProver_top
    | r2_hidden(sK11,o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3198,c_1970])).

cnf(c_3461,plain,
    ( r2_hidden(sK11,o_0_0_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3209,c_3060,c_3198,c_3211])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2011,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3466,plain,
    ( v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3461,c_2011])).

cnf(c_27,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_94,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3466,c_94])).

%------------------------------------------------------------------------------
