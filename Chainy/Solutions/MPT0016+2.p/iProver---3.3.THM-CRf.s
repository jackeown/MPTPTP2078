%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0016+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:11 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   45 (  75 expanded)
%              Number of clauses        :   24 (  31 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 136 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f135,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f211,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f52,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f52])).

fof(f85,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f131,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK14,sK15))
      & r1_tarski(sK13,sK14) ) ),
    introduced(choice_axiom,[])).

fof(f132,plain,
    ( ~ r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK14,sK15))
    & r1_tarski(sK13,sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f85,f131])).

fof(f214,plain,(
    r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f132])).

fof(f41,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f77])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f51,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f83])).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f215,plain,(
    ~ r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK14,sK15)) ),
    inference(cnf_transformation,[],[f132])).

fof(f44,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f206,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_76,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f211])).

cnf(c_2630,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76])).

cnf(c_3567,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_2630])).

cnf(c_80,negated_conjecture,
    ( r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f214])).

cnf(c_2626,plain,
    ( r1_tarski(sK13,sK14) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_80])).

cnf(c_68,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f203])).

cnf(c_2633,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_6333,plain,
    ( r1_tarski(sK14,X0) != iProver_top
    | r1_tarski(sK13,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2626,c_2633])).

cnf(c_7032,plain,
    ( r1_tarski(sK13,k2_xboole_0(X0,sK14)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3567,c_6333])).

cnf(c_78,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f213])).

cnf(c_2628,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78])).

cnf(c_79,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK14,sK15)) ),
    inference(cnf_transformation,[],[f215])).

cnf(c_71,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f206])).

cnf(c_1389,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK15,sK14)) ),
    inference(theory_normalisation,[status(thm)],[c_79,c_71,c_2])).

cnf(c_2627,plain,
    ( r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK15,sK14)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1389])).

cnf(c_4181,plain,
    ( r1_tarski(sK15,k2_xboole_0(sK15,sK14)) != iProver_top
    | r1_tarski(sK13,k2_xboole_0(sK15,sK14)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2628,c_2627])).

cnf(c_1409,plain,
    ( r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK15,sK14)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1389])).

cnf(c_3148,plain,
    ( r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK15,sK14))
    | ~ r1_tarski(sK15,k2_xboole_0(sK15,sK14))
    | ~ r1_tarski(sK13,k2_xboole_0(sK15,sK14)) ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_3149,plain,
    ( r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK15,sK14)) = iProver_top
    | r1_tarski(sK15,k2_xboole_0(sK15,sK14)) != iProver_top
    | r1_tarski(sK13,k2_xboole_0(sK15,sK14)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3148])).

cnf(c_3382,plain,
    ( r1_tarski(sK15,k2_xboole_0(sK15,sK14)) ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_3383,plain,
    ( r1_tarski(sK15,k2_xboole_0(sK15,sK14)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3382])).

cnf(c_4605,plain,
    ( r1_tarski(sK13,k2_xboole_0(sK15,sK14)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4181,c_1409,c_3149,c_3383])).

cnf(c_7162,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_7032,c_4605])).

%------------------------------------------------------------------------------
