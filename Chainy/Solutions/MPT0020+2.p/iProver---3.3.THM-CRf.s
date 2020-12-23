%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0020+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:12 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   54 (  82 expanded)
%              Number of clauses        :   28 (  31 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 190 expanded)
%              Number of equality atoms :   29 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f144,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f54,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f226,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f43,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f43])).

fof(f84,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f85,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f84])).

fof(f140,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK14,sK16))
      & r1_tarski(sK15,sK16)
      & r1_tarski(sK13,sK14) ) ),
    introduced(choice_axiom,[])).

fof(f141,plain,
    ( ~ r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK14,sK16))
    & r1_tarski(sK15,sK16)
    & r1_tarski(sK13,sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15,sK16])],[f85,f140])).

fof(f215,plain,(
    r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f141])).

fof(f46,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f86])).

fof(f218,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f56,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f56])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f92])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f216,plain,(
    ~ r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK14,sK16)) ),
    inference(cnf_transformation,[],[f141])).

fof(f214,plain,(
    r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f141])).

fof(f40,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f49,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f221,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_82,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f226])).

cnf(c_2812,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_82])).

cnf(c_3718,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_2812])).

cnf(c_71,negated_conjecture,
    ( r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f215])).

cnf(c_2817,plain,
    ( r1_tarski(sK15,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_74,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f218])).

cnf(c_2815,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_9226,plain,
    ( r1_tarski(sK16,X0) != iProver_top
    | r1_tarski(sK15,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2817,c_2815])).

cnf(c_10311,plain,
    ( r1_tarski(sK15,k2_xboole_0(X0,sK16)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3718,c_9226])).

cnf(c_84,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f228])).

cnf(c_2810,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_84])).

cnf(c_70,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK14,sK16)) ),
    inference(cnf_transformation,[],[f216])).

cnf(c_2818,plain,
    ( r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK14,sK16)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_6441,plain,
    ( r1_tarski(sK15,k2_xboole_0(sK14,sK16)) != iProver_top
    | r1_tarski(sK13,k2_xboole_0(sK14,sK16)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2810,c_2818])).

cnf(c_72,negated_conjecture,
    ( r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f214])).

cnf(c_86,plain,
    ( r1_tarski(sK13,sK14) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_88,plain,
    ( r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK14,sK16)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_3376,plain,
    ( r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK14,sK16))
    | ~ r1_tarski(sK15,k2_xboole_0(sK14,sK16))
    | ~ r1_tarski(sK13,k2_xboole_0(sK14,sK16)) ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_3377,plain,
    ( r1_tarski(k2_xboole_0(sK13,sK15),k2_xboole_0(sK14,sK16)) = iProver_top
    | r1_tarski(sK15,k2_xboole_0(sK14,sK16)) != iProver_top
    | r1_tarski(sK13,k2_xboole_0(sK14,sK16)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3376])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f211])).

cnf(c_77,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f221])).

cnf(c_1485,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X1,X2)) ),
    inference(theory_normalisation,[status(thm)],[c_67,c_77,c_2])).

cnf(c_3643,plain,
    ( r1_tarski(X0,k2_xboole_0(sK14,sK16))
    | ~ r1_tarski(X0,sK14) ),
    inference(instantiation,[status(thm)],[c_1485])).

cnf(c_4753,plain,
    ( r1_tarski(sK13,k2_xboole_0(sK14,sK16))
    | ~ r1_tarski(sK13,sK14) ),
    inference(instantiation,[status(thm)],[c_3643])).

cnf(c_4754,plain,
    ( r1_tarski(sK13,k2_xboole_0(sK14,sK16)) = iProver_top
    | r1_tarski(sK13,sK14) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4753])).

cnf(c_7527,plain,
    ( r1_tarski(sK15,k2_xboole_0(sK14,sK16)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6441,c_86,c_88,c_3377,c_4754])).

cnf(c_10516,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_10311,c_7527])).

%------------------------------------------------------------------------------
