%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0284+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:33 EST 2020

% Result     : Timeout 59.71s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   60 ( 124 expanded)
%              Number of clauses        :   29 (  45 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :   92 ( 171 expanded)
%              Number of equality atoms :   38 (  81 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f375,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f553,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f375])).

fof(f1235,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f553])).

fof(f57,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f413,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f807,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f413])).

fof(f59,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f415,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f59])).

fof(f416,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f415])).

fof(f809,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f416])).

fof(f381,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f382,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f381])).

fof(f555,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f382])).

fof(f708,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k1_zfmisc_1(k4_xboole_0(sK36,sK35))),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) ),
    introduced(choice_axiom,[])).

fof(f709,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k1_zfmisc_1(k4_xboole_0(sK36,sK35))),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f555,f708])).

fof(f1241,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k1_zfmisc_1(k4_xboole_0(sK36,sK35))),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) ),
    inference(cnf_transformation,[],[f709])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f925,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f865,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1244,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f925,f865])).

fof(f1597,plain,(
    ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k1_zfmisc_1(k4_xboole_0(sK36,sK35))),k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k1_zfmisc_1(k4_xboole_0(sK36,sK35))))),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) ),
    inference(definition_unfolding,[],[f1241,f1244])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f922,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f714,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f929,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f1388,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f929,f1244])).

fof(f168,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f927,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f168])).

cnf(c_513,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f1235])).

cnf(c_15402,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_97,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f807])).

cnf(c_15615,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_97])).

cnf(c_99,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f809])).

cnf(c_15613,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k5_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99])).

cnf(c_519,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k1_zfmisc_1(k4_xboole_0(sK36,sK35))),k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k1_zfmisc_1(k4_xboole_0(sK36,sK35))))),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) ),
    inference(cnf_transformation,[],[f1597])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f922])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f714])).

cnf(c_8860,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k5_xboole_0(k1_zfmisc_1(k4_xboole_0(sK36,sK35)),k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k1_zfmisc_1(k4_xboole_0(sK36,sK35)))))),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) ),
    inference(theory_normalisation,[status(thm)],[c_519,c_211,c_7])).

cnf(c_15397,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k5_xboole_0(k1_zfmisc_1(k4_xboole_0(sK36,sK35)),k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k1_zfmisc_1(k4_xboole_0(sK36,sK35)))))),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8860])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1388])).

cnf(c_9013,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_16851,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK36,sK35)),k1_zfmisc_1(k4_xboole_0(sK35,sK36)))),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15397,c_9013])).

cnf(c_202639,plain,
    ( r1_tarski(k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK36,sK35)),k1_zfmisc_1(k4_xboole_0(sK35,sK36))),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) != iProver_top
    | r1_tarski(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15613,c_16851])).

cnf(c_22909,plain,
    ( ~ r1_tarski(k4_xboole_0(sK35,sK36),k5_xboole_0(sK35,sK36))
    | r1_tarski(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_22910,plain,
    ( r1_tarski(k4_xboole_0(sK35,sK36),k5_xboole_0(sK35,sK36)) != iProver_top
    | r1_tarski(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22909])).

cnf(c_215,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f927])).

cnf(c_51806,plain,
    ( r1_tarski(k4_xboole_0(sK35,sK36),k5_xboole_0(sK35,sK36)) ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_51807,plain,
    ( r1_tarski(k4_xboole_0(sK35,sK36),k5_xboole_0(sK35,sK36)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51806])).

cnf(c_23115,plain,
    ( ~ r1_tarski(X0,k1_zfmisc_1(k5_xboole_0(sK35,sK36)))
    | ~ r1_tarski(X1,k1_zfmisc_1(k5_xboole_0(sK35,sK36)))
    | r1_tarski(k5_xboole_0(X0,X1),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) ),
    inference(instantiation,[status(thm)],[c_99])).

cnf(c_82492,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK36,sK35)),k1_zfmisc_1(k4_xboole_0(sK35,sK36))),k1_zfmisc_1(k5_xboole_0(sK35,sK36)))
    | r1_tarski(k5_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK36,sK35)),k1_zfmisc_1(k4_xboole_0(sK35,sK36)))),k1_zfmisc_1(k5_xboole_0(sK35,sK36)))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) ),
    inference(instantiation,[status(thm)],[c_23115])).

cnf(c_82493,plain,
    ( r1_tarski(k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK36,sK35)),k1_zfmisc_1(k4_xboole_0(sK35,sK36))),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) != iProver_top
    | r1_tarski(k5_xboole_0(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK36,sK35)),k1_zfmisc_1(k4_xboole_0(sK35,sK36)))),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) = iProver_top
    | r1_tarski(k1_zfmisc_1(k4_xboole_0(sK35,sK36)),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_82492])).

cnf(c_205477,plain,
    ( r1_tarski(k4_xboole_0(k1_zfmisc_1(k4_xboole_0(sK36,sK35)),k1_zfmisc_1(k4_xboole_0(sK35,sK36))),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_202639,c_16851,c_22910,c_51807,c_82493])).

cnf(c_211582,plain,
    ( r1_tarski(k1_zfmisc_1(k4_xboole_0(sK36,sK35)),k1_zfmisc_1(k5_xboole_0(sK35,sK36))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15615,c_205477])).

cnf(c_213765,plain,
    ( r1_tarski(k4_xboole_0(sK36,sK35),k5_xboole_0(sK35,sK36)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15402,c_211582])).

cnf(c_15541,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_21265,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_15541])).

cnf(c_214402,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_213765,c_21265])).

%------------------------------------------------------------------------------
