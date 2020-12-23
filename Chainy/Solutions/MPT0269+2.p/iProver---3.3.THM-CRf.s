%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0269+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:32 EST 2020

% Result     : Theorem 11.36s
% Output     : CNFRefutation 11.36s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 225 expanded)
%              Number of clauses        :   33 (  50 expanded)
%              Number of leaves         :   13 (  67 expanded)
%              Depth                    :   18
%              Number of atoms          :  112 ( 353 expanded)
%              Number of equality atoms :   98 ( 339 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f365,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f366,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f365])).

fof(f534,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f366])).

fof(f678,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( k1_tarski(sK36) != sK35
      & k1_xboole_0 != sK35
      & k1_xboole_0 = k4_xboole_0(sK35,k1_tarski(sK36)) ) ),
    introduced(choice_axiom,[])).

fof(f679,plain,
    ( k1_tarski(sK36) != sK35
    & k1_xboole_0 != sK35
    & k1_xboole_0 = k4_xboole_0(sK35,k1_tarski(sK36)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f534,f678])).

fof(f1182,plain,(
    k1_xboole_0 = k4_xboole_0(sK35,k1_tarski(sK36)) ),
    inference(cnf_transformation,[],[f679])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f687,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1518,plain,(
    o_0_0_xboole_0 = k4_xboole_0(sK35,k1_tarski(sK36)) ),
    inference(definition_unfolding,[],[f1182,f687])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f683,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f835,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1202,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f683,f835,f835])).

fof(f60,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f780,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f60])).

fof(f1244,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f780,f835,f835,f835])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f825,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f1283,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f825,f687])).

fof(f111,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f836,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

fof(f1293,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f836,f835,f835])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f762,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f1199,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f762,f835])).

fof(f114,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f839,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f114])).

fof(f1296,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f839,f835,f835,f835])).

fof(f96,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f820,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f96])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f849,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f1302,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f849,f687])).

fof(f340,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f669,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f340])).

fof(f670,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f669])).

fof(f1139,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f670])).

fof(f1484,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(definition_unfolding,[],[f1139,f687])).

fof(f1184,plain,(
    k1_tarski(sK36) != sK35 ),
    inference(cnf_transformation,[],[f679])).

fof(f1183,plain,(
    k1_xboole_0 != sK35 ),
    inference(cnf_transformation,[],[f679])).

fof(f1517,plain,(
    o_0_0_xboole_0 != sK35 ),
    inference(definition_unfolding,[],[f1183,f687])).

cnf(c_492,negated_conjecture,
    ( o_0_0_xboole_0 = k4_xboole_0(sK35,k1_tarski(sK36)) ),
    inference(cnf_transformation,[],[f1518])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1202])).

cnf(c_100,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(cnf_transformation,[],[f1244])).

cnf(c_24916,plain,
    ( k4_xboole_0(k4_xboole_0(sK35,X0),k4_xboole_0(k4_xboole_0(sK35,X0),k1_tarski(sK36))) = k4_xboole_0(k4_xboole_0(sK35,o_0_0_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK36)))) ),
    inference(superposition,[status(thm)],[c_492,c_100])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1283])).

cnf(c_25126,plain,
    ( k4_xboole_0(k4_xboole_0(sK35,X0),k4_xboole_0(k4_xboole_0(sK35,X0),k1_tarski(sK36))) = k4_xboole_0(sK35,k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK36)))) ),
    inference(demodulation,[status(thm)],[c_24916,c_145])).

cnf(c_27799,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK35)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK35)),k1_tarski(sK36))) = k4_xboole_0(sK35,k4_xboole_0(k4_xboole_0(sK35,X0),k4_xboole_0(k4_xboole_0(sK35,X0),k1_tarski(sK36)))) ),
    inference(superposition,[status(thm)],[c_6,c_25126])).

cnf(c_27922,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK35)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK35)),k1_tarski(sK36))) = k4_xboole_0(sK35,k4_xboole_0(sK35,k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK36))))) ),
    inference(light_normalisation,[status(thm)],[c_27799,c_25126])).

cnf(c_155,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f1293])).

cnf(c_19639,plain,
    ( k4_xboole_0(sK35,k4_xboole_0(sK35,k4_xboole_0(k1_tarski(sK36),X0))) = k4_xboole_0(k4_xboole_0(sK35,o_0_0_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_492,c_155])).

cnf(c_19688,plain,
    ( k4_xboole_0(sK35,k4_xboole_0(sK35,k4_xboole_0(k1_tarski(sK36),X0))) = k4_xboole_0(sK35,X0) ),
    inference(demodulation,[status(thm)],[c_19639,c_145])).

cnf(c_19765,plain,
    ( k4_xboole_0(sK35,k4_xboole_0(sK35,k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK36))))) = k4_xboole_0(sK35,k4_xboole_0(k1_tarski(sK36),X0)) ),
    inference(superposition,[status(thm)],[c_6,c_19688])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1199])).

cnf(c_19776,plain,
    ( k4_xboole_0(sK35,k4_xboole_0(k1_tarski(sK36),X0)) = k5_xboole_0(sK35,k4_xboole_0(sK35,X0)) ),
    inference(superposition,[status(thm)],[c_19688,c_1])).

cnf(c_24010,plain,
    ( k4_xboole_0(sK35,k4_xboole_0(sK35,k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK36))))) = k5_xboole_0(sK35,k4_xboole_0(sK35,X0)) ),
    inference(light_normalisation,[status(thm)],[c_19765,c_19776])).

cnf(c_27924,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK35)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK35)),k1_tarski(sK36))) = k5_xboole_0(sK35,k4_xboole_0(sK35,X0)) ),
    inference(light_normalisation,[status(thm)],[c_27922,c_24010])).

cnf(c_158,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f1296])).

cnf(c_27925,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK35,k4_xboole_0(sK35,k1_tarski(sK36))))) = k5_xboole_0(sK35,k4_xboole_0(sK35,X0)) ),
    inference(demodulation,[status(thm)],[c_27924,c_155,c_158])).

cnf(c_27926,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK35,o_0_0_xboole_0))) = k5_xboole_0(sK35,k4_xboole_0(sK35,X0)) ),
    inference(light_normalisation,[status(thm)],[c_27925,c_492])).

cnf(c_27927,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK35)) = k5_xboole_0(sK35,k4_xboole_0(sK35,X0)) ),
    inference(demodulation,[status(thm)],[c_27926,c_145])).

cnf(c_140,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f820])).

cnf(c_14720,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_27985,plain,
    ( r1_tarski(k5_xboole_0(sK35,k4_xboole_0(sK35,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_27927,c_14720])).

cnf(c_29571,plain,
    ( r1_tarski(k5_xboole_0(sK35,o_0_0_xboole_0),k1_tarski(sK36)) = iProver_top ),
    inference(superposition,[status(thm)],[c_492,c_27985])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1302])).

cnf(c_29603,plain,
    ( r1_tarski(sK35,k1_tarski(sK36)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_29571,c_168])).

cnf(c_449,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1484])).

cnf(c_17655,plain,
    ( ~ r1_tarski(sK35,k1_tarski(X0))
    | k1_tarski(X0) = sK35
    | o_0_0_xboole_0 = sK35 ),
    inference(instantiation,[status(thm)],[c_449])).

cnf(c_22705,plain,
    ( ~ r1_tarski(sK35,k1_tarski(sK36))
    | k1_tarski(sK36) = sK35
    | o_0_0_xboole_0 = sK35 ),
    inference(instantiation,[status(thm)],[c_17655])).

cnf(c_22706,plain,
    ( k1_tarski(sK36) = sK35
    | o_0_0_xboole_0 = sK35
    | r1_tarski(sK35,k1_tarski(sK36)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22705])).

cnf(c_490,negated_conjecture,
    ( k1_tarski(sK36) != sK35 ),
    inference(cnf_transformation,[],[f1184])).

cnf(c_491,negated_conjecture,
    ( o_0_0_xboole_0 != sK35 ),
    inference(cnf_transformation,[],[f1517])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29603,c_22706,c_490,c_491])).

%------------------------------------------------------------------------------
