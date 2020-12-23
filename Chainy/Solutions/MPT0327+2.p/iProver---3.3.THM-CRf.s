%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0327+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:35 EST 2020

% Result     : Theorem 19.46s
% Output     : CNFRefutation 19.46s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 473 expanded)
%              Number of clauses        :   46 ( 148 expanded)
%              Number of leaves         :   17 ( 129 expanded)
%              Depth                    :   19
%              Number of atoms          :  114 ( 594 expanded)
%              Number of equality atoms :   88 ( 437 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f352,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f353,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f352])).

fof(f602,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f353])).

fof(f815,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK55,k1_tarski(sK54)),k1_tarski(sK54)) != sK55
      & r2_hidden(sK54,sK55) ) ),
    introduced(choice_axiom,[])).

fof(f816,plain,
    ( k2_xboole_0(k4_xboole_0(sK55,k1_tarski(sK54)),k1_tarski(sK54)) != sK55
    & r2_hidden(sK54,sK55) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK54,sK55])],[f602,f815])).

fof(f1358,plain,(
    r2_hidden(sK54,sK55) ),
    inference(cnf_transformation,[],[f816])).

fof(f399,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1427,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f399])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1007,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1844,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(definition_unfolding,[],[f1427,f1007])).

fof(f395,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f630,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f395])).

fof(f1423,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f630])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f934,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f1496,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f934,f1007])).

fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1065,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f859,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1626,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f1065,f859])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f855,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f1499,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f855,f1007,f1007])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f997,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f1580,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f997,f859])).

fof(f111,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1008,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

fof(f1590,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f1008,f1007,f1007])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f984,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f1572,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f984,f1007,f859,f859])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1071,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1067,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f1485,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1067,f1007])).

fof(f1629,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1071,f1485])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1064,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f856,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1021,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f1599,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f1021,f859])).

fof(f1359,plain,(
    k2_xboole_0(k4_xboole_0(sK55,k1_tarski(sK54)),k1_tarski(sK54)) != sK55 ),
    inference(cnf_transformation,[],[f816])).

fof(f1794,plain,(
    k5_xboole_0(k5_xboole_0(k4_xboole_0(sK55,k1_tarski(sK54)),k1_tarski(sK54)),k4_xboole_0(k4_xboole_0(sK55,k1_tarski(sK54)),k4_xboole_0(k4_xboole_0(sK55,k1_tarski(sK54)),k1_tarski(sK54)))) != sK55 ),
    inference(definition_unfolding,[],[f1359,f1485])).

cnf(c_495,negated_conjecture,
    ( r2_hidden(sK54,sK55) ),
    inference(cnf_transformation,[],[f1358])).

cnf(c_17976,plain,
    ( r2_hidden(sK54,sK55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_563,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1844])).

cnf(c_559,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1423])).

cnf(c_3425,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_559])).

cnf(c_3426,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_3425])).

cnf(c_4138,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)) = k1_tarski(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_563,c_3426])).

cnf(c_17921,plain,
    ( k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1)) = k1_tarski(X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4138])).

cnf(c_30143,plain,
    ( k4_xboole_0(k1_tarski(sK54),k4_xboole_0(k1_tarski(sK54),sK55)) = k1_tarski(sK54) ),
    inference(superposition,[status(thm)],[c_17976,c_17921])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1496])).

cnf(c_31302,plain,
    ( k5_xboole_0(k1_tarski(sK54),k1_tarski(sK54)) = k4_xboole_0(k1_tarski(sK54),sK55) ),
    inference(superposition,[status(thm)],[c_30143,c_1])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1626])).

cnf(c_31317,plain,
    ( k4_xboole_0(k1_tarski(sK54),sK55) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_31302,c_212])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1499])).

cnf(c_31344,plain,
    ( k4_xboole_0(sK55,k4_xboole_0(sK55,k1_tarski(sK54))) = k4_xboole_0(k1_tarski(sK54),o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_31317,c_6])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1580])).

cnf(c_31357,plain,
    ( k4_xboole_0(sK55,k4_xboole_0(sK55,k1_tarski(sK54))) = k1_tarski(sK54) ),
    inference(demodulation,[status(thm)],[c_31344,c_145])).

cnf(c_33950,plain,
    ( k4_xboole_0(sK55,k1_tarski(sK54)) = k5_xboole_0(sK55,k1_tarski(sK54)) ),
    inference(superposition,[status(thm)],[c_31357,c_1])).

cnf(c_33957,plain,
    ( k4_xboole_0(sK55,k5_xboole_0(sK55,k1_tarski(sK54))) = k1_tarski(sK54) ),
    inference(demodulation,[status(thm)],[c_33950,c_31357])).

cnf(c_155,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f1590])).

cnf(c_31326,plain,
    ( k4_xboole_0(k1_tarski(sK54),k4_xboole_0(k1_tarski(sK54),k4_xboole_0(sK55,X0))) = k4_xboole_0(k4_xboole_0(k1_tarski(sK54),o_0_0_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_31317,c_155])).

cnf(c_31387,plain,
    ( k4_xboole_0(k1_tarski(sK54),k4_xboole_0(k1_tarski(sK54),k4_xboole_0(sK55,X0))) = k4_xboole_0(k1_tarski(sK54),X0) ),
    inference(demodulation,[status(thm)],[c_31326,c_145])).

cnf(c_44195,plain,
    ( k4_xboole_0(k1_tarski(sK54),k4_xboole_0(k1_tarski(sK54),k1_tarski(sK54))) = k4_xboole_0(k1_tarski(sK54),k5_xboole_0(sK55,k1_tarski(sK54))) ),
    inference(superposition,[status(thm)],[c_33957,c_31387])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1572])).

cnf(c_18348,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_44197,plain,
    ( k4_xboole_0(k1_tarski(sK54),k5_xboole_0(sK55,k1_tarski(sK54))) = k1_tarski(sK54) ),
    inference(demodulation,[status(thm)],[c_44195,c_145,c_18348])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1629])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1064])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f856])).

cnf(c_10546,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_58252,plain,
    ( k5_xboole_0(k1_tarski(sK54),k5_xboole_0(k5_xboole_0(sK55,k1_tarski(sK54)),k4_xboole_0(k1_tarski(sK54),k1_tarski(sK54)))) = k5_xboole_0(k1_tarski(sK54),k4_xboole_0(k5_xboole_0(sK55,k1_tarski(sK54)),k1_tarski(sK54))) ),
    inference(superposition,[status(thm)],[c_44197,c_10546])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1599])).

cnf(c_31334,plain,
    ( k5_xboole_0(k1_tarski(sK54),k5_xboole_0(sK55,k4_xboole_0(k1_tarski(sK54),o_0_0_xboole_0))) = k5_xboole_0(k1_tarski(sK54),k4_xboole_0(sK55,k1_tarski(sK54))) ),
    inference(superposition,[status(thm)],[c_31317,c_10546])).

cnf(c_23241,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_212,c_211])).

cnf(c_22207,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_168,c_7])).

cnf(c_23272,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_23241,c_22207])).

cnf(c_23852,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_7,c_23272])).

cnf(c_31376,plain,
    ( k5_xboole_0(k1_tarski(sK54),k4_xboole_0(sK55,k1_tarski(sK54))) = sK55 ),
    inference(demodulation,[status(thm)],[c_31334,c_145,c_23852])).

cnf(c_33968,plain,
    ( k5_xboole_0(k1_tarski(sK54),k5_xboole_0(k4_xboole_0(sK55,k1_tarski(sK54)),X0)) = k5_xboole_0(sK55,X0) ),
    inference(superposition,[status(thm)],[c_31376,c_211])).

cnf(c_56914,plain,
    ( k5_xboole_0(k1_tarski(sK54),k5_xboole_0(k5_xboole_0(sK55,k1_tarski(sK54)),X0)) = k5_xboole_0(sK55,X0) ),
    inference(light_normalisation,[status(thm)],[c_33968,c_33950])).

cnf(c_58311,plain,
    ( k5_xboole_0(k1_tarski(sK54),k4_xboole_0(k5_xboole_0(sK55,k1_tarski(sK54)),k1_tarski(sK54))) = sK55 ),
    inference(demodulation,[status(thm)],[c_58252,c_168,c_18348,c_56914])).

cnf(c_494,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK55,k1_tarski(sK54)),k1_tarski(sK54)),k4_xboole_0(k4_xboole_0(sK55,k1_tarski(sK54)),k4_xboole_0(k4_xboole_0(sK55,k1_tarski(sK54)),k1_tarski(sK54)))) != sK55 ),
    inference(cnf_transformation,[],[f1794])).

cnf(c_10429,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK54),k5_xboole_0(k4_xboole_0(sK55,k1_tarski(sK54)),k4_xboole_0(k4_xboole_0(sK55,k1_tarski(sK54)),k4_xboole_0(k4_xboole_0(sK55,k1_tarski(sK54)),k1_tarski(sK54))))) != sK55 ),
    inference(theory_normalisation,[status(thm)],[c_494,c_211,c_7])).

cnf(c_19350,plain,
    ( k5_xboole_0(k1_tarski(sK54),k4_xboole_0(k4_xboole_0(sK55,k1_tarski(sK54)),k1_tarski(sK54))) != sK55 ),
    inference(demodulation,[status(thm)],[c_10429,c_1])).

cnf(c_43219,plain,
    ( k5_xboole_0(k1_tarski(sK54),k4_xboole_0(k5_xboole_0(sK55,k1_tarski(sK54)),k1_tarski(sK54))) != sK55 ),
    inference(demodulation,[status(thm)],[c_33950,c_19350])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_58311,c_43219])).

%------------------------------------------------------------------------------
