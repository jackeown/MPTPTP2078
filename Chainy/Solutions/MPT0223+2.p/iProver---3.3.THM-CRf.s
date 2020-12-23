%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0223+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:28 EST 2020

% Result     : Theorem 11.18s
% Output     : CNFRefutation 11.18s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 420 expanded)
%              Number of clauses        :   36 ( 102 expanded)
%              Number of leaves         :   16 ( 128 expanded)
%              Depth                    :   22
%              Number of atoms          :   95 ( 494 expanded)
%              Number of equality atoms :   85 ( 484 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f306,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f435,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f306])).

fof(f947,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f435])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f680,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f703,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f555,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1037,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f680,f703,f555,f555])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f693,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f1045,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f693,f555])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f551,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f964,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f551,f703,f703])).

fof(f302,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f303,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f302])).

fof(f434,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f303])).

fof(f546,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK28 != sK29
      & k3_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) = k1_tarski(sK28) ) ),
    introduced(choice_axiom,[])).

fof(f547,plain,
    ( sK28 != sK29
    & k3_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) = k1_tarski(sK28) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28,sK29])],[f434,f546])).

fof(f943,plain,(
    k3_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) = k1_tarski(sK28) ),
    inference(cnf_transformation,[],[f547])).

fof(f1211,plain,(
    k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29))) = k1_tarski(sK28) ),
    inference(definition_unfolding,[],[f943,f703])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f630,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f961,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f630,f703])).

fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f761,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f1091,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f761,f555])).

fof(f60,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f648,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f60])).

fof(f1006,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f648,f703,f703,f703])).

fof(f111,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f704,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

fof(f1055,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f704,f703,f703])).

fof(f114,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f707,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f114])).

fof(f1058,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f707,f703,f703,f703])).

fof(f96,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f688,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f96])).

fof(f944,plain,(
    sK28 != sK29 ),
    inference(cnf_transformation,[],[f547])).

cnf(c_387,plain,
    ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f947])).

cnf(c_26629,plain,
    ( ~ r1_tarski(k1_tarski(sK28),k1_tarski(sK29))
    | sK29 = sK28 ),
    inference(instantiation,[status(thm)],[c_387])).

cnf(c_7322,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_21203,plain,
    ( sK28 = sK28 ),
    inference(instantiation,[status(thm)],[c_7322])).

cnf(c_7323,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_14876,plain,
    ( sK29 != X0
    | sK28 != X0
    | sK28 = sK29 ),
    inference(instantiation,[status(thm)],[c_7323])).

cnf(c_21202,plain,
    ( sK29 != sK28
    | sK28 = sK29
    | sK28 != sK28 ),
    inference(instantiation,[status(thm)],[c_14876])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1037])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1045])).

cnf(c_12492,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f964])).

cnf(c_384,negated_conjecture,
    ( k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29))) = k1_tarski(sK28) ),
    inference(cnf_transformation,[],[f1211])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f961])).

cnf(c_14740,plain,
    ( k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) = k5_xboole_0(k1_tarski(sK28),k1_tarski(sK28)) ),
    inference(superposition,[status(thm)],[c_384,c_1])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1091])).

cnf(c_14754,plain,
    ( k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14740,c_212])).

cnf(c_100,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(cnf_transformation,[],[f1006])).

cnf(c_16193,plain,
    ( k4_xboole_0(k4_xboole_0(k1_tarski(sK28),X0),k4_xboole_0(k4_xboole_0(k1_tarski(sK28),X0),k1_tarski(sK29))) = k4_xboole_0(k4_xboole_0(k1_tarski(sK28),o_0_0_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK29)))) ),
    inference(superposition,[status(thm)],[c_14754,c_100])).

cnf(c_16356,plain,
    ( k4_xboole_0(k4_xboole_0(k1_tarski(sK28),X0),k4_xboole_0(k4_xboole_0(k1_tarski(sK28),X0),k1_tarski(sK29))) = k4_xboole_0(k1_tarski(sK28),k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK29)))) ),
    inference(demodulation,[status(thm)],[c_16193,c_145])).

cnf(c_17779,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK28))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK28))),k1_tarski(sK29))) = k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k4_xboole_0(k1_tarski(sK28),X0),k4_xboole_0(k4_xboole_0(k1_tarski(sK28),X0),k1_tarski(sK29)))) ),
    inference(superposition,[status(thm)],[c_6,c_16356])).

cnf(c_17872,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK28))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK28))),k1_tarski(sK29))) = k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK29))))) ),
    inference(light_normalisation,[status(thm)],[c_17779,c_16356])).

cnf(c_155,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f1055])).

cnf(c_158,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f1058])).

cnf(c_17874,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29))))) = k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK29))))) ),
    inference(demodulation,[status(thm)],[c_17872,c_155,c_158])).

cnf(c_17875,plain,
    ( k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK29))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_tarski(sK28),o_0_0_xboole_0))) ),
    inference(light_normalisation,[status(thm)],[c_17874,c_14754])).

cnf(c_17876,plain,
    ( k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK29))))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(sK28))) ),
    inference(demodulation,[status(thm)],[c_17875,c_145])).

cnf(c_17943,plain,
    ( k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK29),o_0_0_xboole_0))) = k4_xboole_0(k1_tarski(sK29),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK28))) ),
    inference(superposition,[status(thm)],[c_12492,c_17876])).

cnf(c_18168,plain,
    ( k4_xboole_0(k1_tarski(sK29),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK28))) = k1_tarski(sK28) ),
    inference(demodulation,[status(thm)],[c_17943,c_145,c_14754])).

cnf(c_18267,plain,
    ( k4_xboole_0(k1_tarski(sK29),k1_tarski(sK28)) = k5_xboole_0(k1_tarski(sK29),k1_tarski(sK28)) ),
    inference(superposition,[status(thm)],[c_18168,c_1])).

cnf(c_18295,plain,
    ( k4_xboole_0(k1_tarski(sK29),k5_xboole_0(k1_tarski(sK29),k1_tarski(sK28))) = k1_tarski(sK28) ),
    inference(demodulation,[status(thm)],[c_18267,c_18168])).

cnf(c_140,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f688])).

cnf(c_12345,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_19760,plain,
    ( r1_tarski(k1_tarski(sK28),k1_tarski(sK29)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18295,c_12345])).

cnf(c_19803,plain,
    ( r1_tarski(k1_tarski(sK28),k1_tarski(sK29)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19760])).

cnf(c_383,negated_conjecture,
    ( sK28 != sK29 ),
    inference(cnf_transformation,[],[f944])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26629,c_21203,c_21202,c_19803,c_383])).

%------------------------------------------------------------------------------
