%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0230+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:29 EST 2020

% Result     : Theorem 7.83s
% Output     : CNFRefutation 7.83s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 152 expanded)
%              Number of clauses        :   32 (  42 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :   19
%              Number of atoms          :  140 ( 260 expanded)
%              Number of equality atoms :   88 ( 182 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f566,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f309])).

fof(f977,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f566])).

fof(f314,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f315,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f314])).

fof(f450,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f315])).

fof(f567,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK28 != sK30
      & sK28 != sK29
      & r1_tarski(k1_tarski(sK28),k2_tarski(sK29,sK30)) ) ),
    introduced(choice_axiom,[])).

fof(f568,plain,
    ( sK28 != sK30
    & sK28 != sK29
    & r1_tarski(k1_tarski(sK28),k2_tarski(sK29,sK30)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28,sK29,sK30])],[f450,f567])).

fof(f982,plain,(
    r1_tarski(k1_tarski(sK28),k2_tarski(sK29,sK30)) ),
    inference(cnf_transformation,[],[f568])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f880,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f784,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f724,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f989,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f784,f724])).

fof(f990,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f880,f989])).

fof(f1263,plain,(
    r1_tarski(k1_tarski(sK28),k5_xboole_0(k5_xboole_0(k1_tarski(sK29),k1_tarski(sK30)),k4_xboole_0(k1_tarski(sK29),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK30))))) ),
    inference(definition_unfolding,[],[f982,f990])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f781,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f573,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f651,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f1000,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f651,f724])).

fof(f55,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f512,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f513,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f512])).

fof(f662,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f513])).

fof(f1042,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f662,f989])).

fof(f105,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f381,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f105])).

fof(f719,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f381])).

fof(f1089,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ) ),
    inference(definition_unfolding,[],[f719,f989])).

fof(f317,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f451,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f317])).

fof(f986,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f451])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f738,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f576,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1103,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f738,f576])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f701,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f1076,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f701,f724,f576,f576])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f714,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f1084,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f714,f576])).

fof(f983,plain,(
    sK28 != sK29 ),
    inference(cnf_transformation,[],[f568])).

fof(f984,plain,(
    sK28 != sK30 ),
    inference(cnf_transformation,[],[f568])).

cnf(c_395,plain,
    ( X0 = X1
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_tarski(X1) ),
    inference(cnf_transformation,[],[f977])).

cnf(c_403,negated_conjecture,
    ( r1_tarski(k1_tarski(sK28),k5_xboole_0(k5_xboole_0(k1_tarski(sK29),k1_tarski(sK30)),k4_xboole_0(k1_tarski(sK29),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK30))))) ),
    inference(cnf_transformation,[],[f1263])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f781])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f573])).

cnf(c_4450,negated_conjecture,
    ( r1_tarski(k1_tarski(sK28),k5_xboole_0(k1_tarski(sK30),k5_xboole_0(k1_tarski(sK29),k4_xboole_0(k1_tarski(sK29),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK30)))))) ),
    inference(theory_normalisation,[status(thm)],[c_403,c_211,c_7])).

cnf(c_9268,plain,
    ( r1_tarski(k1_tarski(sK28),k5_xboole_0(k1_tarski(sK30),k5_xboole_0(k1_tarski(sK29),k4_xboole_0(k1_tarski(sK29),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK30)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4450])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1000])).

cnf(c_9977,plain,
    ( r1_tarski(k1_tarski(sK28),k5_xboole_0(k1_tarski(sK30),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK30)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9268,c_1])).

cnf(c_95,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,X2))
    | r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f1042])).

cnf(c_150,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1089])).

cnf(c_1859,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X2)
    | ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(prop_impl,[status(thm)],[c_150])).

cnf(c_1860,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(renaming,[status(thm)],[c_1859])).

cnf(c_2354,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(bin_hyper_res,[status(thm)],[c_95,c_1860])).

cnf(c_9266,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2354])).

cnf(c_11868,plain,
    ( r1_tarski(k4_xboole_0(k1_tarski(sK28),k1_tarski(sK30)),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK30))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9977,c_9266])).

cnf(c_13130,plain,
    ( sK29 = sK30
    | r1_tarski(k4_xboole_0(k1_tarski(sK28),k1_tarski(sK30)),k1_tarski(sK29)) = iProver_top ),
    inference(superposition,[status(thm)],[c_395,c_11868])).

cnf(c_13433,plain,
    ( sK29 = sK30
    | sK30 = sK28
    | r1_tarski(k1_tarski(sK28),k1_tarski(sK29)) = iProver_top ),
    inference(superposition,[status(thm)],[c_395,c_13130])).

cnf(c_405,plain,
    ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f986])).

cnf(c_9269,plain,
    ( X0 = X1
    | r1_tarski(k1_tarski(X1),k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_13537,plain,
    ( sK29 = sK30
    | sK29 = sK28
    | sK30 = sK28 ),
    inference(superposition,[status(thm)],[c_13433,c_9269])).

cnf(c_13546,plain,
    ( sK29 = sK28
    | sK30 = sK28
    | r1_tarski(k1_tarski(sK28),k5_xboole_0(k1_tarski(sK30),k4_xboole_0(k1_tarski(sK30),k1_tarski(sK30)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13537,c_9977])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1103])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1076])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1084])).

cnf(c_9549,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_13551,plain,
    ( sK29 = sK28
    | sK30 = sK28
    | r1_tarski(k1_tarski(sK28),k1_tarski(sK30)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13546,c_168,c_9549])).

cnf(c_13629,plain,
    ( sK29 = sK28
    | sK30 = sK28 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13551,c_9269])).

cnf(c_402,negated_conjecture,
    ( sK28 != sK29 ),
    inference(cnf_transformation,[],[f983])).

cnf(c_13638,plain,
    ( sK30 = sK28 ),
    inference(superposition,[status(thm)],[c_13629,c_402])).

cnf(c_401,negated_conjecture,
    ( sK28 != sK30 ),
    inference(cnf_transformation,[],[f984])).

cnf(c_13650,plain,
    ( sK28 != sK28 ),
    inference(demodulation,[status(thm)],[c_13638,c_401])).

cnf(c_13651,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_13650])).

%------------------------------------------------------------------------------
