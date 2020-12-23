%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0231+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:29 EST 2020

% Result     : Theorem 14.81s
% Output     : CNFRefutation 14.81s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 399 expanded)
%              Number of clauses        :   46 ( 112 expanded)
%              Number of leaves         :   20 ( 107 expanded)
%              Depth                    :   23
%              Number of atoms          :  214 ( 698 expanded)
%              Number of equality atoms :  157 ( 512 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f568,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f309])).

fof(f979,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f568])).

fof(f315,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f316,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f315])).

fof(f452,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f316])).

fof(f569,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( sK28 != sK30
      & r1_tarski(k2_tarski(sK28,sK29),k1_tarski(sK30)) ) ),
    introduced(choice_axiom,[])).

fof(f570,plain,
    ( sK28 != sK30
    & r1_tarski(k2_tarski(sK28,sK29),k1_tarski(sK30)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28,sK29,sK30])],[f452,f569])).

fof(f985,plain,(
    r1_tarski(k2_tarski(sK28,sK29),k1_tarski(sK30)) ),
    inference(cnf_transformation,[],[f570])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f882,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f786,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f726,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f991,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f786,f726])).

fof(f992,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f882,f991])).

fof(f1266,plain,(
    r1_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)))),k1_tarski(sK30)) ),
    inference(definition_unfolding,[],[f985,f992])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f783,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f575,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f790,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f1135,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f790,f991])).

fof(f299,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f566,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f299])).

fof(f567,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f566])).

fof(f966,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f567])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f578,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1254,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(definition_unfolding,[],[f966,f578])).

fof(f168,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f788,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f168])).

fof(f986,plain,(
    sK28 != sK30 ),
    inference(cnf_transformation,[],[f570])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f527,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f175])).

fof(f528,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f527])).

fof(f529,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK20(X0,X1) != X0
          | ~ r2_hidden(sK20(X0,X1),X1) )
        & ( sK20(X0,X1) = X0
          | r2_hidden(sK20(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f530,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK20(X0,X1) != X0
            | ~ r2_hidden(sK20(X0,X1),X1) )
          & ( sK20(X0,X1) = X0
            | r2_hidden(sK20(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f528,f529])).

fof(f802,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f530])).

fof(f1293,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f802])).

fof(f297,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f563,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f297])).

fof(f960,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f563])).

fof(f1248,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(definition_unfolding,[],[f960,f578])).

fof(f97,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f520,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f97])).

fof(f713,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f520])).

fof(f1082,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f713,f578])).

fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f784,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f1132,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f784,f578])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f740,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f1105,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f740,f578])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f703,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f1078,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f703,f726,f578,f578])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f716,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f1086,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f716,f578])).

cnf(c_395,plain,
    ( X0 = X1
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_tarski(X1) ),
    inference(cnf_transformation,[],[f979])).

cnf(c_403,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)))),k1_tarski(sK30)) ),
    inference(cnf_transformation,[],[f1266])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f783])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f575])).

cnf(c_7441,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k1_tarski(sK28),k5_xboole_0(k1_tarski(sK29),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29))))),k1_tarski(sK30)) ),
    inference(theory_normalisation,[status(thm)],[c_403,c_211,c_7])).

cnf(c_12275,plain,
    ( r1_tarski(k5_xboole_0(k1_tarski(sK28),k5_xboole_0(k1_tarski(sK29),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29))))),k1_tarski(sK30)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7441])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1135])).

cnf(c_7549,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_12532,plain,
    ( r1_tarski(k5_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK28))),k1_tarski(sK30)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12275,c_7549])).

cnf(c_22602,plain,
    ( sK29 = sK28
    | r1_tarski(k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)),k1_tarski(sK30)) = iProver_top ),
    inference(superposition,[status(thm)],[c_395,c_12532])).

cnf(c_385,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1254])).

cnf(c_12281,plain,
    ( k1_tarski(X0) = X1
    | o_0_0_xboole_0 = X1
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_27312,plain,
    ( k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) = k1_tarski(sK30)
    | k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) = o_0_0_xboole_0
    | sK29 = sK28 ),
    inference(superposition,[status(thm)],[c_22602,c_12281])).

cnf(c_215,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f788])).

cnf(c_12363,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_26646,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_12363])).

cnf(c_31640,plain,
    ( k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) = o_0_0_xboole_0
    | sK29 = sK28
    | r1_tarski(k4_xboole_0(k1_tarski(sK29),k1_tarski(sK28)),k1_tarski(sK30)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27312,c_26646])).

cnf(c_402,negated_conjecture,
    ( sK28 != sK30 ),
    inference(cnf_transformation,[],[f986])).

cnf(c_232,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f1293])).

cnf(c_13145,plain,
    ( ~ r2_hidden(sK28,k1_tarski(sK30))
    | sK28 = sK30 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_378,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1248])).

cnf(c_13711,plain,
    ( r2_hidden(sK28,k1_tarski(sK30))
    | k4_xboole_0(k1_tarski(sK28),k1_tarski(sK30)) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_378])).

cnf(c_141,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1082])).

cnf(c_20667,plain,
    ( ~ r1_tarski(k1_tarski(sK28),k1_tarski(sK30))
    | k4_xboole_0(k1_tarski(sK28),k1_tarski(sK30)) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_141])).

cnf(c_20668,plain,
    ( k4_xboole_0(k1_tarski(sK28),k1_tarski(sK30)) = o_0_0_xboole_0
    | r1_tarski(k1_tarski(sK28),k1_tarski(sK30)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20667])).

cnf(c_29692,plain,
    ( k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) = o_0_0_xboole_0
    | sK29 = sK28
    | r1_tarski(k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)),k1_tarski(sK30)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27312,c_12363])).

cnf(c_33847,plain,
    ( k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) = o_0_0_xboole_0
    | sK29 = sK28
    | r1_tarski(k1_tarski(sK28),k1_tarski(sK30)) = iProver_top ),
    inference(superposition,[status(thm)],[c_395,c_29692])).

cnf(c_35776,plain,
    ( sK29 = sK28
    | k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_31640,c_402,c_13145,c_13711,c_20668,c_33847])).

cnf(c_35777,plain,
    ( k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)) = o_0_0_xboole_0
    | sK29 = sK28 ),
    inference(renaming,[status(thm)],[c_35776])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1132])).

cnf(c_20851,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_212,c_211])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1105])).

cnf(c_17012,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_168])).

cnf(c_20860,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_20851,c_17012])).

cnf(c_25746,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_7,c_20860])).

cnf(c_35784,plain,
    ( k5_xboole_0(k1_tarski(sK29),o_0_0_xboole_0) = k1_tarski(sK28)
    | sK29 = sK28 ),
    inference(superposition,[status(thm)],[c_35777,c_25746])).

cnf(c_35787,plain,
    ( k1_tarski(sK29) = k1_tarski(sK28)
    | sK29 = sK28 ),
    inference(demodulation,[status(thm)],[c_35784,c_168])).

cnf(c_37167,plain,
    ( sK29 = sK28
    | r1_tarski(k5_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK28))),k1_tarski(sK30)) = iProver_top ),
    inference(superposition,[status(thm)],[c_35787,c_12532])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1078])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1086])).

cnf(c_12513,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_37168,plain,
    ( sK29 = sK28
    | r1_tarski(k1_tarski(sK28),k1_tarski(sK30)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_37167,c_168,c_12513])).

cnf(c_37604,plain,
    ( sK29 = sK28 ),
    inference(global_propositional_subsumption,[status(thm)],[c_37168,c_402,c_13145,c_13711,c_20668])).

cnf(c_37622,plain,
    ( r1_tarski(k5_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK28))),k1_tarski(sK30)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_37604,c_12532])).

cnf(c_37623,plain,
    ( r1_tarski(k1_tarski(sK28),k1_tarski(sK30)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_37622,c_168,c_12513])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37623,c_20668,c_13711,c_13145,c_402])).

%------------------------------------------------------------------------------
