%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:47 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 127 expanded)
%              Number of clauses        :   31 (  42 expanded)
%              Number of leaves         :   12 (  31 expanded)
%              Depth                    :   15
%              Number of atoms          :  201 ( 311 expanded)
%              Number of equality atoms :   52 (  91 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK2,sK4)
        | ~ r1_tarski(sK2,sK3) )
      & r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ( ~ r1_xboole_0(sK2,sK4)
      | ~ r1_tarski(sK2,sK3) )
    & r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f23])).

fof(f40,plain,(
    r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f50,plain,(
    r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
    inference(definition_unfolding,[],[f40,f35])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f39,f35,f35])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f38,f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f21])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f27,f35])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f41,plain,
    ( ~ r1_xboole_0(sK2,sK4)
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_12231,plain,
    ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12338,plain,
    ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_12231])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12234,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12418,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) = sK2 ),
    inference(superposition,[status(thm)],[c_12338,c_12234])).

cnf(c_13,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_12,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12233,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_12366,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_12233])).

cnf(c_14218,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_12366])).

cnf(c_17091,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12418,c_14218])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12235,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12785,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_12235])).

cnf(c_28358,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_17091,c_12785])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_12237,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_12236,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_12240,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_12430,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top
    | r2_hidden(sK1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12236,c_12240])).

cnf(c_12521,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_12237,c_12430])).

cnf(c_12659,plain,
    ( r1_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_12521])).

cnf(c_12872,plain,
    ( r1_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_12659])).

cnf(c_13342,plain,
    ( r1_xboole_0(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_12418,c_12872])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r1_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,plain,
    ( r1_tarski(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28358,c_13342,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:21:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.81/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.81/1.50  
% 7.81/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.81/1.50  
% 7.81/1.50  ------  iProver source info
% 7.81/1.50  
% 7.81/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.81/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.81/1.50  git: non_committed_changes: false
% 7.81/1.50  git: last_make_outside_of_git: false
% 7.81/1.50  
% 7.81/1.50  ------ 
% 7.81/1.50  ------ Parsing...
% 7.81/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.81/1.50  
% 7.81/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.81/1.50  
% 7.81/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.81/1.50  
% 7.81/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.50  ------ Proving...
% 7.81/1.50  ------ Problem Properties 
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  clauses                                 16
% 7.81/1.50  conjectures                             4
% 7.81/1.50  EPR                                     2
% 7.81/1.50  Horn                                    10
% 7.81/1.50  unary                                   4
% 7.81/1.50  binary                                  7
% 7.81/1.50  lits                                    34
% 7.81/1.50  lits eq                                 6
% 7.81/1.50  fd_pure                                 0
% 7.81/1.50  fd_pseudo                               0
% 7.81/1.50  fd_cond                                 0
% 7.81/1.50  fd_pseudo_cond                          3
% 7.81/1.50  AC symbols                              0
% 7.81/1.50  
% 7.81/1.50  ------ Input Options Time Limit: Unbounded
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.81/1.50  Current options:
% 7.81/1.50  ------ 
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  ------ Proving...
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  ------ Preprocessing... sf_s  rm: 11 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.50  
% 7.81/1.50  ------ Proving...
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  ------ Preprocessing...
% 7.81/1.50  
% 7.81/1.50  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.50  
% 7.81/1.50  ------ Proving...
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.50  
% 7.81/1.50  ------ Proving...
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.50  
% 7.81/1.50  ------ Proving...
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.81/1.50  
% 7.81/1.50  ------ Proving...
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.50  
% 7.81/1.50  ------ Proving...
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.81/1.50  
% 7.81/1.50  ------ Proving...
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.50  
% 7.81/1.50  ------ Proving...
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.81/1.50  
% 7.81/1.50  ------ Proving...
% 7.81/1.50  
% 7.81/1.50  
% 7.81/1.50  % SZS status Theorem for theBenchmark.p
% 7.81/1.50  
% 7.81/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.81/1.50  
% 7.81/1.50  fof(f1,axiom,(
% 7.81/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.81/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.50  
% 7.81/1.50  fof(f25,plain,(
% 7.81/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.81/1.50    inference(cnf_transformation,[],[f1])).
% 7.81/1.50  
% 7.81/1.50  fof(f9,conjecture,(
% 7.81/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.81/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.50  
% 7.81/1.50  fof(f10,negated_conjecture,(
% 7.81/1.50    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.81/1.50    inference(negated_conjecture,[],[f9])).
% 7.81/1.50  
% 7.81/1.50  fof(f15,plain,(
% 7.81/1.50    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 7.81/1.50    inference(ennf_transformation,[],[f10])).
% 7.81/1.50  
% 7.81/1.50  fof(f23,plain,(
% 7.81/1.50    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)) & r1_tarski(sK2,k4_xboole_0(sK3,sK4)))),
% 7.81/1.50    introduced(choice_axiom,[])).
% 7.81/1.50  
% 7.81/1.50  fof(f24,plain,(
% 7.81/1.50    (~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)) & r1_tarski(sK2,k4_xboole_0(sK3,sK4))),
% 7.81/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f23])).
% 7.81/1.50  
% 7.81/1.50  fof(f40,plain,(
% 7.81/1.50    r1_tarski(sK2,k4_xboole_0(sK3,sK4))),
% 7.81/1.50    inference(cnf_transformation,[],[f24])).
% 7.81/1.50  
% 7.81/1.50  fof(f4,axiom,(
% 7.81/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.81/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.50  
% 7.81/1.50  fof(f35,plain,(
% 7.81/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.81/1.50    inference(cnf_transformation,[],[f4])).
% 7.81/1.50  
% 7.81/1.50  fof(f50,plain,(
% 7.81/1.50    r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)))),
% 7.81/1.50    inference(definition_unfolding,[],[f40,f35])).
% 7.81/1.50  
% 7.81/1.50  fof(f6,axiom,(
% 7.81/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.81/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.51  
% 7.81/1.51  fof(f14,plain,(
% 7.81/1.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.81/1.51    inference(ennf_transformation,[],[f6])).
% 7.81/1.51  
% 7.81/1.51  fof(f37,plain,(
% 7.81/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.81/1.51    inference(cnf_transformation,[],[f14])).
% 7.81/1.51  
% 7.81/1.51  fof(f8,axiom,(
% 7.81/1.51    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.81/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.51  
% 7.81/1.51  fof(f39,plain,(
% 7.81/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.81/1.51    inference(cnf_transformation,[],[f8])).
% 7.81/1.51  
% 7.81/1.51  fof(f49,plain,(
% 7.81/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 7.81/1.51    inference(definition_unfolding,[],[f39,f35,f35])).
% 7.81/1.51  
% 7.81/1.51  fof(f7,axiom,(
% 7.81/1.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.81/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.51  
% 7.81/1.51  fof(f38,plain,(
% 7.81/1.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.81/1.51    inference(cnf_transformation,[],[f7])).
% 7.81/1.51  
% 7.81/1.51  fof(f48,plain,(
% 7.81/1.51    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 7.81/1.51    inference(definition_unfolding,[],[f38,f35])).
% 7.81/1.51  
% 7.81/1.51  fof(f5,axiom,(
% 7.81/1.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 7.81/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.51  
% 7.81/1.51  fof(f13,plain,(
% 7.81/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 7.81/1.51    inference(ennf_transformation,[],[f5])).
% 7.81/1.51  
% 7.81/1.51  fof(f36,plain,(
% 7.81/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 7.81/1.51    inference(cnf_transformation,[],[f13])).
% 7.81/1.51  
% 7.81/1.51  fof(f3,axiom,(
% 7.81/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.81/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.51  
% 7.81/1.51  fof(f11,plain,(
% 7.81/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.81/1.51    inference(rectify,[],[f3])).
% 7.81/1.51  
% 7.81/1.51  fof(f12,plain,(
% 7.81/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.81/1.51    inference(ennf_transformation,[],[f11])).
% 7.81/1.51  
% 7.81/1.51  fof(f21,plain,(
% 7.81/1.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.81/1.51    introduced(choice_axiom,[])).
% 7.81/1.51  
% 7.81/1.51  fof(f22,plain,(
% 7.81/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.81/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f21])).
% 7.81/1.51  
% 7.81/1.51  fof(f33,plain,(
% 7.81/1.51    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.81/1.51    inference(cnf_transformation,[],[f22])).
% 7.81/1.51  
% 7.81/1.51  fof(f32,plain,(
% 7.81/1.51    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.81/1.51    inference(cnf_transformation,[],[f22])).
% 7.81/1.51  
% 7.81/1.51  fof(f2,axiom,(
% 7.81/1.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.81/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.81/1.51  
% 7.81/1.51  fof(f16,plain,(
% 7.81/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.81/1.51    inference(nnf_transformation,[],[f2])).
% 7.81/1.51  
% 7.81/1.51  fof(f17,plain,(
% 7.81/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.81/1.51    inference(flattening,[],[f16])).
% 7.81/1.51  
% 7.81/1.51  fof(f18,plain,(
% 7.81/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.81/1.51    inference(rectify,[],[f17])).
% 7.81/1.51  
% 7.81/1.51  fof(f19,plain,(
% 7.81/1.51    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.81/1.51    introduced(choice_axiom,[])).
% 7.81/1.51  
% 7.81/1.51  fof(f20,plain,(
% 7.81/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.81/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 7.81/1.51  
% 7.81/1.51  fof(f27,plain,(
% 7.81/1.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.81/1.51    inference(cnf_transformation,[],[f20])).
% 7.81/1.51  
% 7.81/1.51  fof(f46,plain,(
% 7.81/1.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.81/1.51    inference(definition_unfolding,[],[f27,f35])).
% 7.81/1.51  
% 7.81/1.51  fof(f52,plain,(
% 7.81/1.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.81/1.51    inference(equality_resolution,[],[f46])).
% 7.81/1.51  
% 7.81/1.51  fof(f41,plain,(
% 7.81/1.51    ~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)),
% 7.81/1.51    inference(cnf_transformation,[],[f24])).
% 7.81/1.51  
% 7.81/1.51  cnf(c_0,plain,
% 7.81/1.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.81/1.51      inference(cnf_transformation,[],[f25]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_15,negated_conjecture,
% 7.81/1.51      ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
% 7.81/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_12231,plain,
% 7.81/1.51      ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) = iProver_top ),
% 7.81/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_12338,plain,
% 7.81/1.51      ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) = iProver_top ),
% 7.81/1.51      inference(demodulation,[status(thm)],[c_0,c_12231]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_11,plain,
% 7.81/1.51      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.81/1.51      inference(cnf_transformation,[],[f37]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_12234,plain,
% 7.81/1.51      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.81/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_12418,plain,
% 7.81/1.51      ( k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) = sK2 ),
% 7.81/1.51      inference(superposition,[status(thm)],[c_12338,c_12234]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_13,plain,
% 7.81/1.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.81/1.51      inference(cnf_transformation,[],[f49]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_12,plain,
% 7.81/1.51      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 7.81/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_12233,plain,
% 7.81/1.51      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 7.81/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_12366,plain,
% 7.81/1.51      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
% 7.81/1.51      inference(superposition,[status(thm)],[c_13,c_12233]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_14218,plain,
% 7.81/1.51      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X0,X1)) = iProver_top ),
% 7.81/1.51      inference(superposition,[status(thm)],[c_0,c_12366]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_17091,plain,
% 7.81/1.51      ( r1_tarski(sK2,k3_xboole_0(sK2,sK3)) = iProver_top ),
% 7.81/1.51      inference(superposition,[status(thm)],[c_12418,c_14218]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_10,plain,
% 7.81/1.51      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 7.81/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_12235,plain,
% 7.81/1.51      ( r1_tarski(X0,X1) = iProver_top
% 7.81/1.51      | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 7.81/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_12785,plain,
% 7.81/1.51      ( r1_tarski(X0,X1) = iProver_top
% 7.81/1.51      | r1_tarski(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 7.81/1.51      inference(superposition,[status(thm)],[c_0,c_12235]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_28358,plain,
% 7.81/1.51      ( r1_tarski(sK2,sK3) = iProver_top ),
% 7.81/1.51      inference(superposition,[status(thm)],[c_17091,c_12785]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_8,plain,
% 7.81/1.51      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 7.81/1.51      inference(cnf_transformation,[],[f33]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_12237,plain,
% 7.81/1.51      ( r1_xboole_0(X0,X1) = iProver_top
% 7.81/1.51      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 7.81/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_9,plain,
% 7.81/1.51      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.81/1.51      inference(cnf_transformation,[],[f32]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_12236,plain,
% 7.81/1.51      ( r1_xboole_0(X0,X1) = iProver_top
% 7.81/1.51      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 7.81/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_5,negated_conjecture,
% 7.81/1.51      ( ~ r2_hidden(X0,X1)
% 7.81/1.51      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 7.81/1.51      inference(cnf_transformation,[],[f52]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_12240,plain,
% 7.81/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.81/1.51      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 7.81/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_12430,plain,
% 7.81/1.51      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top
% 7.81/1.51      | r2_hidden(sK1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1) != iProver_top ),
% 7.81/1.51      inference(superposition,[status(thm)],[c_12236,c_12240]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_12521,plain,
% 7.81/1.51      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 7.81/1.51      inference(superposition,[status(thm)],[c_12237,c_12430]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_12659,plain,
% 7.81/1.51      ( r1_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) = iProver_top ),
% 7.81/1.51      inference(superposition,[status(thm)],[c_13,c_12521]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_12872,plain,
% 7.81/1.51      ( r1_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),X2) = iProver_top ),
% 7.81/1.51      inference(superposition,[status(thm)],[c_0,c_12659]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_13342,plain,
% 7.81/1.51      ( r1_xboole_0(sK2,sK4) = iProver_top ),
% 7.81/1.51      inference(superposition,[status(thm)],[c_12418,c_12872]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_14,negated_conjecture,
% 7.81/1.51      ( ~ r1_tarski(sK2,sK3) | ~ r1_xboole_0(sK2,sK4) ),
% 7.81/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(c_17,plain,
% 7.81/1.51      ( r1_tarski(sK2,sK3) != iProver_top
% 7.81/1.51      | r1_xboole_0(sK2,sK4) != iProver_top ),
% 7.81/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.81/1.51  
% 7.81/1.51  cnf(contradiction,plain,
% 7.81/1.51      ( $false ),
% 7.81/1.51      inference(minisat,[status(thm)],[c_28358,c_13342,c_17]) ).
% 7.81/1.51  
% 7.81/1.51  
% 7.81/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.81/1.51  
% 7.81/1.51  ------                               Statistics
% 7.81/1.51  
% 7.81/1.51  ------ Selected
% 7.81/1.51  
% 7.81/1.51  total_time:                             0.677
% 7.81/1.51  
%------------------------------------------------------------------------------
