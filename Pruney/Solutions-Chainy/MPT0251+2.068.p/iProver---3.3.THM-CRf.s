%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:13 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.32s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 144 expanded)
%              Number of clauses        :   23 (  27 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :  203 ( 425 expanded)
%              Number of equality atoms :   75 ( 161 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK2),sK3) != sK3
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k2_xboole_0(k1_tarski(sK2),sK3) != sK3
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f28])).

fof(f51,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f56])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f54])).

fof(f58,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f43,f55])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f30,f55,f55])).

fof(f52,plain,(
    k2_xboole_0(k1_tarski(sK2),sK3) != sK3 ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) != sK3 ),
    inference(definition_unfolding,[],[f52,f55,f56])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_690,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_692,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_699,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1661,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r2_hidden(sK1(X0,X1,X1),X1) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_699])).

cnf(c_1663,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r2_hidden(sK1(X0,X1,X1),X1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1661])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_701,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_16430,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r2_hidden(sK1(X0,X1,X1),X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_701])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_700,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_16440,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r2_hidden(sK1(X0,X1,X1),X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16430,c_700])).

cnf(c_16900,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16440,c_1663])).

cnf(c_16905,plain,
    ( k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k3_enumset1(X1,X1,X1,X1,X1)
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_692,c_16900])).

cnf(c_17532,plain,
    ( k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_690,c_16905])).

cnf(c_13,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_17675,plain,
    ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = sK3 ),
    inference(superposition,[status(thm)],[c_17532,c_13])).

cnf(c_0,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_16,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_791,plain,
    ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != sK3 ),
    inference(superposition,[status(thm)],[c_0,c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17675,c_791])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.32/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.32/1.49  
% 7.32/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.32/1.49  
% 7.32/1.49  ------  iProver source info
% 7.32/1.49  
% 7.32/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.32/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.32/1.49  git: non_committed_changes: false
% 7.32/1.49  git: last_make_outside_of_git: false
% 7.32/1.49  
% 7.32/1.49  ------ 
% 7.32/1.49  ------ Parsing...
% 7.32/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.32/1.49  
% 7.32/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.32/1.49  
% 7.32/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.32/1.49  
% 7.32/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.32/1.49  ------ Proving...
% 7.32/1.49  ------ Problem Properties 
% 7.32/1.49  
% 7.32/1.49  
% 7.32/1.49  clauses                                 17
% 7.32/1.49  conjectures                             2
% 7.32/1.49  EPR                                     4
% 7.32/1.49  Horn                                    14
% 7.32/1.49  unary                                   5
% 7.32/1.49  binary                                  6
% 7.32/1.49  lits                                    36
% 7.32/1.49  lits eq                                 7
% 7.32/1.49  fd_pure                                 0
% 7.32/1.49  fd_pseudo                               0
% 7.32/1.49  fd_cond                                 0
% 7.32/1.49  fd_pseudo_cond                          4
% 7.32/1.49  AC symbols                              0
% 7.32/1.49  
% 7.32/1.49  ------ Input Options Time Limit: Unbounded
% 7.32/1.49  
% 7.32/1.49  
% 7.32/1.49  ------ 
% 7.32/1.49  Current options:
% 7.32/1.49  ------ 
% 7.32/1.49  
% 7.32/1.49  
% 7.32/1.49  
% 7.32/1.49  
% 7.32/1.49  ------ Proving...
% 7.32/1.49  
% 7.32/1.49  
% 7.32/1.49  % SZS status Theorem for theBenchmark.p
% 7.32/1.49  
% 7.32/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.32/1.49  
% 7.32/1.49  fof(f12,conjecture,(
% 7.32/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 7.32/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f13,negated_conjecture,(
% 7.32/1.49    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 7.32/1.49    inference(negated_conjecture,[],[f12])).
% 7.32/1.49  
% 7.32/1.49  fof(f15,plain,(
% 7.32/1.49    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 7.32/1.49    inference(ennf_transformation,[],[f13])).
% 7.32/1.49  
% 7.32/1.49  fof(f28,plain,(
% 7.32/1.49    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK2),sK3) != sK3 & r2_hidden(sK2,sK3))),
% 7.32/1.49    introduced(choice_axiom,[])).
% 7.32/1.49  
% 7.32/1.49  fof(f29,plain,(
% 7.32/1.49    k2_xboole_0(k1_tarski(sK2),sK3) != sK3 & r2_hidden(sK2,sK3)),
% 7.32/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f28])).
% 7.32/1.49  
% 7.32/1.49  fof(f51,plain,(
% 7.32/1.49    r2_hidden(sK2,sK3)),
% 7.32/1.49    inference(cnf_transformation,[],[f29])).
% 7.32/1.49  
% 7.32/1.49  fof(f10,axiom,(
% 7.32/1.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.32/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f27,plain,(
% 7.32/1.49    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 7.32/1.49    inference(nnf_transformation,[],[f10])).
% 7.32/1.49  
% 7.32/1.49  fof(f49,plain,(
% 7.32/1.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.32/1.49    inference(cnf_transformation,[],[f27])).
% 7.32/1.49  
% 7.32/1.49  fof(f6,axiom,(
% 7.32/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.32/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.49  
% 7.32/1.49  fof(f44,plain,(
% 7.32/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.32/1.49    inference(cnf_transformation,[],[f6])).
% 7.32/1.49  
% 7.32/1.49  fof(f7,axiom,(
% 7.32/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.32/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f45,plain,(
% 7.32/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f7])).
% 7.32/1.50  
% 7.32/1.50  fof(f8,axiom,(
% 7.32/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.32/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f46,plain,(
% 7.32/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f8])).
% 7.32/1.50  
% 7.32/1.50  fof(f9,axiom,(
% 7.32/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.32/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f47,plain,(
% 7.32/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f9])).
% 7.32/1.50  
% 7.32/1.50  fof(f53,plain,(
% 7.32/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.32/1.50    inference(definition_unfolding,[],[f46,f47])).
% 7.32/1.50  
% 7.32/1.50  fof(f54,plain,(
% 7.32/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.32/1.50    inference(definition_unfolding,[],[f45,f53])).
% 7.32/1.50  
% 7.32/1.50  fof(f56,plain,(
% 7.32/1.50    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 7.32/1.50    inference(definition_unfolding,[],[f44,f54])).
% 7.32/1.50  
% 7.32/1.50  fof(f59,plain,(
% 7.32/1.50    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.32/1.50    inference(definition_unfolding,[],[f49,f56])).
% 7.32/1.50  
% 7.32/1.50  fof(f3,axiom,(
% 7.32/1.50    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.32/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f20,plain,(
% 7.32/1.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.32/1.50    inference(nnf_transformation,[],[f3])).
% 7.32/1.50  
% 7.32/1.50  fof(f21,plain,(
% 7.32/1.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.32/1.50    inference(flattening,[],[f20])).
% 7.32/1.50  
% 7.32/1.50  fof(f22,plain,(
% 7.32/1.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.32/1.50    inference(rectify,[],[f21])).
% 7.32/1.50  
% 7.32/1.50  fof(f23,plain,(
% 7.32/1.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.32/1.50    introduced(choice_axiom,[])).
% 7.32/1.50  
% 7.32/1.50  fof(f24,plain,(
% 7.32/1.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.32/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 7.32/1.50  
% 7.32/1.50  fof(f38,plain,(
% 7.32/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f24])).
% 7.32/1.50  
% 7.32/1.50  fof(f2,axiom,(
% 7.32/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.32/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f14,plain,(
% 7.32/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.32/1.50    inference(ennf_transformation,[],[f2])).
% 7.32/1.50  
% 7.32/1.50  fof(f16,plain,(
% 7.32/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.32/1.50    inference(nnf_transformation,[],[f14])).
% 7.32/1.50  
% 7.32/1.50  fof(f17,plain,(
% 7.32/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.32/1.50    inference(rectify,[],[f16])).
% 7.32/1.50  
% 7.32/1.50  fof(f18,plain,(
% 7.32/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.32/1.50    introduced(choice_axiom,[])).
% 7.32/1.50  
% 7.32/1.50  fof(f19,plain,(
% 7.32/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.32/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 7.32/1.50  
% 7.32/1.50  fof(f31,plain,(
% 7.32/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f19])).
% 7.32/1.50  
% 7.32/1.50  fof(f39,plain,(
% 7.32/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f24])).
% 7.32/1.50  
% 7.32/1.50  fof(f5,axiom,(
% 7.32/1.50    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 7.32/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f43,plain,(
% 7.32/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 7.32/1.50    inference(cnf_transformation,[],[f5])).
% 7.32/1.50  
% 7.32/1.50  fof(f11,axiom,(
% 7.32/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.32/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f50,plain,(
% 7.32/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.32/1.50    inference(cnf_transformation,[],[f11])).
% 7.32/1.50  
% 7.32/1.50  fof(f55,plain,(
% 7.32/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 7.32/1.50    inference(definition_unfolding,[],[f50,f54])).
% 7.32/1.50  
% 7.32/1.50  fof(f58,plain,(
% 7.32/1.50    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 7.32/1.50    inference(definition_unfolding,[],[f43,f55])).
% 7.32/1.50  
% 7.32/1.50  fof(f1,axiom,(
% 7.32/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.32/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f30,plain,(
% 7.32/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.32/1.50    inference(cnf_transformation,[],[f1])).
% 7.32/1.50  
% 7.32/1.50  fof(f57,plain,(
% 7.32/1.50    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 7.32/1.50    inference(definition_unfolding,[],[f30,f55,f55])).
% 7.32/1.50  
% 7.32/1.50  fof(f52,plain,(
% 7.32/1.50    k2_xboole_0(k1_tarski(sK2),sK3) != sK3),
% 7.32/1.50    inference(cnf_transformation,[],[f29])).
% 7.32/1.50  
% 7.32/1.50  fof(f61,plain,(
% 7.32/1.50    k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) != sK3),
% 7.32/1.50    inference(definition_unfolding,[],[f52,f55,f56])).
% 7.32/1.50  
% 7.32/1.50  cnf(c_17,negated_conjecture,
% 7.32/1.50      ( r2_hidden(sK2,sK3) ),
% 7.32/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_690,plain,
% 7.32/1.50      ( r2_hidden(sK2,sK3) = iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_14,plain,
% 7.32/1.50      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 7.32/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_692,plain,
% 7.32/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.32/1.50      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_5,plain,
% 7.32/1.50      ( r2_hidden(sK1(X0,X1,X2),X1)
% 7.32/1.50      | r2_hidden(sK1(X0,X1,X2),X2)
% 7.32/1.50      | k3_xboole_0(X0,X1) = X2 ),
% 7.32/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_699,plain,
% 7.32/1.50      ( k3_xboole_0(X0,X1) = X2
% 7.32/1.50      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 7.32/1.50      | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1661,plain,
% 7.32/1.50      ( k3_xboole_0(X0,X1) = X1
% 7.32/1.50      | r2_hidden(sK1(X0,X1,X1),X1) = iProver_top
% 7.32/1.50      | iProver_top != iProver_top ),
% 7.32/1.50      inference(equality_factoring,[status(thm)],[c_699]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_1663,plain,
% 7.32/1.50      ( k3_xboole_0(X0,X1) = X1
% 7.32/1.50      | r2_hidden(sK1(X0,X1,X1),X1) = iProver_top ),
% 7.32/1.50      inference(equality_resolution_simp,[status(thm)],[c_1661]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_3,plain,
% 7.32/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.32/1.50      inference(cnf_transformation,[],[f31]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_701,plain,
% 7.32/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.32/1.50      | r2_hidden(X0,X2) = iProver_top
% 7.32/1.50      | r1_tarski(X1,X2) != iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_16430,plain,
% 7.32/1.50      ( k3_xboole_0(X0,X1) = X1
% 7.32/1.50      | r2_hidden(sK1(X0,X1,X1),X2) = iProver_top
% 7.32/1.50      | r1_tarski(X1,X2) != iProver_top ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_1663,c_701]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_4,plain,
% 7.32/1.50      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 7.32/1.50      | ~ r2_hidden(sK1(X0,X1,X2),X0)
% 7.32/1.50      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 7.32/1.50      | k3_xboole_0(X0,X1) = X2 ),
% 7.32/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_700,plain,
% 7.32/1.50      ( k3_xboole_0(X0,X1) = X2
% 7.32/1.50      | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top
% 7.32/1.50      | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
% 7.32/1.50      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top ),
% 7.32/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_16440,plain,
% 7.32/1.50      ( k3_xboole_0(X0,X1) = X1
% 7.32/1.50      | r2_hidden(sK1(X0,X1,X1),X1) != iProver_top
% 7.32/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_16430,c_700]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_16900,plain,
% 7.32/1.50      ( k3_xboole_0(X0,X1) = X1 | r1_tarski(X1,X0) != iProver_top ),
% 7.32/1.50      inference(global_propositional_subsumption,
% 7.32/1.50                [status(thm)],
% 7.32/1.50                [c_16440,c_1663]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_16905,plain,
% 7.32/1.50      ( k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k3_enumset1(X1,X1,X1,X1,X1)
% 7.32/1.50      | r2_hidden(X1,X0) != iProver_top ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_692,c_16900]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_17532,plain,
% 7.32/1.50      ( k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_690,c_16905]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_13,plain,
% 7.32/1.50      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
% 7.32/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_17675,plain,
% 7.32/1.50      ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = sK3 ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_17532,c_13]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_0,plain,
% 7.32/1.50      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
% 7.32/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_16,negated_conjecture,
% 7.32/1.50      ( k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) != sK3 ),
% 7.32/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(c_791,plain,
% 7.32/1.50      ( k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) != sK3 ),
% 7.32/1.50      inference(superposition,[status(thm)],[c_0,c_16]) ).
% 7.32/1.50  
% 7.32/1.50  cnf(contradiction,plain,
% 7.32/1.50      ( $false ),
% 7.32/1.50      inference(minisat,[status(thm)],[c_17675,c_791]) ).
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.32/1.50  
% 7.32/1.50  ------                               Statistics
% 7.32/1.50  
% 7.32/1.50  ------ Selected
% 7.32/1.50  
% 7.32/1.50  total_time:                             0.631
% 7.32/1.50  
%------------------------------------------------------------------------------
