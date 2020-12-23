%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0111+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:22 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 331 expanded)
%              Number of clauses        :   46 ( 116 expanded)
%              Number of leaves         :    6 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  217 (1459 expanded)
%              Number of equality atoms :   83 ( 396 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,axiom,(
    ! [X0,X1] : r3_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f166,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(rectify,[],[f46])).

fof(f404,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f166])).

fof(f52,conjecture,(
    ! [X0,X1] :
      ( ~ ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) )
    <=> r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( ~ r2_xboole_0(X1,X0)
            & X0 != X1
            & ~ r2_xboole_0(X0,X1) )
      <=> r3_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f52])).

fof(f185,plain,(
    ? [X0,X1] :
      ( ( r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    <~> r3_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f314,plain,(
    ? [X0,X1] :
      ( ( ~ r3_xboole_0(X0,X1)
        | ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) ) )
      & ( r3_xboole_0(X0,X1)
        | r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f185])).

fof(f315,plain,(
    ? [X0,X1] :
      ( ( ~ r3_xboole_0(X0,X1)
        | ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) ) )
      & ( r3_xboole_0(X0,X1)
        | r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f314])).

fof(f316,plain,
    ( ? [X0,X1] :
        ( ( ~ r3_xboole_0(X0,X1)
          | ( ~ r2_xboole_0(X1,X0)
            & X0 != X1
            & ~ r2_xboole_0(X0,X1) ) )
        & ( r3_xboole_0(X0,X1)
          | r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1) ) )
   => ( ( ~ r3_xboole_0(sK13,sK14)
        | ( ~ r2_xboole_0(sK14,sK13)
          & sK13 != sK14
          & ~ r2_xboole_0(sK13,sK14) ) )
      & ( r3_xboole_0(sK13,sK14)
        | r2_xboole_0(sK14,sK13)
        | sK13 = sK14
        | r2_xboole_0(sK13,sK14) ) ) ),
    introduced(choice_axiom,[])).

fof(f317,plain,
    ( ( ~ r3_xboole_0(sK13,sK14)
      | ( ~ r2_xboole_0(sK14,sK13)
        & sK13 != sK14
        & ~ r2_xboole_0(sK13,sK14) ) )
    & ( r3_xboole_0(sK13,sK14)
      | r2_xboole_0(sK14,sK13)
      | sK13 = sK14
      | r2_xboole_0(sK13,sK14) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f315,f316])).

fof(f410,plain,
    ( r3_xboole_0(sK13,sK14)
    | r2_xboole_0(sK14,sK13)
    | sK13 = sK14
    | r2_xboole_0(sK13,sK14) ),
    inference(cnf_transformation,[],[f317])).

fof(f413,plain,
    ( ~ r3_xboole_0(sK13,sK14)
    | ~ r2_xboole_0(sK14,sK13) ),
    inference(cnf_transformation,[],[f317])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f311,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f312,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f311])).

fof(f395,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f312])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f288,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f289,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f288])).

fof(f356,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f289])).

fof(f47,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
     => r3_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f184,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X1,X0)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f405,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X1,X0)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f184])).

fof(f411,plain,
    ( ~ r3_xboole_0(sK13,sK14)
    | ~ r2_xboole_0(sK13,sK14) ),
    inference(cnf_transformation,[],[f317])).

fof(f412,plain,
    ( ~ r3_xboole_0(sK13,sK14)
    | sK13 != sK14 ),
    inference(cnf_transformation,[],[f317])).

fof(f394,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f312])).

fof(f393,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f312])).

fof(f358,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f289])).

cnf(c_80,plain,
    ( r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f404])).

cnf(c_5949,plain,
    ( r3_xboole_0(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_80])).

cnf(c_88,negated_conjecture,
    ( r3_xboole_0(sK13,sK14)
    | r2_xboole_0(sK14,sK13)
    | r2_xboole_0(sK13,sK14)
    | sK13 = sK14 ),
    inference(cnf_transformation,[],[f410])).

cnf(c_5944,plain,
    ( sK13 = sK14
    | r3_xboole_0(sK13,sK14) = iProver_top
    | r2_xboole_0(sK14,sK13) = iProver_top
    | r2_xboole_0(sK13,sK14) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_88])).

cnf(c_203,plain,
    ( sK13 = sK14
    | r3_xboole_0(sK13,sK14) = iProver_top
    | r2_xboole_0(sK14,sK13) = iProver_top
    | r2_xboole_0(sK13,sK14) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_88])).

cnf(c_85,negated_conjecture,
    ( ~ r3_xboole_0(sK13,sK14)
    | ~ r2_xboole_0(sK14,sK13) ),
    inference(cnf_transformation,[],[f413])).

cnf(c_5947,plain,
    ( r3_xboole_0(sK13,sK14) != iProver_top
    | r2_xboole_0(sK14,sK13) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_85])).

cnf(c_206,plain,
    ( r3_xboole_0(sK13,sK14) != iProver_top
    | r2_xboole_0(sK14,sK13) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_85])).

cnf(c_69,plain,
    ( r3_xboole_0(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f395])).

cnf(c_6285,plain,
    ( r3_xboole_0(sK13,sK14)
    | ~ r1_tarski(sK14,sK13) ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_6289,plain,
    ( r3_xboole_0(sK13,sK14) = iProver_top
    | r1_tarski(sK14,sK13) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6285])).

cnf(c_34,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f356])).

cnf(c_6313,plain,
    ( r1_tarski(sK14,sK13)
    | ~ r2_xboole_0(sK14,sK13) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_6314,plain,
    ( r1_tarski(sK14,sK13) = iProver_top
    | r2_xboole_0(sK14,sK13) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6313])).

cnf(c_6432,plain,
    ( r2_xboole_0(sK14,sK13) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5947,c_206,c_6289,c_6314])).

cnf(c_6437,plain,
    ( r3_xboole_0(sK13,sK14) = iProver_top
    | sK13 = sK14
    | r2_xboole_0(sK13,sK14) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5944,c_203,c_206,c_6289,c_6314])).

cnf(c_6438,plain,
    ( sK13 = sK14
    | r3_xboole_0(sK13,sK14) = iProver_top
    | r2_xboole_0(sK13,sK14) = iProver_top ),
    inference(renaming,[status(thm)],[c_6437])).

cnf(c_81,plain,
    ( ~ r3_xboole_0(X0,X1)
    | r3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f405])).

cnf(c_5948,plain,
    ( r3_xboole_0(X0,X1) != iProver_top
    | r3_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_81])).

cnf(c_16628,plain,
    ( sK14 = sK13
    | r3_xboole_0(sK14,sK13) = iProver_top
    | r2_xboole_0(sK13,sK14) = iProver_top ),
    inference(superposition,[status(thm)],[c_6438,c_5948])).

cnf(c_87,negated_conjecture,
    ( ~ r3_xboole_0(sK13,sK14)
    | ~ r2_xboole_0(sK13,sK14) ),
    inference(cnf_transformation,[],[f411])).

cnf(c_204,plain,
    ( r3_xboole_0(sK13,sK14) != iProver_top
    | r2_xboole_0(sK13,sK14) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_87])).

cnf(c_86,negated_conjecture,
    ( ~ r3_xboole_0(sK13,sK14)
    | sK13 != sK14 ),
    inference(cnf_transformation,[],[f412])).

cnf(c_205,plain,
    ( sK13 != sK14
    | r3_xboole_0(sK13,sK14) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_86])).

cnf(c_70,plain,
    ( r3_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f394])).

cnf(c_6286,plain,
    ( r3_xboole_0(sK13,sK14)
    | ~ r1_tarski(sK13,sK14) ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_6287,plain,
    ( r3_xboole_0(sK13,sK14) = iProver_top
    | r1_tarski(sK13,sK14) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6286])).

cnf(c_6291,plain,
    ( ~ r3_xboole_0(sK14,sK13)
    | r3_xboole_0(sK13,sK14) ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_6292,plain,
    ( r3_xboole_0(sK14,sK13) != iProver_top
    | r3_xboole_0(sK13,sK14) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6291])).

cnf(c_71,plain,
    ( ~ r3_xboole_0(X0,X1)
    | r1_tarski(X0,X1)
    | r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f393])).

cnf(c_6309,plain,
    ( ~ r3_xboole_0(sK14,sK13)
    | r1_tarski(sK14,sK13)
    | r1_tarski(sK13,sK14) ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_6322,plain,
    ( r3_xboole_0(sK14,sK13) != iProver_top
    | r1_tarski(sK14,sK13) = iProver_top
    | r1_tarski(sK13,sK14) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6309])).

cnf(c_32,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f358])).

cnf(c_6379,plain,
    ( ~ r1_tarski(sK14,sK13)
    | r2_xboole_0(sK14,sK13)
    | sK13 = sK14 ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_6383,plain,
    ( sK13 = sK14
    | r1_tarski(sK14,sK13) != iProver_top
    | r2_xboole_0(sK14,sK13) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6379])).

cnf(c_6467,plain,
    ( r1_tarski(sK13,sK14)
    | ~ r2_xboole_0(sK13,sK14) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_6468,plain,
    ( r1_tarski(sK13,sK14) = iProver_top
    | r2_xboole_0(sK13,sK14) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6467])).

cnf(c_7074,plain,
    ( ~ r1_tarski(X0,sK14)
    | r2_xboole_0(X0,sK14)
    | sK14 = X0 ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_12496,plain,
    ( ~ r1_tarski(sK13,sK14)
    | r2_xboole_0(sK13,sK14)
    | sK14 = sK13 ),
    inference(instantiation,[status(thm)],[c_7074])).

cnf(c_12497,plain,
    ( sK14 = sK13
    | r1_tarski(sK13,sK14) != iProver_top
    | r2_xboole_0(sK13,sK14) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12496])).

cnf(c_17141,plain,
    ( sK14 = sK13
    | r2_xboole_0(sK13,sK14) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16628,c_204,c_205,c_206,c_6287,c_6289,c_6292,c_6314,c_6322,c_6383,c_6468,c_12497])).

cnf(c_17145,plain,
    ( sK14 = sK13 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17141,c_204,c_205,c_206,c_6287,c_6289,c_6292,c_6314,c_6322,c_6383,c_6468,c_12497,c_16628])).

cnf(c_5946,plain,
    ( sK13 != sK14
    | r3_xboole_0(sK13,sK14) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_86])).

cnf(c_17150,plain,
    ( sK13 != sK13
    | r3_xboole_0(sK13,sK13) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17145,c_5946])).

cnf(c_17151,plain,
    ( r3_xboole_0(sK13,sK13) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_17150])).

cnf(c_17331,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_5949,c_17151])).

%------------------------------------------------------------------------------
