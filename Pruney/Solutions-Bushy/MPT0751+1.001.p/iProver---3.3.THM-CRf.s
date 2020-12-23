%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0751+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:03 EST 2020

% Result     : Theorem 1.29s
% Output     : CNFRefutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  131 (1528 expanded)
%              Number of clauses        :   77 ( 508 expanded)
%              Number of leaves         :   15 ( 306 expanded)
%              Depth                    :   25
%              Number of atoms          :  442 (6996 expanded)
%              Number of equality atoms :  146 (1421 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( ~ ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
        & ~ ( ! [X1] :
                ( v3_ordinal1(X1)
               => k1_ordinal1(X1) != X0 )
            & ~ v4_ordinal1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X1] :
                  ( v3_ordinal1(X1)
                 => k1_ordinal1(X1) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X2] :
                  ( v3_ordinal1(X2)
                 => k1_ordinal1(X2) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(rectify,[],[f11])).

fof(f28,plain,(
    ? [X0] :
      ( ( ( v4_ordinal1(X0)
          & ? [X1] :
              ( k1_ordinal1(X1) = X0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != X0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(X0) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_ordinal1(X1) = X0
          & v3_ordinal1(X1) )
     => ( k1_ordinal1(sK2) = X0
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ( ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
          | ( ! [X2] :
                ( k1_ordinal1(X2) != X0
                | ~ v3_ordinal1(X2) )
            & ~ v4_ordinal1(X0) ) )
        & v3_ordinal1(X0) )
   => ( ( ( v4_ordinal1(sK1)
          & ? [X1] :
              ( k1_ordinal1(X1) = sK1
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != sK1
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(sK1) ) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( ( v4_ordinal1(sK1)
        & k1_ordinal1(sK2) = sK1
        & v3_ordinal1(sK2) )
      | ( ! [X2] :
            ( k1_ordinal1(X2) != sK1
            | ~ v3_ordinal1(X2) )
        & ~ v4_ordinal1(sK1) ) )
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f36,f35])).

fof(f52,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X1] :
              ( r2_hidden(k1_ordinal1(X1),X0)
              | ~ r2_hidden(X1,X0)
              | ~ v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK0(X0)),X0)
        & r2_hidden(sK0(X0),X0)
        & v3_ordinal1(sK0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ( ~ r2_hidden(k1_ordinal1(sK0(X0)),X0)
            & r2_hidden(sK0(X0),X0)
            & v3_ordinal1(sK0(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f51,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k1_ordinal1(sK0(X0)),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | v3_ordinal1(sK0(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | r2_hidden(sK0(X0),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,
    ( v3_ordinal1(sK2)
    | ~ v4_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,
    ( k1_ordinal1(sK2) = sK1
    | ~ v4_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    ! [X2] :
      ( k1_ordinal1(sK2) = sK1
      | k1_ordinal1(X2) != sK1
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f48,plain,(
    ! [X2,X0] :
      ( r2_hidden(k1_ordinal1(X2),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X2] :
      ( v4_ordinal1(sK1)
      | k1_ordinal1(X2) != sK1
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_20,negated_conjecture,
    ( v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1084,plain,
    ( v3_ordinal1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_7,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_231,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_1,c_7])).

cnf(c_253,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_2,c_231])).

cnf(c_279,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_5,c_253])).

cnf(c_9,plain,
    ( r1_ordinal1(k1_ordinal1(X0),X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_307,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | ~ v3_ordinal1(X3)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 != X3
    | X3 = X2
    | k1_ordinal1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_279,c_9])).

cnf(c_308,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_ordinal1(X0),X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(k1_ordinal1(X0))
    | X1 = k1_ordinal1(X0) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_3,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_310,plain,
    ( ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | r2_hidden(k1_ordinal1(X0),X1)
    | ~ r2_hidden(X0,X1)
    | X1 = k1_ordinal1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_308,c_3])).

cnf(c_311,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_ordinal1(X0),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = k1_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_310])).

cnf(c_1083,plain,
    ( X0 = k1_ordinal1(X1)
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(k1_ordinal1(X1),X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_10,plain,
    ( ~ r2_hidden(k1_ordinal1(sK0(X0)),X0)
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1093,plain,
    ( r2_hidden(k1_ordinal1(sK0(X0)),X0) != iProver_top
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1629,plain,
    ( k1_ordinal1(sK0(X0)) = X0
    | r2_hidden(sK0(X0),X0) != iProver_top
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1083,c_1093])).

cnf(c_12,plain,
    ( v4_ordinal1(X0)
    | ~ v3_ordinal1(X0)
    | v3_ordinal1(sK0(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_37,plain,
    ( v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( r2_hidden(sK0(X0),X0)
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_40,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2216,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v4_ordinal1(X0) = iProver_top
    | k1_ordinal1(sK0(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1629,c_37,c_40])).

cnf(c_2217,plain,
    ( k1_ordinal1(sK0(X0)) = X0
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2216])).

cnf(c_2227,plain,
    ( k1_ordinal1(sK0(sK1)) = sK1
    | v4_ordinal1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1084,c_2217])).

cnf(c_19,negated_conjecture,
    ( ~ v4_ordinal1(sK1)
    | v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1085,plain,
    ( v4_ordinal1(sK1) != iProver_top
    | v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2257,plain,
    ( k1_ordinal1(sK0(sK1)) = sK1
    | v3_ordinal1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2227,c_1085])).

cnf(c_17,negated_conjecture,
    ( ~ v4_ordinal1(sK1)
    | k1_ordinal1(sK2) = sK1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1087,plain,
    ( k1_ordinal1(sK2) = sK1
    | v4_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2256,plain,
    ( k1_ordinal1(sK0(sK1)) = sK1
    | k1_ordinal1(sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_2227,c_1087])).

cnf(c_16,negated_conjecture,
    ( ~ v3_ordinal1(X0)
    | k1_ordinal1(X0) != sK1
    | k1_ordinal1(sK2) = sK1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1088,plain,
    ( k1_ordinal1(X0) != sK1
    | k1_ordinal1(sK2) = sK1
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2338,plain,
    ( k1_ordinal1(sK2) = sK1
    | v3_ordinal1(sK0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2256,c_1088])).

cnf(c_21,plain,
    ( v3_ordinal1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_432,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(sK0(X0))
    | k1_ordinal1(sK2) = sK1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_433,plain,
    ( v3_ordinal1(sK0(sK1))
    | ~ v3_ordinal1(sK1)
    | k1_ordinal1(sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_434,plain,
    ( k1_ordinal1(sK2) = sK1
    | v3_ordinal1(sK0(sK1)) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_2477,plain,
    ( k1_ordinal1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2338,c_21,c_434])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_ordinal1(X0),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1090,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k1_ordinal1(X0),X1) = iProver_top
    | v4_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1094,plain,
    ( r2_hidden(X0,k1_ordinal1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1096,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1428,plain,
    ( r2_hidden(k1_ordinal1(X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_1096])).

cnf(c_1635,plain,
    ( k1_ordinal1(X0) = X0
    | r2_hidden(X0,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1083,c_1428])).

cnf(c_1236,plain,
    ( ~ r2_hidden(k1_ordinal1(X0),k1_ordinal1(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_828,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1261,plain,
    ( k1_ordinal1(X0) = k1_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_828])).

cnf(c_830,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1219,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_ordinal1(X2))
    | X0 != X2
    | X1 != k1_ordinal1(X2) ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_1260,plain,
    ( ~ r2_hidden(X0,k1_ordinal1(X0))
    | r2_hidden(X1,k1_ordinal1(X0))
    | X1 != X0
    | k1_ordinal1(X0) != k1_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_1319,plain,
    ( ~ r2_hidden(X0,k1_ordinal1(X0))
    | r2_hidden(k1_ordinal1(X0),k1_ordinal1(X0))
    | k1_ordinal1(X0) != X0
    | k1_ordinal1(X0) != k1_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_1260])).

cnf(c_1737,plain,
    ( r2_hidden(X0,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1635,c_6,c_1236,c_1261,c_1319])).

cnf(c_1835,plain,
    ( r2_hidden(X0,k1_ordinal1(X0)) != iProver_top
    | v4_ordinal1(k1_ordinal1(X0)) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_1737])).

cnf(c_55,plain,
    ( r2_hidden(X0,k1_ordinal1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_64,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1209,plain,
    ( ~ r2_hidden(X0,k1_ordinal1(X0))
    | r2_hidden(k1_ordinal1(X0),k1_ordinal1(X0))
    | ~ v4_ordinal1(k1_ordinal1(X0))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k1_ordinal1(X0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1210,plain,
    ( r2_hidden(X0,k1_ordinal1(X0)) != iProver_top
    | r2_hidden(k1_ordinal1(X0),k1_ordinal1(X0)) = iProver_top
    | v4_ordinal1(k1_ordinal1(X0)) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1209])).

cnf(c_1252,plain,
    ( r2_hidden(k1_ordinal1(X0),k1_ordinal1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1236])).

cnf(c_1877,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v4_ordinal1(k1_ordinal1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1835,c_55,c_64,c_1210,c_1252])).

cnf(c_1878,plain,
    ( v4_ordinal1(k1_ordinal1(X0)) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1877])).

cnf(c_2485,plain,
    ( v4_ordinal1(sK1) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2477,c_1878])).

cnf(c_14,negated_conjecture,
    ( v4_ordinal1(sK1)
    | ~ v3_ordinal1(X0)
    | k1_ordinal1(X0) != sK1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1089,plain,
    ( k1_ordinal1(X0) != sK1
    | v4_ordinal1(sK1) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2490,plain,
    ( v4_ordinal1(sK1) = iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2477,c_1089])).

cnf(c_2512,plain,
    ( v3_ordinal1(sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2485,c_2490])).

cnf(c_2639,plain,
    ( k1_ordinal1(sK0(sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_2257,c_2512])).

cnf(c_2685,plain,
    ( v4_ordinal1(sK1) != iProver_top
    | v3_ordinal1(sK0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2639,c_1878])).

cnf(c_2690,plain,
    ( v4_ordinal1(sK1) = iProver_top
    | v3_ordinal1(sK0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2639,c_1089])).

cnf(c_2716,plain,
    ( v3_ordinal1(sK0(sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2685,c_2690])).

cnf(c_418,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(sK0(X0))
    | v3_ordinal1(sK2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_419,plain,
    ( v3_ordinal1(sK0(sK1))
    | v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_420,plain,
    ( v3_ordinal1(sK0(sK1)) = iProver_top
    | v3_ordinal1(sK2) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2716,c_2512,c_420,c_21])).


%------------------------------------------------------------------------------
