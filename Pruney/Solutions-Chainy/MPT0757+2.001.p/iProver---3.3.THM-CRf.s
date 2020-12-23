%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:10 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 343 expanded)
%              Number of clauses        :   71 ( 114 expanded)
%              Number of leaves         :   13 (  80 expanded)
%              Depth                    :   15
%              Number of atoms          :  328 (1309 expanded)
%              Number of equality atoms :  119 ( 336 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ~ ( ~ r2_xboole_0(X1,X0)
                & X0 != X1
                & ~ r2_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
     => ( ~ r2_xboole_0(sK3,X0)
        & sK3 != X0
        & ~ r2_xboole_0(X0,sK3)
        & v3_ordinal1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_xboole_0(X1,X0)
            & X0 != X1
            & ~ r2_xboole_0(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ r2_xboole_0(X1,sK2)
          & sK2 != X1
          & ~ r2_xboole_0(sK2,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r2_xboole_0(sK3,sK2)
    & sK2 != sK3
    & ~ r2_xboole_0(sK2,sK3)
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f34,f33])).

fof(f52,plain,(
    ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f35])).

fof(f50,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X2,X0)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ~ r2_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_418,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_912,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK3,sK2),sK3)
    | X0 != sK0(sK3,sK2)
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_418])).

cnf(c_1056,plain,
    ( r2_hidden(X0,sK3)
    | ~ r2_hidden(sK0(sK3,sK2),sK3)
    | X0 != sK0(sK3,sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_2007,plain,
    ( ~ r2_hidden(sK0(sK3,sK2),sK3)
    | r2_hidden(sK2,sK3)
    | sK2 != sK0(sK3,sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_944,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2,sK3)
    | X0 != sK2
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_418])).

cnf(c_1168,plain,
    ( r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,sK3)
    | X0 != sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_944])).

cnf(c_1551,plain,
    ( r2_hidden(sK2,sK0(sK2,sK3))
    | ~ r2_hidden(sK2,sK3)
    | sK0(sK2,sK3) != sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_1552,plain,
    ( sK0(sK2,sK3) != sK3
    | sK2 != sK2
    | r2_hidden(sK2,sK0(sK2,sK3)) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1551])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_760,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,negated_conjecture,
    ( ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_227,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_228,plain,
    ( ~ r1_tarski(sK2,sK3)
    | sK3 = sK2 ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_267,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | sK2 != X0
    | sK2 = sK3
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_228])).

cnf(c_268,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),sK3)
    | sK2 = sK3 ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_15,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_270,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_268,c_15])).

cnf(c_753,plain,
    ( r2_hidden(sK0(sK2,sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_1093,plain,
    ( sK0(sK2,sK3) = sK3
    | r2_hidden(sK3,sK0(sK2,sK3)) = iProver_top
    | v3_ordinal1(sK0(sK2,sK3)) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_753])).

cnf(c_18,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_256,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | sK2 != X0
    | sK2 = sK3
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_228])).

cnf(c_257,plain,
    ( r2_hidden(sK0(sK2,sK3),sK2)
    | sK2 = sK3 ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_258,plain,
    ( sK2 = sK3
    | r2_hidden(sK0(sK2,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_257])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_876,plain,
    ( ~ r2_hidden(X0,sK2)
    | v3_ordinal1(X0)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_983,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),sK2)
    | v3_ordinal1(sK0(sK2,sK3))
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_984,plain,
    ( r2_hidden(sK0(sK2,sK3),sK2) != iProver_top
    | v3_ordinal1(sK0(sK2,sK3)) = iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_983])).

cnf(c_1528,plain,
    ( sK0(sK2,sK3) = sK3
    | r2_hidden(sK3,sK0(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1093,c_19,c_20,c_15,c_258,c_984])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_932,plain,
    ( ~ r2_hidden(X0,sK0(sK3,sK2))
    | ~ r2_hidden(sK0(sK3,sK2),sK3)
    | ~ r2_hidden(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1264,plain,
    ( ~ r2_hidden(sK0(sK3,sK2),sK3)
    | ~ r2_hidden(sK2,sK0(sK3,sK2))
    | ~ r2_hidden(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_932])).

cnf(c_1268,plain,
    ( r2_hidden(sK0(sK3,sK2),sK3) != iProver_top
    | r2_hidden(sK2,sK0(sK3,sK2)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1264])).

cnf(c_1014,plain,
    ( r2_hidden(X0,sK2)
    | r2_hidden(sK2,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1241,plain,
    ( r2_hidden(sK0(sK3,sK2),sK2)
    | r2_hidden(sK2,sK0(sK3,sK2))
    | ~ v3_ordinal1(sK0(sK3,sK2))
    | ~ v3_ordinal1(sK2)
    | sK2 = sK0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_1242,plain,
    ( sK2 = sK0(sK3,sK2)
    | r2_hidden(sK0(sK3,sK2),sK2) = iProver_top
    | r2_hidden(sK2,sK0(sK3,sK2)) = iProver_top
    | v3_ordinal1(sK0(sK3,sK2)) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1241])).

cnf(c_416,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1057,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_416])).

cnf(c_942,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1040,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),sK2)
    | ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK3,sK0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_942])).

cnf(c_1041,plain,
    ( r2_hidden(sK0(sK2,sK3),sK2) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | r2_hidden(sK3,sK0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1040])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1022,plain,
    ( r2_hidden(sK2,sK3)
    | k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1023,plain,
    ( k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1022])).

cnf(c_1020,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_416])).

cnf(c_871,plain,
    ( ~ r2_hidden(X0,sK3)
    | v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_958,plain,
    ( ~ r2_hidden(sK0(sK3,sK2),sK3)
    | v3_ordinal1(sK0(sK3,sK2))
    | ~ v3_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_871])).

cnf(c_959,plain,
    ( r2_hidden(sK0(sK3,sK2),sK3) != iProver_top
    | v3_ordinal1(sK0(sK3,sK2)) = iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_958])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_945,plain,
    ( ~ r2_hidden(sK2,sK3)
    | k4_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_925,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),sK2)
    | ~ r2_hidden(sK2,sK0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_926,plain,
    ( r2_hidden(sK0(sK2,sK3),sK2) != iProver_top
    | r2_hidden(sK2,sK0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_925])).

cnf(c_909,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK3,sK2)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_910,plain,
    ( sK2 = sK3
    | r2_hidden(sK2,sK3) = iProver_top
    | r2_hidden(sK3,sK2) = iProver_top
    | v3_ordinal1(sK2) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_909])).

cnf(c_14,negated_conjecture,
    ( ~ r2_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_216,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_217,plain,
    ( ~ r1_tarski(sK3,sK2)
    | sK2 = sK3 ),
    inference(unflattening,[status(thm)],[c_216])).

cnf(c_219,plain,
    ( ~ r1_tarski(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_217,c_15])).

cnf(c_249,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_219])).

cnf(c_250,plain,
    ( ~ r2_hidden(sK0(sK3,sK2),sK2) ),
    inference(unflattening,[status(thm)],[c_249])).

cnf(c_251,plain,
    ( r2_hidden(sK0(sK3,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_250])).

cnf(c_242,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_219])).

cnf(c_243,plain,
    ( r2_hidden(sK0(sK3,sK2),sK3) ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_244,plain,
    ( r2_hidden(sK0(sK3,sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_243])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2007,c_1552,c_1528,c_1268,c_1242,c_1057,c_1041,c_1023,c_1020,c_959,c_945,c_926,c_910,c_258,c_251,c_244,c_243,c_15,c_20,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.17/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.02  
% 2.17/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.17/1.02  
% 2.17/1.02  ------  iProver source info
% 2.17/1.02  
% 2.17/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.17/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.17/1.02  git: non_committed_changes: false
% 2.17/1.02  git: last_make_outside_of_git: false
% 2.17/1.02  
% 2.17/1.02  ------ 
% 2.17/1.02  
% 2.17/1.02  ------ Input Options
% 2.17/1.02  
% 2.17/1.02  --out_options                           all
% 2.17/1.02  --tptp_safe_out                         true
% 2.17/1.02  --problem_path                          ""
% 2.17/1.02  --include_path                          ""
% 2.17/1.02  --clausifier                            res/vclausify_rel
% 2.17/1.02  --clausifier_options                    --mode clausify
% 2.17/1.02  --stdin                                 false
% 2.17/1.02  --stats_out                             all
% 2.17/1.02  
% 2.17/1.02  ------ General Options
% 2.17/1.02  
% 2.17/1.02  --fof                                   false
% 2.17/1.02  --time_out_real                         305.
% 2.17/1.02  --time_out_virtual                      -1.
% 2.17/1.02  --symbol_type_check                     false
% 2.17/1.02  --clausify_out                          false
% 2.17/1.02  --sig_cnt_out                           false
% 2.17/1.02  --trig_cnt_out                          false
% 2.17/1.02  --trig_cnt_out_tolerance                1.
% 2.17/1.02  --trig_cnt_out_sk_spl                   false
% 2.17/1.02  --abstr_cl_out                          false
% 2.17/1.02  
% 2.17/1.02  ------ Global Options
% 2.17/1.02  
% 2.17/1.02  --schedule                              default
% 2.17/1.02  --add_important_lit                     false
% 2.17/1.02  --prop_solver_per_cl                    1000
% 2.17/1.02  --min_unsat_core                        false
% 2.17/1.02  --soft_assumptions                      false
% 2.17/1.02  --soft_lemma_size                       3
% 2.17/1.02  --prop_impl_unit_size                   0
% 2.17/1.02  --prop_impl_unit                        []
% 2.17/1.02  --share_sel_clauses                     true
% 2.17/1.02  --reset_solvers                         false
% 2.17/1.02  --bc_imp_inh                            [conj_cone]
% 2.17/1.02  --conj_cone_tolerance                   3.
% 2.17/1.02  --extra_neg_conj                        none
% 2.17/1.02  --large_theory_mode                     true
% 2.17/1.02  --prolific_symb_bound                   200
% 2.17/1.02  --lt_threshold                          2000
% 2.17/1.02  --clause_weak_htbl                      true
% 2.17/1.02  --gc_record_bc_elim                     false
% 2.17/1.02  
% 2.17/1.02  ------ Preprocessing Options
% 2.17/1.02  
% 2.17/1.02  --preprocessing_flag                    true
% 2.17/1.02  --time_out_prep_mult                    0.1
% 2.17/1.02  --splitting_mode                        input
% 2.17/1.02  --splitting_grd                         true
% 2.17/1.02  --splitting_cvd                         false
% 2.17/1.02  --splitting_cvd_svl                     false
% 2.17/1.02  --splitting_nvd                         32
% 2.17/1.02  --sub_typing                            true
% 2.17/1.02  --prep_gs_sim                           true
% 2.17/1.02  --prep_unflatten                        true
% 2.17/1.02  --prep_res_sim                          true
% 2.17/1.02  --prep_upred                            true
% 2.17/1.02  --prep_sem_filter                       exhaustive
% 2.17/1.02  --prep_sem_filter_out                   false
% 2.17/1.02  --pred_elim                             true
% 2.17/1.02  --res_sim_input                         true
% 2.17/1.02  --eq_ax_congr_red                       true
% 2.17/1.02  --pure_diseq_elim                       true
% 2.17/1.02  --brand_transform                       false
% 2.17/1.02  --non_eq_to_eq                          false
% 2.17/1.02  --prep_def_merge                        true
% 2.17/1.02  --prep_def_merge_prop_impl              false
% 2.17/1.02  --prep_def_merge_mbd                    true
% 2.17/1.02  --prep_def_merge_tr_red                 false
% 2.17/1.02  --prep_def_merge_tr_cl                  false
% 2.17/1.02  --smt_preprocessing                     true
% 2.17/1.02  --smt_ac_axioms                         fast
% 2.17/1.02  --preprocessed_out                      false
% 2.17/1.02  --preprocessed_stats                    false
% 2.17/1.02  
% 2.17/1.02  ------ Abstraction refinement Options
% 2.17/1.02  
% 2.17/1.02  --abstr_ref                             []
% 2.17/1.02  --abstr_ref_prep                        false
% 2.17/1.02  --abstr_ref_until_sat                   false
% 2.17/1.02  --abstr_ref_sig_restrict                funpre
% 2.17/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/1.02  --abstr_ref_under                       []
% 2.17/1.02  
% 2.17/1.02  ------ SAT Options
% 2.17/1.02  
% 2.17/1.02  --sat_mode                              false
% 2.17/1.02  --sat_fm_restart_options                ""
% 2.17/1.02  --sat_gr_def                            false
% 2.17/1.02  --sat_epr_types                         true
% 2.17/1.02  --sat_non_cyclic_types                  false
% 2.17/1.02  --sat_finite_models                     false
% 2.17/1.02  --sat_fm_lemmas                         false
% 2.17/1.02  --sat_fm_prep                           false
% 2.17/1.02  --sat_fm_uc_incr                        true
% 2.17/1.02  --sat_out_model                         small
% 2.17/1.02  --sat_out_clauses                       false
% 2.17/1.02  
% 2.17/1.02  ------ QBF Options
% 2.17/1.02  
% 2.17/1.02  --qbf_mode                              false
% 2.17/1.02  --qbf_elim_univ                         false
% 2.17/1.02  --qbf_dom_inst                          none
% 2.17/1.02  --qbf_dom_pre_inst                      false
% 2.17/1.02  --qbf_sk_in                             false
% 2.17/1.02  --qbf_pred_elim                         true
% 2.17/1.02  --qbf_split                             512
% 2.17/1.02  
% 2.17/1.02  ------ BMC1 Options
% 2.17/1.02  
% 2.17/1.02  --bmc1_incremental                      false
% 2.17/1.02  --bmc1_axioms                           reachable_all
% 2.17/1.02  --bmc1_min_bound                        0
% 2.17/1.02  --bmc1_max_bound                        -1
% 2.17/1.02  --bmc1_max_bound_default                -1
% 2.17/1.02  --bmc1_symbol_reachability              true
% 2.17/1.02  --bmc1_property_lemmas                  false
% 2.17/1.02  --bmc1_k_induction                      false
% 2.17/1.02  --bmc1_non_equiv_states                 false
% 2.17/1.02  --bmc1_deadlock                         false
% 2.17/1.02  --bmc1_ucm                              false
% 2.17/1.02  --bmc1_add_unsat_core                   none
% 2.17/1.02  --bmc1_unsat_core_children              false
% 2.17/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/1.02  --bmc1_out_stat                         full
% 2.17/1.02  --bmc1_ground_init                      false
% 2.17/1.02  --bmc1_pre_inst_next_state              false
% 2.17/1.02  --bmc1_pre_inst_state                   false
% 2.17/1.02  --bmc1_pre_inst_reach_state             false
% 2.17/1.02  --bmc1_out_unsat_core                   false
% 2.17/1.02  --bmc1_aig_witness_out                  false
% 2.17/1.02  --bmc1_verbose                          false
% 2.17/1.02  --bmc1_dump_clauses_tptp                false
% 2.17/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.17/1.02  --bmc1_dump_file                        -
% 2.17/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.17/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.17/1.02  --bmc1_ucm_extend_mode                  1
% 2.17/1.02  --bmc1_ucm_init_mode                    2
% 2.17/1.02  --bmc1_ucm_cone_mode                    none
% 2.17/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.17/1.02  --bmc1_ucm_relax_model                  4
% 2.17/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.17/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/1.02  --bmc1_ucm_layered_model                none
% 2.17/1.02  --bmc1_ucm_max_lemma_size               10
% 2.17/1.02  
% 2.17/1.02  ------ AIG Options
% 2.17/1.02  
% 2.17/1.02  --aig_mode                              false
% 2.17/1.02  
% 2.17/1.02  ------ Instantiation Options
% 2.17/1.02  
% 2.17/1.02  --instantiation_flag                    true
% 2.17/1.02  --inst_sos_flag                         false
% 2.17/1.02  --inst_sos_phase                        true
% 2.17/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/1.02  --inst_lit_sel_side                     num_symb
% 2.17/1.02  --inst_solver_per_active                1400
% 2.17/1.02  --inst_solver_calls_frac                1.
% 2.17/1.02  --inst_passive_queue_type               priority_queues
% 2.17/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/1.02  --inst_passive_queues_freq              [25;2]
% 2.17/1.02  --inst_dismatching                      true
% 2.17/1.02  --inst_eager_unprocessed_to_passive     true
% 2.17/1.02  --inst_prop_sim_given                   true
% 2.17/1.02  --inst_prop_sim_new                     false
% 2.17/1.02  --inst_subs_new                         false
% 2.17/1.02  --inst_eq_res_simp                      false
% 2.17/1.02  --inst_subs_given                       false
% 2.17/1.02  --inst_orphan_elimination               true
% 2.17/1.02  --inst_learning_loop_flag               true
% 2.17/1.02  --inst_learning_start                   3000
% 2.17/1.02  --inst_learning_factor                  2
% 2.17/1.02  --inst_start_prop_sim_after_learn       3
% 2.17/1.02  --inst_sel_renew                        solver
% 2.17/1.02  --inst_lit_activity_flag                true
% 2.17/1.02  --inst_restr_to_given                   false
% 2.17/1.02  --inst_activity_threshold               500
% 2.17/1.02  --inst_out_proof                        true
% 2.17/1.02  
% 2.17/1.02  ------ Resolution Options
% 2.17/1.02  
% 2.17/1.02  --resolution_flag                       true
% 2.17/1.02  --res_lit_sel                           adaptive
% 2.17/1.02  --res_lit_sel_side                      none
% 2.17/1.02  --res_ordering                          kbo
% 2.17/1.02  --res_to_prop_solver                    active
% 2.17/1.02  --res_prop_simpl_new                    false
% 2.17/1.02  --res_prop_simpl_given                  true
% 2.17/1.02  --res_passive_queue_type                priority_queues
% 2.17/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/1.02  --res_passive_queues_freq               [15;5]
% 2.17/1.02  --res_forward_subs                      full
% 2.17/1.02  --res_backward_subs                     full
% 2.17/1.02  --res_forward_subs_resolution           true
% 2.17/1.02  --res_backward_subs_resolution          true
% 2.17/1.02  --res_orphan_elimination                true
% 2.17/1.02  --res_time_limit                        2.
% 2.17/1.02  --res_out_proof                         true
% 2.17/1.02  
% 2.17/1.02  ------ Superposition Options
% 2.17/1.02  
% 2.17/1.02  --superposition_flag                    true
% 2.17/1.02  --sup_passive_queue_type                priority_queues
% 2.17/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.17/1.02  --demod_completeness_check              fast
% 2.17/1.02  --demod_use_ground                      true
% 2.17/1.02  --sup_to_prop_solver                    passive
% 2.17/1.02  --sup_prop_simpl_new                    true
% 2.17/1.02  --sup_prop_simpl_given                  true
% 2.17/1.02  --sup_fun_splitting                     false
% 2.17/1.02  --sup_smt_interval                      50000
% 2.17/1.02  
% 2.17/1.02  ------ Superposition Simplification Setup
% 2.17/1.02  
% 2.17/1.02  --sup_indices_passive                   []
% 2.17/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/1.02  --sup_full_bw                           [BwDemod]
% 2.17/1.02  --sup_immed_triv                        [TrivRules]
% 2.17/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/1.02  --sup_immed_bw_main                     []
% 2.17/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/1.02  
% 2.17/1.02  ------ Combination Options
% 2.17/1.02  
% 2.17/1.02  --comb_res_mult                         3
% 2.17/1.02  --comb_sup_mult                         2
% 2.17/1.02  --comb_inst_mult                        10
% 2.17/1.02  
% 2.17/1.02  ------ Debug Options
% 2.17/1.02  
% 2.17/1.02  --dbg_backtrace                         false
% 2.17/1.02  --dbg_dump_prop_clauses                 false
% 2.17/1.02  --dbg_dump_prop_clauses_file            -
% 2.17/1.02  --dbg_out_stat                          false
% 2.17/1.02  ------ Parsing...
% 2.17/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.17/1.02  
% 2.17/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.17/1.02  
% 2.17/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.17/1.02  
% 2.17/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.17/1.02  ------ Proving...
% 2.17/1.02  ------ Problem Properties 
% 2.17/1.02  
% 2.17/1.02  
% 2.17/1.02  clauses                                 16
% 2.17/1.02  conjectures                             3
% 2.17/1.02  EPR                                     7
% 2.17/1.02  Horn                                    15
% 2.17/1.02  unary                                   7
% 2.17/1.02  binary                                  5
% 2.17/1.02  lits                                    31
% 2.17/1.02  lits eq                                 4
% 2.17/1.02  fd_pure                                 0
% 2.17/1.02  fd_pseudo                               0
% 2.17/1.02  fd_cond                                 0
% 2.17/1.02  fd_pseudo_cond                          1
% 2.17/1.02  AC symbols                              0
% 2.17/1.02  
% 2.17/1.02  ------ Schedule dynamic 5 is on 
% 2.17/1.02  
% 2.17/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.17/1.02  
% 2.17/1.02  
% 2.17/1.02  ------ 
% 2.17/1.02  Current options:
% 2.17/1.02  ------ 
% 2.17/1.02  
% 2.17/1.02  ------ Input Options
% 2.17/1.02  
% 2.17/1.02  --out_options                           all
% 2.17/1.02  --tptp_safe_out                         true
% 2.17/1.02  --problem_path                          ""
% 2.17/1.02  --include_path                          ""
% 2.17/1.02  --clausifier                            res/vclausify_rel
% 2.17/1.02  --clausifier_options                    --mode clausify
% 2.17/1.02  --stdin                                 false
% 2.17/1.02  --stats_out                             all
% 2.17/1.02  
% 2.17/1.02  ------ General Options
% 2.17/1.02  
% 2.17/1.02  --fof                                   false
% 2.17/1.02  --time_out_real                         305.
% 2.17/1.02  --time_out_virtual                      -1.
% 2.17/1.02  --symbol_type_check                     false
% 2.17/1.02  --clausify_out                          false
% 2.17/1.02  --sig_cnt_out                           false
% 2.17/1.02  --trig_cnt_out                          false
% 2.17/1.02  --trig_cnt_out_tolerance                1.
% 2.17/1.02  --trig_cnt_out_sk_spl                   false
% 2.17/1.02  --abstr_cl_out                          false
% 2.17/1.02  
% 2.17/1.02  ------ Global Options
% 2.17/1.02  
% 2.17/1.02  --schedule                              default
% 2.17/1.02  --add_important_lit                     false
% 2.17/1.02  --prop_solver_per_cl                    1000
% 2.17/1.02  --min_unsat_core                        false
% 2.17/1.02  --soft_assumptions                      false
% 2.17/1.02  --soft_lemma_size                       3
% 2.17/1.02  --prop_impl_unit_size                   0
% 2.17/1.02  --prop_impl_unit                        []
% 2.17/1.02  --share_sel_clauses                     true
% 2.17/1.02  --reset_solvers                         false
% 2.17/1.02  --bc_imp_inh                            [conj_cone]
% 2.17/1.02  --conj_cone_tolerance                   3.
% 2.17/1.02  --extra_neg_conj                        none
% 2.17/1.02  --large_theory_mode                     true
% 2.17/1.02  --prolific_symb_bound                   200
% 2.17/1.02  --lt_threshold                          2000
% 2.17/1.02  --clause_weak_htbl                      true
% 2.17/1.02  --gc_record_bc_elim                     false
% 2.17/1.02  
% 2.17/1.02  ------ Preprocessing Options
% 2.17/1.02  
% 2.17/1.02  --preprocessing_flag                    true
% 2.17/1.02  --time_out_prep_mult                    0.1
% 2.17/1.02  --splitting_mode                        input
% 2.17/1.02  --splitting_grd                         true
% 2.17/1.02  --splitting_cvd                         false
% 2.17/1.02  --splitting_cvd_svl                     false
% 2.17/1.02  --splitting_nvd                         32
% 2.17/1.02  --sub_typing                            true
% 2.17/1.02  --prep_gs_sim                           true
% 2.17/1.02  --prep_unflatten                        true
% 2.17/1.02  --prep_res_sim                          true
% 2.17/1.02  --prep_upred                            true
% 2.17/1.02  --prep_sem_filter                       exhaustive
% 2.17/1.02  --prep_sem_filter_out                   false
% 2.17/1.02  --pred_elim                             true
% 2.17/1.02  --res_sim_input                         true
% 2.17/1.02  --eq_ax_congr_red                       true
% 2.17/1.02  --pure_diseq_elim                       true
% 2.17/1.02  --brand_transform                       false
% 2.17/1.02  --non_eq_to_eq                          false
% 2.17/1.02  --prep_def_merge                        true
% 2.17/1.02  --prep_def_merge_prop_impl              false
% 2.17/1.02  --prep_def_merge_mbd                    true
% 2.17/1.02  --prep_def_merge_tr_red                 false
% 2.17/1.02  --prep_def_merge_tr_cl                  false
% 2.17/1.02  --smt_preprocessing                     true
% 2.17/1.02  --smt_ac_axioms                         fast
% 2.17/1.02  --preprocessed_out                      false
% 2.17/1.02  --preprocessed_stats                    false
% 2.17/1.02  
% 2.17/1.02  ------ Abstraction refinement Options
% 2.17/1.02  
% 2.17/1.02  --abstr_ref                             []
% 2.17/1.02  --abstr_ref_prep                        false
% 2.17/1.02  --abstr_ref_until_sat                   false
% 2.17/1.02  --abstr_ref_sig_restrict                funpre
% 2.17/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/1.02  --abstr_ref_under                       []
% 2.17/1.02  
% 2.17/1.02  ------ SAT Options
% 2.17/1.02  
% 2.17/1.02  --sat_mode                              false
% 2.17/1.02  --sat_fm_restart_options                ""
% 2.17/1.02  --sat_gr_def                            false
% 2.17/1.02  --sat_epr_types                         true
% 2.17/1.02  --sat_non_cyclic_types                  false
% 2.17/1.02  --sat_finite_models                     false
% 2.17/1.02  --sat_fm_lemmas                         false
% 2.17/1.02  --sat_fm_prep                           false
% 2.17/1.02  --sat_fm_uc_incr                        true
% 2.17/1.02  --sat_out_model                         small
% 2.17/1.02  --sat_out_clauses                       false
% 2.17/1.02  
% 2.17/1.02  ------ QBF Options
% 2.17/1.02  
% 2.17/1.02  --qbf_mode                              false
% 2.17/1.02  --qbf_elim_univ                         false
% 2.17/1.02  --qbf_dom_inst                          none
% 2.17/1.02  --qbf_dom_pre_inst                      false
% 2.17/1.02  --qbf_sk_in                             false
% 2.17/1.02  --qbf_pred_elim                         true
% 2.17/1.02  --qbf_split                             512
% 2.17/1.02  
% 2.17/1.02  ------ BMC1 Options
% 2.17/1.02  
% 2.17/1.02  --bmc1_incremental                      false
% 2.17/1.02  --bmc1_axioms                           reachable_all
% 2.17/1.02  --bmc1_min_bound                        0
% 2.17/1.02  --bmc1_max_bound                        -1
% 2.17/1.02  --bmc1_max_bound_default                -1
% 2.17/1.02  --bmc1_symbol_reachability              true
% 2.17/1.02  --bmc1_property_lemmas                  false
% 2.17/1.02  --bmc1_k_induction                      false
% 2.17/1.02  --bmc1_non_equiv_states                 false
% 2.17/1.02  --bmc1_deadlock                         false
% 2.17/1.02  --bmc1_ucm                              false
% 2.17/1.02  --bmc1_add_unsat_core                   none
% 2.17/1.02  --bmc1_unsat_core_children              false
% 2.17/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/1.02  --bmc1_out_stat                         full
% 2.17/1.02  --bmc1_ground_init                      false
% 2.17/1.02  --bmc1_pre_inst_next_state              false
% 2.17/1.02  --bmc1_pre_inst_state                   false
% 2.17/1.02  --bmc1_pre_inst_reach_state             false
% 2.17/1.02  --bmc1_out_unsat_core                   false
% 2.17/1.02  --bmc1_aig_witness_out                  false
% 2.17/1.02  --bmc1_verbose                          false
% 2.17/1.02  --bmc1_dump_clauses_tptp                false
% 2.17/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.17/1.02  --bmc1_dump_file                        -
% 2.17/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.17/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.17/1.02  --bmc1_ucm_extend_mode                  1
% 2.17/1.02  --bmc1_ucm_init_mode                    2
% 2.17/1.02  --bmc1_ucm_cone_mode                    none
% 2.17/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.17/1.02  --bmc1_ucm_relax_model                  4
% 2.17/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.17/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/1.02  --bmc1_ucm_layered_model                none
% 2.17/1.02  --bmc1_ucm_max_lemma_size               10
% 2.17/1.02  
% 2.17/1.02  ------ AIG Options
% 2.17/1.02  
% 2.17/1.02  --aig_mode                              false
% 2.17/1.02  
% 2.17/1.02  ------ Instantiation Options
% 2.17/1.02  
% 2.17/1.02  --instantiation_flag                    true
% 2.17/1.02  --inst_sos_flag                         false
% 2.17/1.02  --inst_sos_phase                        true
% 2.17/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/1.02  --inst_lit_sel_side                     none
% 2.17/1.02  --inst_solver_per_active                1400
% 2.17/1.02  --inst_solver_calls_frac                1.
% 2.17/1.02  --inst_passive_queue_type               priority_queues
% 2.17/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/1.02  --inst_passive_queues_freq              [25;2]
% 2.17/1.02  --inst_dismatching                      true
% 2.17/1.02  --inst_eager_unprocessed_to_passive     true
% 2.17/1.02  --inst_prop_sim_given                   true
% 2.17/1.02  --inst_prop_sim_new                     false
% 2.17/1.02  --inst_subs_new                         false
% 2.17/1.02  --inst_eq_res_simp                      false
% 2.17/1.02  --inst_subs_given                       false
% 2.17/1.02  --inst_orphan_elimination               true
% 2.17/1.02  --inst_learning_loop_flag               true
% 2.17/1.02  --inst_learning_start                   3000
% 2.17/1.02  --inst_learning_factor                  2
% 2.17/1.02  --inst_start_prop_sim_after_learn       3
% 2.17/1.02  --inst_sel_renew                        solver
% 2.17/1.02  --inst_lit_activity_flag                true
% 2.17/1.02  --inst_restr_to_given                   false
% 2.17/1.02  --inst_activity_threshold               500
% 2.17/1.02  --inst_out_proof                        true
% 2.17/1.02  
% 2.17/1.02  ------ Resolution Options
% 2.17/1.02  
% 2.17/1.02  --resolution_flag                       false
% 2.17/1.02  --res_lit_sel                           adaptive
% 2.17/1.02  --res_lit_sel_side                      none
% 2.17/1.02  --res_ordering                          kbo
% 2.17/1.02  --res_to_prop_solver                    active
% 2.17/1.02  --res_prop_simpl_new                    false
% 2.17/1.02  --res_prop_simpl_given                  true
% 2.17/1.02  --res_passive_queue_type                priority_queues
% 2.17/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/1.02  --res_passive_queues_freq               [15;5]
% 2.17/1.02  --res_forward_subs                      full
% 2.17/1.02  --res_backward_subs                     full
% 2.17/1.02  --res_forward_subs_resolution           true
% 2.17/1.02  --res_backward_subs_resolution          true
% 2.17/1.02  --res_orphan_elimination                true
% 2.17/1.02  --res_time_limit                        2.
% 2.17/1.02  --res_out_proof                         true
% 2.17/1.02  
% 2.17/1.02  ------ Superposition Options
% 2.17/1.02  
% 2.17/1.02  --superposition_flag                    true
% 2.17/1.02  --sup_passive_queue_type                priority_queues
% 2.17/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.17/1.02  --demod_completeness_check              fast
% 2.17/1.02  --demod_use_ground                      true
% 2.17/1.02  --sup_to_prop_solver                    passive
% 2.17/1.02  --sup_prop_simpl_new                    true
% 2.17/1.02  --sup_prop_simpl_given                  true
% 2.17/1.02  --sup_fun_splitting                     false
% 2.17/1.02  --sup_smt_interval                      50000
% 2.17/1.02  
% 2.17/1.02  ------ Superposition Simplification Setup
% 2.17/1.02  
% 2.17/1.02  --sup_indices_passive                   []
% 2.17/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/1.02  --sup_full_bw                           [BwDemod]
% 2.17/1.02  --sup_immed_triv                        [TrivRules]
% 2.17/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/1.02  --sup_immed_bw_main                     []
% 2.17/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/1.02  
% 2.17/1.02  ------ Combination Options
% 2.17/1.02  
% 2.17/1.02  --comb_res_mult                         3
% 2.17/1.02  --comb_sup_mult                         2
% 2.17/1.02  --comb_inst_mult                        10
% 2.17/1.02  
% 2.17/1.02  ------ Debug Options
% 2.17/1.02  
% 2.17/1.02  --dbg_backtrace                         false
% 2.17/1.02  --dbg_dump_prop_clauses                 false
% 2.17/1.02  --dbg_dump_prop_clauses_file            -
% 2.17/1.02  --dbg_out_stat                          false
% 2.17/1.02  
% 2.17/1.02  
% 2.17/1.02  
% 2.17/1.02  
% 2.17/1.02  ------ Proving...
% 2.17/1.02  
% 2.17/1.02  
% 2.17/1.02  % SZS status Theorem for theBenchmark.p
% 2.17/1.02  
% 2.17/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.17/1.02  
% 2.17/1.02  fof(f8,axiom,(
% 2.17/1.02    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 2.17/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.02  
% 2.17/1.02  fof(f20,plain,(
% 2.17/1.02    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.17/1.02    inference(ennf_transformation,[],[f8])).
% 2.17/1.02  
% 2.17/1.02  fof(f21,plain,(
% 2.17/1.02    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.17/1.02    inference(flattening,[],[f20])).
% 2.17/1.02  
% 2.17/1.02  fof(f48,plain,(
% 2.17/1.02    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.17/1.02    inference(cnf_transformation,[],[f21])).
% 2.17/1.02  
% 2.17/1.02  fof(f2,axiom,(
% 2.17/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.17/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.02  
% 2.17/1.02  fof(f13,plain,(
% 2.17/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 2.17/1.02    inference(unused_predicate_definition_removal,[],[f2])).
% 2.17/1.02  
% 2.17/1.02  fof(f15,plain,(
% 2.17/1.02    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 2.17/1.02    inference(ennf_transformation,[],[f13])).
% 2.17/1.02  
% 2.17/1.02  fof(f25,plain,(
% 2.17/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.17/1.02    introduced(choice_axiom,[])).
% 2.17/1.02  
% 2.17/1.02  fof(f26,plain,(
% 2.17/1.02    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.17/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f25])).
% 2.17/1.02  
% 2.17/1.02  fof(f38,plain,(
% 2.17/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.17/1.02    inference(cnf_transformation,[],[f26])).
% 2.17/1.02  
% 2.17/1.02  fof(f3,axiom,(
% 2.17/1.02    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.17/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.02  
% 2.17/1.02  fof(f12,plain,(
% 2.17/1.02    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 2.17/1.02    inference(unused_predicate_definition_removal,[],[f3])).
% 2.17/1.02  
% 2.17/1.02  fof(f16,plain,(
% 2.17/1.02    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 2.17/1.02    inference(ennf_transformation,[],[f12])).
% 2.17/1.02  
% 2.17/1.02  fof(f17,plain,(
% 2.17/1.02    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 2.17/1.02    inference(flattening,[],[f16])).
% 2.17/1.02  
% 2.17/1.02  fof(f39,plain,(
% 2.17/1.02    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.17/1.02    inference(cnf_transformation,[],[f17])).
% 2.17/1.02  
% 2.17/1.02  fof(f10,conjecture,(
% 2.17/1.02    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 2.17/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.02  
% 2.17/1.02  fof(f11,negated_conjecture,(
% 2.17/1.02    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 2.17/1.02    inference(negated_conjecture,[],[f10])).
% 2.17/1.02  
% 2.17/1.02  fof(f23,plain,(
% 2.17/1.02    ? [X0] : (? [X1] : ((~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.17/1.02    inference(ennf_transformation,[],[f11])).
% 2.17/1.02  
% 2.17/1.02  fof(f24,plain,(
% 2.17/1.02    ? [X0] : (? [X1] : (~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.17/1.02    inference(flattening,[],[f23])).
% 2.17/1.02  
% 2.17/1.02  fof(f34,plain,(
% 2.17/1.02    ( ! [X0] : (? [X1] : (~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1) & v3_ordinal1(X1)) => (~r2_xboole_0(sK3,X0) & sK3 != X0 & ~r2_xboole_0(X0,sK3) & v3_ordinal1(sK3))) )),
% 2.17/1.02    introduced(choice_axiom,[])).
% 2.17/1.02  
% 2.17/1.02  fof(f33,plain,(
% 2.17/1.02    ? [X0] : (? [X1] : (~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (~r2_xboole_0(X1,sK2) & sK2 != X1 & ~r2_xboole_0(sK2,X1) & v3_ordinal1(X1)) & v3_ordinal1(sK2))),
% 2.17/1.02    introduced(choice_axiom,[])).
% 2.17/1.02  
% 2.17/1.02  fof(f35,plain,(
% 2.17/1.02    (~r2_xboole_0(sK3,sK2) & sK2 != sK3 & ~r2_xboole_0(sK2,sK3) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)),
% 2.17/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f34,f33])).
% 2.17/1.02  
% 2.17/1.02  fof(f52,plain,(
% 2.17/1.02    ~r2_xboole_0(sK2,sK3)),
% 2.17/1.02    inference(cnf_transformation,[],[f35])).
% 2.17/1.02  
% 2.17/1.02  fof(f53,plain,(
% 2.17/1.02    sK2 != sK3),
% 2.17/1.02    inference(cnf_transformation,[],[f35])).
% 2.17/1.02  
% 2.17/1.02  fof(f50,plain,(
% 2.17/1.02    v3_ordinal1(sK2)),
% 2.17/1.02    inference(cnf_transformation,[],[f35])).
% 2.17/1.02  
% 2.17/1.02  fof(f51,plain,(
% 2.17/1.02    v3_ordinal1(sK3)),
% 2.17/1.02    inference(cnf_transformation,[],[f35])).
% 2.17/1.02  
% 2.17/1.02  fof(f37,plain,(
% 2.17/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.17/1.02    inference(cnf_transformation,[],[f26])).
% 2.17/1.02  
% 2.17/1.02  fof(f7,axiom,(
% 2.17/1.02    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 2.17/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.02  
% 2.17/1.02  fof(f18,plain,(
% 2.17/1.02    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 2.17/1.02    inference(ennf_transformation,[],[f7])).
% 2.17/1.02  
% 2.17/1.02  fof(f19,plain,(
% 2.17/1.02    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 2.17/1.02    inference(flattening,[],[f18])).
% 2.17/1.02  
% 2.17/1.02  fof(f47,plain,(
% 2.17/1.02    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 2.17/1.02    inference(cnf_transformation,[],[f19])).
% 2.17/1.02  
% 2.17/1.02  fof(f9,axiom,(
% 2.17/1.02    ! [X0,X1,X2] : ~(r2_hidden(X2,X0) & r2_hidden(X1,X2) & r2_hidden(X0,X1))),
% 2.17/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.02  
% 2.17/1.02  fof(f22,plain,(
% 2.17/1.02    ! [X0,X1,X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X1))),
% 2.17/1.02    inference(ennf_transformation,[],[f9])).
% 2.17/1.02  
% 2.17/1.02  fof(f49,plain,(
% 2.17/1.02    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X1)) )),
% 2.17/1.02    inference(cnf_transformation,[],[f22])).
% 2.17/1.02  
% 2.17/1.02  fof(f5,axiom,(
% 2.17/1.02    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 2.17/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.02  
% 2.17/1.02  fof(f28,plain,(
% 2.17/1.02    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0))),
% 2.17/1.02    inference(nnf_transformation,[],[f5])).
% 2.17/1.02  
% 2.17/1.02  fof(f42,plain,(
% 2.17/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 2.17/1.02    inference(cnf_transformation,[],[f28])).
% 2.17/1.02  
% 2.17/1.02  fof(f43,plain,(
% 2.17/1.02    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) )),
% 2.17/1.02    inference(cnf_transformation,[],[f28])).
% 2.17/1.02  
% 2.17/1.02  fof(f1,axiom,(
% 2.17/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 2.17/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.02  
% 2.17/1.02  fof(f14,plain,(
% 2.17/1.02    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 2.17/1.02    inference(ennf_transformation,[],[f1])).
% 2.17/1.02  
% 2.17/1.02  fof(f36,plain,(
% 2.17/1.02    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.17/1.02    inference(cnf_transformation,[],[f14])).
% 2.17/1.02  
% 2.17/1.02  fof(f54,plain,(
% 2.17/1.02    ~r2_xboole_0(sK3,sK2)),
% 2.17/1.02    inference(cnf_transformation,[],[f35])).
% 2.17/1.02  
% 2.17/1.02  cnf(c_418,plain,
% 2.17/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.17/1.02      theory(equality) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_912,plain,
% 2.17/1.02      ( r2_hidden(X0,X1)
% 2.17/1.02      | ~ r2_hidden(sK0(sK3,sK2),sK3)
% 2.17/1.02      | X0 != sK0(sK3,sK2)
% 2.17/1.02      | X1 != sK3 ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_418]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1056,plain,
% 2.17/1.02      ( r2_hidden(X0,sK3)
% 2.17/1.02      | ~ r2_hidden(sK0(sK3,sK2),sK3)
% 2.17/1.02      | X0 != sK0(sK3,sK2)
% 2.17/1.02      | sK3 != sK3 ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_912]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_2007,plain,
% 2.17/1.02      ( ~ r2_hidden(sK0(sK3,sK2),sK3)
% 2.17/1.02      | r2_hidden(sK2,sK3)
% 2.17/1.02      | sK2 != sK0(sK3,sK2)
% 2.17/1.02      | sK3 != sK3 ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_1056]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_944,plain,
% 2.17/1.02      ( r2_hidden(X0,X1) | ~ r2_hidden(sK2,sK3) | X0 != sK2 | X1 != sK3 ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_418]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1168,plain,
% 2.17/1.02      ( r2_hidden(sK2,X0)
% 2.17/1.02      | ~ r2_hidden(sK2,sK3)
% 2.17/1.02      | X0 != sK3
% 2.17/1.02      | sK2 != sK2 ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_944]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1551,plain,
% 2.17/1.02      ( r2_hidden(sK2,sK0(sK2,sK3))
% 2.17/1.02      | ~ r2_hidden(sK2,sK3)
% 2.17/1.02      | sK0(sK2,sK3) != sK3
% 2.17/1.02      | sK2 != sK2 ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_1168]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1552,plain,
% 2.17/1.02      ( sK0(sK2,sK3) != sK3
% 2.17/1.02      | sK2 != sK2
% 2.17/1.02      | r2_hidden(sK2,sK0(sK2,sK3)) = iProver_top
% 2.17/1.02      | r2_hidden(sK2,sK3) != iProver_top ),
% 2.17/1.02      inference(predicate_to_equality,[status(thm)],[c_1551]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_12,plain,
% 2.17/1.02      ( r2_hidden(X0,X1)
% 2.17/1.02      | r2_hidden(X1,X0)
% 2.17/1.02      | ~ v3_ordinal1(X0)
% 2.17/1.02      | ~ v3_ordinal1(X1)
% 2.17/1.02      | X1 = X0 ),
% 2.17/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_760,plain,
% 2.17/1.02      ( X0 = X1
% 2.17/1.02      | r2_hidden(X1,X0) = iProver_top
% 2.17/1.02      | r2_hidden(X0,X1) = iProver_top
% 2.17/1.02      | v3_ordinal1(X1) != iProver_top
% 2.17/1.02      | v3_ordinal1(X0) != iProver_top ),
% 2.17/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1,plain,
% 2.17/1.02      ( r1_tarski(X0,X1) | ~ r2_hidden(sK0(X0,X1),X1) ),
% 2.17/1.02      inference(cnf_transformation,[],[f38]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_3,plain,
% 2.17/1.02      ( r2_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 2.17/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_16,negated_conjecture,
% 2.17/1.02      ( ~ r2_xboole_0(sK2,sK3) ),
% 2.17/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_227,plain,
% 2.17/1.02      ( ~ r1_tarski(X0,X1) | X1 = X0 | sK2 != X0 | sK3 != X1 ),
% 2.17/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_228,plain,
% 2.17/1.02      ( ~ r1_tarski(sK2,sK3) | sK3 = sK2 ),
% 2.17/1.02      inference(unflattening,[status(thm)],[c_227]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_267,plain,
% 2.17/1.02      ( ~ r2_hidden(sK0(X0,X1),X1) | sK2 != X0 | sK2 = sK3 | sK3 != X1 ),
% 2.17/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_228]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_268,plain,
% 2.17/1.02      ( ~ r2_hidden(sK0(sK2,sK3),sK3) | sK2 = sK3 ),
% 2.17/1.02      inference(unflattening,[status(thm)],[c_267]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_15,negated_conjecture,
% 2.17/1.02      ( sK2 != sK3 ),
% 2.17/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_270,plain,
% 2.17/1.02      ( ~ r2_hidden(sK0(sK2,sK3),sK3) ),
% 2.17/1.02      inference(global_propositional_subsumption,
% 2.17/1.02                [status(thm)],
% 2.17/1.02                [c_268,c_15]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_753,plain,
% 2.17/1.02      ( r2_hidden(sK0(sK2,sK3),sK3) != iProver_top ),
% 2.17/1.02      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1093,plain,
% 2.17/1.02      ( sK0(sK2,sK3) = sK3
% 2.17/1.02      | r2_hidden(sK3,sK0(sK2,sK3)) = iProver_top
% 2.17/1.02      | v3_ordinal1(sK0(sK2,sK3)) != iProver_top
% 2.17/1.02      | v3_ordinal1(sK3) != iProver_top ),
% 2.17/1.02      inference(superposition,[status(thm)],[c_760,c_753]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_18,negated_conjecture,
% 2.17/1.02      ( v3_ordinal1(sK2) ),
% 2.17/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_19,plain,
% 2.17/1.02      ( v3_ordinal1(sK2) = iProver_top ),
% 2.17/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_17,negated_conjecture,
% 2.17/1.02      ( v3_ordinal1(sK3) ),
% 2.17/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_20,plain,
% 2.17/1.02      ( v3_ordinal1(sK3) = iProver_top ),
% 2.17/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_2,plain,
% 2.17/1.02      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 2.17/1.02      inference(cnf_transformation,[],[f37]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_256,plain,
% 2.17/1.02      ( r2_hidden(sK0(X0,X1),X0) | sK2 != X0 | sK2 = sK3 | sK3 != X1 ),
% 2.17/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_228]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_257,plain,
% 2.17/1.02      ( r2_hidden(sK0(sK2,sK3),sK2) | sK2 = sK3 ),
% 2.17/1.02      inference(unflattening,[status(thm)],[c_256]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_258,plain,
% 2.17/1.02      ( sK2 = sK3 | r2_hidden(sK0(sK2,sK3),sK2) = iProver_top ),
% 2.17/1.02      inference(predicate_to_equality,[status(thm)],[c_257]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_11,plain,
% 2.17/1.02      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 2.17/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_876,plain,
% 2.17/1.02      ( ~ r2_hidden(X0,sK2) | v3_ordinal1(X0) | ~ v3_ordinal1(sK2) ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_983,plain,
% 2.17/1.02      ( ~ r2_hidden(sK0(sK2,sK3),sK2)
% 2.17/1.02      | v3_ordinal1(sK0(sK2,sK3))
% 2.17/1.02      | ~ v3_ordinal1(sK2) ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_876]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_984,plain,
% 2.17/1.02      ( r2_hidden(sK0(sK2,sK3),sK2) != iProver_top
% 2.17/1.02      | v3_ordinal1(sK0(sK2,sK3)) = iProver_top
% 2.17/1.02      | v3_ordinal1(sK2) != iProver_top ),
% 2.17/1.02      inference(predicate_to_equality,[status(thm)],[c_983]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1528,plain,
% 2.17/1.02      ( sK0(sK2,sK3) = sK3 | r2_hidden(sK3,sK0(sK2,sK3)) = iProver_top ),
% 2.17/1.02      inference(global_propositional_subsumption,
% 2.17/1.02                [status(thm)],
% 2.17/1.02                [c_1093,c_19,c_20,c_15,c_258,c_984]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_13,plain,
% 2.17/1.02      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X1,X2) ),
% 2.17/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_932,plain,
% 2.17/1.02      ( ~ r2_hidden(X0,sK0(sK3,sK2))
% 2.17/1.02      | ~ r2_hidden(sK0(sK3,sK2),sK3)
% 2.17/1.02      | ~ r2_hidden(sK3,X0) ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_13]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1264,plain,
% 2.17/1.02      ( ~ r2_hidden(sK0(sK3,sK2),sK3)
% 2.17/1.02      | ~ r2_hidden(sK2,sK0(sK3,sK2))
% 2.17/1.02      | ~ r2_hidden(sK3,sK2) ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_932]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1268,plain,
% 2.17/1.02      ( r2_hidden(sK0(sK3,sK2),sK3) != iProver_top
% 2.17/1.02      | r2_hidden(sK2,sK0(sK3,sK2)) != iProver_top
% 2.17/1.02      | r2_hidden(sK3,sK2) != iProver_top ),
% 2.17/1.02      inference(predicate_to_equality,[status(thm)],[c_1264]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1014,plain,
% 2.17/1.02      ( r2_hidden(X0,sK2)
% 2.17/1.02      | r2_hidden(sK2,X0)
% 2.17/1.02      | ~ v3_ordinal1(X0)
% 2.17/1.02      | ~ v3_ordinal1(sK2)
% 2.17/1.02      | sK2 = X0 ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1241,plain,
% 2.17/1.02      ( r2_hidden(sK0(sK3,sK2),sK2)
% 2.17/1.02      | r2_hidden(sK2,sK0(sK3,sK2))
% 2.17/1.02      | ~ v3_ordinal1(sK0(sK3,sK2))
% 2.17/1.02      | ~ v3_ordinal1(sK2)
% 2.17/1.02      | sK2 = sK0(sK3,sK2) ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_1014]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1242,plain,
% 2.17/1.02      ( sK2 = sK0(sK3,sK2)
% 2.17/1.02      | r2_hidden(sK0(sK3,sK2),sK2) = iProver_top
% 2.17/1.02      | r2_hidden(sK2,sK0(sK3,sK2)) = iProver_top
% 2.17/1.02      | v3_ordinal1(sK0(sK3,sK2)) != iProver_top
% 2.17/1.02      | v3_ordinal1(sK2) != iProver_top ),
% 2.17/1.02      inference(predicate_to_equality,[status(thm)],[c_1241]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_416,plain,( X0 = X0 ),theory(equality) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1057,plain,
% 2.17/1.02      ( sK3 = sK3 ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_416]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_942,plain,
% 2.17/1.02      ( ~ r2_hidden(X0,sK2)
% 2.17/1.02      | ~ r2_hidden(sK2,sK3)
% 2.17/1.02      | ~ r2_hidden(sK3,X0) ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_13]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1040,plain,
% 2.17/1.02      ( ~ r2_hidden(sK0(sK2,sK3),sK2)
% 2.17/1.02      | ~ r2_hidden(sK2,sK3)
% 2.17/1.02      | ~ r2_hidden(sK3,sK0(sK2,sK3)) ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_942]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1041,plain,
% 2.17/1.02      ( r2_hidden(sK0(sK2,sK3),sK2) != iProver_top
% 2.17/1.02      | r2_hidden(sK2,sK3) != iProver_top
% 2.17/1.02      | r2_hidden(sK3,sK0(sK2,sK3)) != iProver_top ),
% 2.17/1.02      inference(predicate_to_equality,[status(thm)],[c_1040]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_7,plain,
% 2.17/1.02      ( r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 2.17/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1022,plain,
% 2.17/1.02      ( r2_hidden(sK2,sK3)
% 2.17/1.02      | k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0 ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1023,plain,
% 2.17/1.02      ( k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0
% 2.17/1.02      | r2_hidden(sK2,sK3) = iProver_top ),
% 2.17/1.02      inference(predicate_to_equality,[status(thm)],[c_1022]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_1020,plain,
% 2.17/1.02      ( sK2 = sK2 ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_416]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_871,plain,
% 2.17/1.02      ( ~ r2_hidden(X0,sK3) | v3_ordinal1(X0) | ~ v3_ordinal1(sK3) ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_958,plain,
% 2.17/1.02      ( ~ r2_hidden(sK0(sK3,sK2),sK3)
% 2.17/1.02      | v3_ordinal1(sK0(sK3,sK2))
% 2.17/1.02      | ~ v3_ordinal1(sK3) ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_871]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_959,plain,
% 2.17/1.02      ( r2_hidden(sK0(sK3,sK2),sK3) != iProver_top
% 2.17/1.02      | v3_ordinal1(sK0(sK3,sK2)) = iProver_top
% 2.17/1.02      | v3_ordinal1(sK3) != iProver_top ),
% 2.17/1.02      inference(predicate_to_equality,[status(thm)],[c_958]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_6,plain,
% 2.17/1.02      ( ~ r2_hidden(X0,X1)
% 2.17/1.02      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
% 2.17/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_945,plain,
% 2.17/1.02      ( ~ r2_hidden(sK2,sK3)
% 2.17/1.02      | k4_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0 ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_0,plain,
% 2.17/1.02      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.17/1.02      inference(cnf_transformation,[],[f36]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_925,plain,
% 2.17/1.02      ( ~ r2_hidden(sK0(sK2,sK3),sK2) | ~ r2_hidden(sK2,sK0(sK2,sK3)) ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_926,plain,
% 2.17/1.02      ( r2_hidden(sK0(sK2,sK3),sK2) != iProver_top
% 2.17/1.02      | r2_hidden(sK2,sK0(sK2,sK3)) != iProver_top ),
% 2.17/1.02      inference(predicate_to_equality,[status(thm)],[c_925]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_909,plain,
% 2.17/1.02      ( r2_hidden(sK2,sK3)
% 2.17/1.02      | r2_hidden(sK3,sK2)
% 2.17/1.02      | ~ v3_ordinal1(sK2)
% 2.17/1.02      | ~ v3_ordinal1(sK3)
% 2.17/1.02      | sK2 = sK3 ),
% 2.17/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_910,plain,
% 2.17/1.02      ( sK2 = sK3
% 2.17/1.02      | r2_hidden(sK2,sK3) = iProver_top
% 2.17/1.02      | r2_hidden(sK3,sK2) = iProver_top
% 2.17/1.02      | v3_ordinal1(sK2) != iProver_top
% 2.17/1.02      | v3_ordinal1(sK3) != iProver_top ),
% 2.17/1.02      inference(predicate_to_equality,[status(thm)],[c_909]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_14,negated_conjecture,
% 2.17/1.02      ( ~ r2_xboole_0(sK3,sK2) ),
% 2.17/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_216,plain,
% 2.17/1.02      ( ~ r1_tarski(X0,X1) | X1 = X0 | sK2 != X1 | sK3 != X0 ),
% 2.17/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_14]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_217,plain,
% 2.17/1.02      ( ~ r1_tarski(sK3,sK2) | sK2 = sK3 ),
% 2.17/1.02      inference(unflattening,[status(thm)],[c_216]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_219,plain,
% 2.17/1.02      ( ~ r1_tarski(sK3,sK2) ),
% 2.17/1.02      inference(global_propositional_subsumption,
% 2.17/1.02                [status(thm)],
% 2.17/1.02                [c_217,c_15]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_249,plain,
% 2.17/1.02      ( ~ r2_hidden(sK0(X0,X1),X1) | sK2 != X1 | sK3 != X0 ),
% 2.17/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_219]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_250,plain,
% 2.17/1.02      ( ~ r2_hidden(sK0(sK3,sK2),sK2) ),
% 2.17/1.02      inference(unflattening,[status(thm)],[c_249]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_251,plain,
% 2.17/1.02      ( r2_hidden(sK0(sK3,sK2),sK2) != iProver_top ),
% 2.17/1.02      inference(predicate_to_equality,[status(thm)],[c_250]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_242,plain,
% 2.17/1.02      ( r2_hidden(sK0(X0,X1),X0) | sK2 != X1 | sK3 != X0 ),
% 2.17/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_219]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_243,plain,
% 2.17/1.02      ( r2_hidden(sK0(sK3,sK2),sK3) ),
% 2.17/1.02      inference(unflattening,[status(thm)],[c_242]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(c_244,plain,
% 2.17/1.02      ( r2_hidden(sK0(sK3,sK2),sK3) = iProver_top ),
% 2.17/1.02      inference(predicate_to_equality,[status(thm)],[c_243]) ).
% 2.17/1.02  
% 2.17/1.02  cnf(contradiction,plain,
% 2.17/1.02      ( $false ),
% 2.17/1.02      inference(minisat,
% 2.17/1.02                [status(thm)],
% 2.17/1.02                [c_2007,c_1552,c_1528,c_1268,c_1242,c_1057,c_1041,c_1023,
% 2.17/1.02                 c_1020,c_959,c_945,c_926,c_910,c_258,c_251,c_244,c_243,
% 2.17/1.02                 c_15,c_20,c_19]) ).
% 2.17/1.02  
% 2.17/1.02  
% 2.17/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.17/1.02  
% 2.17/1.02  ------                               Statistics
% 2.17/1.02  
% 2.17/1.02  ------ General
% 2.17/1.02  
% 2.17/1.02  abstr_ref_over_cycles:                  0
% 2.17/1.02  abstr_ref_under_cycles:                 0
% 2.17/1.02  gc_basic_clause_elim:                   0
% 2.17/1.02  forced_gc_time:                         0
% 2.17/1.02  parsing_time:                           0.01
% 2.17/1.02  unif_index_cands_time:                  0.
% 2.17/1.02  unif_index_add_time:                    0.
% 2.17/1.02  orderings_time:                         0.
% 2.17/1.02  out_proof_time:                         0.021
% 2.17/1.02  total_time:                             0.117
% 2.17/1.02  num_of_symbols:                         42
% 2.17/1.02  num_of_terms:                           1109
% 2.17/1.02  
% 2.17/1.02  ------ Preprocessing
% 2.17/1.02  
% 2.17/1.02  num_of_splits:                          0
% 2.17/1.02  num_of_split_atoms:                     0
% 2.17/1.02  num_of_reused_defs:                     0
% 2.17/1.02  num_eq_ax_congr_red:                    13
% 2.17/1.02  num_of_sem_filtered_clauses:            1
% 2.17/1.02  num_of_subtypes:                        0
% 2.17/1.02  monotx_restored_types:                  0
% 2.17/1.02  sat_num_of_epr_types:                   0
% 2.17/1.02  sat_num_of_non_cyclic_types:            0
% 2.17/1.02  sat_guarded_non_collapsed_types:        0
% 2.17/1.02  num_pure_diseq_elim:                    0
% 2.17/1.02  simp_replaced_by:                       0
% 2.17/1.02  res_preprocessed:                       78
% 2.17/1.02  prep_upred:                             0
% 2.17/1.02  prep_unflattend:                        12
% 2.17/1.02  smt_new_axioms:                         0
% 2.17/1.02  pred_elim_cands:                        2
% 2.17/1.02  pred_elim:                              2
% 2.17/1.02  pred_elim_cl:                           1
% 2.17/1.02  pred_elim_cycles:                       4
% 2.17/1.02  merged_defs:                            8
% 2.17/1.02  merged_defs_ncl:                        0
% 2.17/1.02  bin_hyper_res:                          8
% 2.17/1.02  prep_cycles:                            4
% 2.17/1.02  pred_elim_time:                         0.001
% 2.17/1.02  splitting_time:                         0.
% 2.17/1.02  sem_filter_time:                        0.
% 2.17/1.02  monotx_time:                            0.
% 2.17/1.02  subtype_inf_time:                       0.
% 2.17/1.02  
% 2.17/1.02  ------ Problem properties
% 2.17/1.02  
% 2.17/1.02  clauses:                                16
% 2.17/1.02  conjectures:                            3
% 2.17/1.02  epr:                                    7
% 2.17/1.02  horn:                                   15
% 2.17/1.02  ground:                                 7
% 2.17/1.02  unary:                                  7
% 2.17/1.02  binary:                                 5
% 2.17/1.02  lits:                                   31
% 2.17/1.02  lits_eq:                                4
% 2.17/1.02  fd_pure:                                0
% 2.17/1.02  fd_pseudo:                              0
% 2.17/1.02  fd_cond:                                0
% 2.17/1.02  fd_pseudo_cond:                         1
% 2.17/1.02  ac_symbols:                             0
% 2.17/1.02  
% 2.17/1.02  ------ Propositional Solver
% 2.17/1.02  
% 2.17/1.02  prop_solver_calls:                      28
% 2.17/1.02  prop_fast_solver_calls:                 402
% 2.17/1.02  smt_solver_calls:                       0
% 2.17/1.02  smt_fast_solver_calls:                  0
% 2.17/1.02  prop_num_of_clauses:                    646
% 2.17/1.02  prop_preprocess_simplified:             2765
% 2.17/1.02  prop_fo_subsumed:                       9
% 2.17/1.02  prop_solver_time:                       0.
% 2.17/1.02  smt_solver_time:                        0.
% 2.17/1.02  smt_fast_solver_time:                   0.
% 2.17/1.02  prop_fast_solver_time:                  0.
% 2.17/1.02  prop_unsat_core_time:                   0.
% 2.17/1.02  
% 2.17/1.02  ------ QBF
% 2.17/1.02  
% 2.17/1.02  qbf_q_res:                              0
% 2.17/1.02  qbf_num_tautologies:                    0
% 2.17/1.02  qbf_prep_cycles:                        0
% 2.17/1.02  
% 2.17/1.02  ------ BMC1
% 2.17/1.02  
% 2.17/1.02  bmc1_current_bound:                     -1
% 2.17/1.02  bmc1_last_solved_bound:                 -1
% 2.17/1.02  bmc1_unsat_core_size:                   -1
% 2.17/1.02  bmc1_unsat_core_parents_size:           -1
% 2.17/1.02  bmc1_merge_next_fun:                    0
% 2.17/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.17/1.02  
% 2.17/1.02  ------ Instantiation
% 2.17/1.02  
% 2.17/1.02  inst_num_of_clauses:                    205
% 2.17/1.02  inst_num_in_passive:                    40
% 2.17/1.02  inst_num_in_active:                     109
% 2.17/1.02  inst_num_in_unprocessed:                56
% 2.17/1.02  inst_num_of_loops:                      143
% 2.17/1.02  inst_num_of_learning_restarts:          0
% 2.17/1.02  inst_num_moves_active_passive:          30
% 2.17/1.02  inst_lit_activity:                      0
% 2.17/1.02  inst_lit_activity_moves:                0
% 2.17/1.02  inst_num_tautologies:                   0
% 2.17/1.02  inst_num_prop_implied:                  0
% 2.17/1.02  inst_num_existing_simplified:           0
% 2.17/1.02  inst_num_eq_res_simplified:             0
% 2.17/1.02  inst_num_child_elim:                    0
% 2.17/1.02  inst_num_of_dismatching_blockings:      12
% 2.17/1.02  inst_num_of_non_proper_insts:           201
% 2.17/1.02  inst_num_of_duplicates:                 0
% 2.17/1.02  inst_inst_num_from_inst_to_res:         0
% 2.17/1.02  inst_dismatching_checking_time:         0.
% 2.17/1.02  
% 2.17/1.02  ------ Resolution
% 2.17/1.02  
% 2.17/1.02  res_num_of_clauses:                     0
% 2.17/1.02  res_num_in_passive:                     0
% 2.17/1.02  res_num_in_active:                      0
% 2.17/1.02  res_num_of_loops:                       82
% 2.17/1.02  res_forward_subset_subsumed:            51
% 2.17/1.02  res_backward_subset_subsumed:           0
% 2.17/1.02  res_forward_subsumed:                   0
% 2.17/1.02  res_backward_subsumed:                  0
% 2.17/1.02  res_forward_subsumption_resolution:     0
% 2.17/1.02  res_backward_subsumption_resolution:    0
% 2.17/1.02  res_clause_to_clause_subsumption:       138
% 2.17/1.02  res_orphan_elimination:                 0
% 2.17/1.02  res_tautology_del:                      33
% 2.17/1.02  res_num_eq_res_simplified:              0
% 2.17/1.02  res_num_sel_changes:                    0
% 2.17/1.02  res_moves_from_active_to_pass:          0
% 2.17/1.02  
% 2.17/1.02  ------ Superposition
% 2.17/1.02  
% 2.17/1.02  sup_time_total:                         0.
% 2.17/1.02  sup_time_generating:                    0.
% 2.17/1.02  sup_time_sim_full:                      0.
% 2.17/1.02  sup_time_sim_immed:                     0.
% 2.17/1.02  
% 2.17/1.02  sup_num_of_clauses:                     42
% 2.17/1.02  sup_num_in_active:                      28
% 2.17/1.02  sup_num_in_passive:                     14
% 2.17/1.02  sup_num_of_loops:                       28
% 2.17/1.02  sup_fw_superposition:                   33
% 2.17/1.02  sup_bw_superposition:                   19
% 2.17/1.02  sup_immediate_simplified:               6
% 2.17/1.02  sup_given_eliminated:                   0
% 2.17/1.02  comparisons_done:                       0
% 2.17/1.02  comparisons_avoided:                    6
% 2.17/1.02  
% 2.17/1.02  ------ Simplifications
% 2.17/1.02  
% 2.17/1.02  
% 2.17/1.02  sim_fw_subset_subsumed:                 6
% 2.17/1.02  sim_bw_subset_subsumed:                 0
% 2.17/1.02  sim_fw_subsumed:                        0
% 2.17/1.02  sim_bw_subsumed:                        0
% 2.17/1.02  sim_fw_subsumption_res:                 0
% 2.17/1.02  sim_bw_subsumption_res:                 0
% 2.17/1.02  sim_tautology_del:                      9
% 2.17/1.02  sim_eq_tautology_del:                   1
% 2.17/1.02  sim_eq_res_simp:                        0
% 2.17/1.02  sim_fw_demodulated:                     0
% 2.17/1.02  sim_bw_demodulated:                     0
% 2.17/1.02  sim_light_normalised:                   0
% 2.17/1.02  sim_joinable_taut:                      0
% 2.17/1.02  sim_joinable_simp:                      0
% 2.17/1.02  sim_ac_normalised:                      0
% 2.17/1.02  sim_smt_subsumption:                    0
% 2.17/1.02  
%------------------------------------------------------------------------------
