%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:49 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 922 expanded)
%              Number of clauses        :   62 ( 204 expanded)
%              Number of leaves         :   12 ( 226 expanded)
%              Depth                    :   19
%              Number of atoms          :  323 (3666 expanded)
%              Number of equality atoms :   88 ( 394 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(X0,sK4)
          | ~ r2_hidden(X0,k1_ordinal1(sK4)) )
        & ( r1_ordinal1(X0,sK4)
          | r2_hidden(X0,k1_ordinal1(sK4)) )
        & v3_ordinal1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK3,X1)
            | ~ r2_hidden(sK3,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK3,X1)
            | r2_hidden(sK3,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ~ r1_ordinal1(sK3,sK4)
      | ~ r2_hidden(sK3,k1_ordinal1(sK4)) )
    & ( r1_ordinal1(sK3,sK4)
      | r2_hidden(sK3,k1_ordinal1(sK4)) )
    & v3_ordinal1(sK4)
    & v3_ordinal1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f39,f41,f40])).

fof(f77,plain,
    ( ~ r1_ordinal1(sK3,sK4)
    | ~ r2_hidden(sK3,k1_ordinal1(sK4)) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f79,plain,(
    ! [X0] : k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f67,f78])).

fof(f83,plain,
    ( ~ r1_ordinal1(sK3,sK4)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(definition_unfolding,[],[f77,f79])).

fof(f74,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,
    ( r1_ordinal1(sK3,sK4)
    | r2_hidden(sK3,k1_ordinal1(sK4)) ),
    inference(cnf_transformation,[],[f42])).

fof(f84,plain,
    ( r1_ordinal1(sK3,sK4)
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(definition_unfolding,[],[f76,f79])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f36])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) ) ),
    inference(definition_unfolding,[],[f70,f79])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f79])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f72,f79])).

fof(f95,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) ),
    inference(equality_resolution,[],[f80])).

cnf(c_27,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_28,negated_conjecture,
    ( ~ r1_ordinal1(sK3,sK4)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_240,plain,
    ( ~ r1_ordinal1(sK3,sK4)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(prop_impl,[status(thm)],[c_28])).

cnf(c_422,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_240])).

cnf(c_423,plain,
    ( r2_hidden(sK4,sK3)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_31,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_30,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_425,plain,
    ( r2_hidden(sK4,sK3)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_31,c_30])).

cnf(c_23,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_29,negated_conjecture,
    ( r1_ordinal1(sK3,sK4)
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_242,plain,
    ( r1_ordinal1(sK3,sK4)
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(prop_impl,[status(thm)],[c_29])).

cnf(c_450,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_242])).

cnf(c_451,plain,
    ( r1_tarski(sK3,sK4)
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_453,plain,
    ( r1_tarski(sK3,sK4)
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_451,c_31,c_30])).

cnf(c_1254,plain,
    ( r1_tarski(sK3,sK4)
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(prop_impl,[status(thm)],[c_31,c_30,c_451])).

cnf(c_1312,plain,
    ( r1_tarski(sK3,sK4)
    | r2_hidden(sK4,sK3) ),
    inference(bin_hyper_res,[status(thm)],[c_425,c_1254])).

cnf(c_2714,plain,
    ( r1_tarski(sK3,sK4) = iProver_top
    | r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1312])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_79,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_78,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_80,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_83,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_455,plain,
    ( r1_tarski(sK3,sK4) = iProver_top
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_1321,plain,
    ( r1_tarski(sK3,sK4) = iProver_top
    | r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1312])).

cnf(c_2079,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2782,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,sK4)
    | sK4 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_2079])).

cnf(c_2783,plain,
    ( sK4 != X0
    | sK3 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2782])).

cnf(c_2785,plain,
    ( sK4 != sK4
    | sK3 != sK4
    | r1_tarski(sK4,sK4) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2783])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2789,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2790,plain,
    ( r2_hidden(sK4,sK3) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2789])).

cnf(c_26,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2832,plain,
    ( r2_hidden(sK3,X0)
    | ~ r2_hidden(sK3,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)))
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2833,plain,
    ( sK3 = X0
    | r2_hidden(sK3,X0) = iProver_top
    | r2_hidden(sK3,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2832])).

cnf(c_2835,plain,
    ( sK3 = sK4
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2833])).

cnf(c_3279,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2714,c_79,c_80,c_83,c_455,c_1321,c_2785,c_2790,c_2835])).

cnf(c_2736,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5802,plain,
    ( sK4 = sK3
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3279,c_2736])).

cnf(c_32,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_33,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_22,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_436,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_240])).

cnf(c_437,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_439,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_31,c_30])).

cnf(c_441,plain,
    ( r1_tarski(sK3,sK4) != iProver_top
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2892,plain,
    ( r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2893,plain,
    ( r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2892])).

cnf(c_405,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_27,c_23])).

cnf(c_2897,plain,
    ( r1_tarski(X0,sK3)
    | r2_hidden(sK3,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_2898,plain,
    ( r1_tarski(X0,sK3) = iProver_top
    | r2_hidden(sK3,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2897])).

cnf(c_2900,plain,
    ( r1_tarski(sK4,sK3) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2898])).

cnf(c_6637,plain,
    ( sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5802,c_32,c_33,c_79,c_80,c_83,c_441,c_455,c_1321,c_2785,c_2790,c_2835,c_2893,c_2900])).

cnf(c_1252,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(prop_impl,[status(thm)],[c_31,c_30,c_437])).

cnf(c_2716,plain,
    ( r1_tarski(sK3,sK4) != iProver_top
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1252])).

cnf(c_6360,plain,
    ( r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2716,c_79,c_80,c_83,c_441,c_455,c_1321,c_2785,c_2790,c_2835])).

cnf(c_6640,plain,
    ( r2_hidden(sK3,k2_xboole_0(sK3,k2_enumset1(sK3,sK3,sK3,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6637,c_6360])).

cnf(c_24,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3080,plain,
    ( r2_hidden(sK3,k2_xboole_0(sK3,k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_3081,plain,
    ( r2_hidden(sK3,k2_xboole_0(sK3,k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3080])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6640,c_3081])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.63/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.00  
% 3.63/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.63/1.00  
% 3.63/1.00  ------  iProver source info
% 3.63/1.00  
% 3.63/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.63/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.63/1.00  git: non_committed_changes: false
% 3.63/1.00  git: last_make_outside_of_git: false
% 3.63/1.00  
% 3.63/1.00  ------ 
% 3.63/1.00  
% 3.63/1.00  ------ Input Options
% 3.63/1.00  
% 3.63/1.00  --out_options                           all
% 3.63/1.00  --tptp_safe_out                         true
% 3.63/1.00  --problem_path                          ""
% 3.63/1.00  --include_path                          ""
% 3.63/1.00  --clausifier                            res/vclausify_rel
% 3.63/1.00  --clausifier_options                    ""
% 3.63/1.00  --stdin                                 false
% 3.63/1.00  --stats_out                             all
% 3.63/1.00  
% 3.63/1.00  ------ General Options
% 3.63/1.00  
% 3.63/1.00  --fof                                   false
% 3.63/1.00  --time_out_real                         305.
% 3.63/1.00  --time_out_virtual                      -1.
% 3.63/1.00  --symbol_type_check                     false
% 3.63/1.00  --clausify_out                          false
% 3.63/1.00  --sig_cnt_out                           false
% 3.63/1.00  --trig_cnt_out                          false
% 3.63/1.00  --trig_cnt_out_tolerance                1.
% 3.63/1.00  --trig_cnt_out_sk_spl                   false
% 3.63/1.00  --abstr_cl_out                          false
% 3.63/1.00  
% 3.63/1.00  ------ Global Options
% 3.63/1.00  
% 3.63/1.00  --schedule                              default
% 3.63/1.00  --add_important_lit                     false
% 3.63/1.00  --prop_solver_per_cl                    1000
% 3.63/1.00  --min_unsat_core                        false
% 3.63/1.00  --soft_assumptions                      false
% 3.63/1.00  --soft_lemma_size                       3
% 3.63/1.00  --prop_impl_unit_size                   0
% 3.63/1.00  --prop_impl_unit                        []
% 3.63/1.00  --share_sel_clauses                     true
% 3.63/1.00  --reset_solvers                         false
% 3.63/1.00  --bc_imp_inh                            [conj_cone]
% 3.63/1.00  --conj_cone_tolerance                   3.
% 3.63/1.00  --extra_neg_conj                        none
% 3.63/1.00  --large_theory_mode                     true
% 3.63/1.00  --prolific_symb_bound                   200
% 3.63/1.00  --lt_threshold                          2000
% 3.63/1.00  --clause_weak_htbl                      true
% 3.63/1.00  --gc_record_bc_elim                     false
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing Options
% 3.63/1.00  
% 3.63/1.00  --preprocessing_flag                    true
% 3.63/1.00  --time_out_prep_mult                    0.1
% 3.63/1.00  --splitting_mode                        input
% 3.63/1.00  --splitting_grd                         true
% 3.63/1.00  --splitting_cvd                         false
% 3.63/1.00  --splitting_cvd_svl                     false
% 3.63/1.00  --splitting_nvd                         32
% 3.63/1.00  --sub_typing                            true
% 3.63/1.00  --prep_gs_sim                           true
% 3.63/1.00  --prep_unflatten                        true
% 3.63/1.00  --prep_res_sim                          true
% 3.63/1.00  --prep_upred                            true
% 3.63/1.00  --prep_sem_filter                       exhaustive
% 3.63/1.00  --prep_sem_filter_out                   false
% 3.63/1.00  --pred_elim                             true
% 3.63/1.00  --res_sim_input                         true
% 3.63/1.00  --eq_ax_congr_red                       true
% 3.63/1.00  --pure_diseq_elim                       true
% 3.63/1.00  --brand_transform                       false
% 3.63/1.00  --non_eq_to_eq                          false
% 3.63/1.00  --prep_def_merge                        true
% 3.63/1.00  --prep_def_merge_prop_impl              false
% 3.63/1.00  --prep_def_merge_mbd                    true
% 3.63/1.00  --prep_def_merge_tr_red                 false
% 3.63/1.00  --prep_def_merge_tr_cl                  false
% 3.63/1.00  --smt_preprocessing                     true
% 3.63/1.00  --smt_ac_axioms                         fast
% 3.63/1.00  --preprocessed_out                      false
% 3.63/1.00  --preprocessed_stats                    false
% 3.63/1.00  
% 3.63/1.00  ------ Abstraction refinement Options
% 3.63/1.00  
% 3.63/1.00  --abstr_ref                             []
% 3.63/1.00  --abstr_ref_prep                        false
% 3.63/1.00  --abstr_ref_until_sat                   false
% 3.63/1.00  --abstr_ref_sig_restrict                funpre
% 3.63/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/1.00  --abstr_ref_under                       []
% 3.63/1.00  
% 3.63/1.00  ------ SAT Options
% 3.63/1.00  
% 3.63/1.00  --sat_mode                              false
% 3.63/1.00  --sat_fm_restart_options                ""
% 3.63/1.00  --sat_gr_def                            false
% 3.63/1.00  --sat_epr_types                         true
% 3.63/1.00  --sat_non_cyclic_types                  false
% 3.63/1.00  --sat_finite_models                     false
% 3.63/1.00  --sat_fm_lemmas                         false
% 3.63/1.00  --sat_fm_prep                           false
% 3.63/1.00  --sat_fm_uc_incr                        true
% 3.63/1.00  --sat_out_model                         small
% 3.63/1.00  --sat_out_clauses                       false
% 3.63/1.00  
% 3.63/1.00  ------ QBF Options
% 3.63/1.00  
% 3.63/1.00  --qbf_mode                              false
% 3.63/1.00  --qbf_elim_univ                         false
% 3.63/1.00  --qbf_dom_inst                          none
% 3.63/1.00  --qbf_dom_pre_inst                      false
% 3.63/1.00  --qbf_sk_in                             false
% 3.63/1.00  --qbf_pred_elim                         true
% 3.63/1.00  --qbf_split                             512
% 3.63/1.00  
% 3.63/1.00  ------ BMC1 Options
% 3.63/1.00  
% 3.63/1.00  --bmc1_incremental                      false
% 3.63/1.00  --bmc1_axioms                           reachable_all
% 3.63/1.00  --bmc1_min_bound                        0
% 3.63/1.00  --bmc1_max_bound                        -1
% 3.63/1.00  --bmc1_max_bound_default                -1
% 3.63/1.00  --bmc1_symbol_reachability              true
% 3.63/1.00  --bmc1_property_lemmas                  false
% 3.63/1.00  --bmc1_k_induction                      false
% 3.63/1.00  --bmc1_non_equiv_states                 false
% 3.63/1.00  --bmc1_deadlock                         false
% 3.63/1.00  --bmc1_ucm                              false
% 3.63/1.00  --bmc1_add_unsat_core                   none
% 3.63/1.00  --bmc1_unsat_core_children              false
% 3.63/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/1.00  --bmc1_out_stat                         full
% 3.63/1.00  --bmc1_ground_init                      false
% 3.63/1.00  --bmc1_pre_inst_next_state              false
% 3.63/1.00  --bmc1_pre_inst_state                   false
% 3.63/1.00  --bmc1_pre_inst_reach_state             false
% 3.63/1.00  --bmc1_out_unsat_core                   false
% 3.63/1.00  --bmc1_aig_witness_out                  false
% 3.63/1.00  --bmc1_verbose                          false
% 3.63/1.00  --bmc1_dump_clauses_tptp                false
% 3.63/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.63/1.00  --bmc1_dump_file                        -
% 3.63/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.63/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.63/1.00  --bmc1_ucm_extend_mode                  1
% 3.63/1.00  --bmc1_ucm_init_mode                    2
% 3.63/1.00  --bmc1_ucm_cone_mode                    none
% 3.63/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.63/1.00  --bmc1_ucm_relax_model                  4
% 3.63/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.63/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/1.00  --bmc1_ucm_layered_model                none
% 3.63/1.00  --bmc1_ucm_max_lemma_size               10
% 3.63/1.00  
% 3.63/1.00  ------ AIG Options
% 3.63/1.00  
% 3.63/1.00  --aig_mode                              false
% 3.63/1.00  
% 3.63/1.00  ------ Instantiation Options
% 3.63/1.00  
% 3.63/1.00  --instantiation_flag                    true
% 3.63/1.00  --inst_sos_flag                         true
% 3.63/1.00  --inst_sos_phase                        true
% 3.63/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/1.00  --inst_lit_sel_side                     num_symb
% 3.63/1.00  --inst_solver_per_active                1400
% 3.63/1.00  --inst_solver_calls_frac                1.
% 3.63/1.00  --inst_passive_queue_type               priority_queues
% 3.63/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/1.00  --inst_passive_queues_freq              [25;2]
% 3.63/1.00  --inst_dismatching                      true
% 3.63/1.00  --inst_eager_unprocessed_to_passive     true
% 3.63/1.00  --inst_prop_sim_given                   true
% 3.63/1.00  --inst_prop_sim_new                     false
% 3.63/1.00  --inst_subs_new                         false
% 3.63/1.00  --inst_eq_res_simp                      false
% 3.63/1.00  --inst_subs_given                       false
% 3.63/1.00  --inst_orphan_elimination               true
% 3.63/1.00  --inst_learning_loop_flag               true
% 3.63/1.00  --inst_learning_start                   3000
% 3.63/1.00  --inst_learning_factor                  2
% 3.63/1.00  --inst_start_prop_sim_after_learn       3
% 3.63/1.00  --inst_sel_renew                        solver
% 3.63/1.00  --inst_lit_activity_flag                true
% 3.63/1.00  --inst_restr_to_given                   false
% 3.63/1.00  --inst_activity_threshold               500
% 3.63/1.00  --inst_out_proof                        true
% 3.63/1.00  
% 3.63/1.00  ------ Resolution Options
% 3.63/1.00  
% 3.63/1.00  --resolution_flag                       true
% 3.63/1.00  --res_lit_sel                           adaptive
% 3.63/1.00  --res_lit_sel_side                      none
% 3.63/1.00  --res_ordering                          kbo
% 3.63/1.00  --res_to_prop_solver                    active
% 3.63/1.00  --res_prop_simpl_new                    false
% 3.63/1.00  --res_prop_simpl_given                  true
% 3.63/1.00  --res_passive_queue_type                priority_queues
% 3.63/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/1.00  --res_passive_queues_freq               [15;5]
% 3.63/1.00  --res_forward_subs                      full
% 3.63/1.00  --res_backward_subs                     full
% 3.63/1.00  --res_forward_subs_resolution           true
% 3.63/1.00  --res_backward_subs_resolution          true
% 3.63/1.00  --res_orphan_elimination                true
% 3.63/1.00  --res_time_limit                        2.
% 3.63/1.00  --res_out_proof                         true
% 3.63/1.00  
% 3.63/1.00  ------ Superposition Options
% 3.63/1.00  
% 3.63/1.00  --superposition_flag                    true
% 3.63/1.00  --sup_passive_queue_type                priority_queues
% 3.63/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.63/1.00  --demod_completeness_check              fast
% 3.63/1.00  --demod_use_ground                      true
% 3.63/1.00  --sup_to_prop_solver                    passive
% 3.63/1.00  --sup_prop_simpl_new                    true
% 3.63/1.00  --sup_prop_simpl_given                  true
% 3.63/1.00  --sup_fun_splitting                     true
% 3.63/1.00  --sup_smt_interval                      50000
% 3.63/1.00  
% 3.63/1.00  ------ Superposition Simplification Setup
% 3.63/1.00  
% 3.63/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.63/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.63/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.63/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.63/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.63/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.63/1.00  --sup_immed_triv                        [TrivRules]
% 3.63/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.00  --sup_immed_bw_main                     []
% 3.63/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.63/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.00  --sup_input_bw                          []
% 3.63/1.00  
% 3.63/1.00  ------ Combination Options
% 3.63/1.00  
% 3.63/1.00  --comb_res_mult                         3
% 3.63/1.00  --comb_sup_mult                         2
% 3.63/1.00  --comb_inst_mult                        10
% 3.63/1.00  
% 3.63/1.00  ------ Debug Options
% 3.63/1.00  
% 3.63/1.00  --dbg_backtrace                         false
% 3.63/1.00  --dbg_dump_prop_clauses                 false
% 3.63/1.00  --dbg_dump_prop_clauses_file            -
% 3.63/1.00  --dbg_out_stat                          false
% 3.63/1.00  ------ Parsing...
% 3.63/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/1.00  ------ Proving...
% 3.63/1.00  ------ Problem Properties 
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  clauses                                 30
% 3.63/1.00  conjectures                             2
% 3.63/1.00  EPR                                     12
% 3.63/1.00  Horn                                    22
% 3.63/1.00  unary                                   5
% 3.63/1.00  binary                                  12
% 3.63/1.00  lits                                    76
% 3.63/1.00  lits eq                                 18
% 3.63/1.00  fd_pure                                 0
% 3.63/1.00  fd_pseudo                               0
% 3.63/1.00  fd_cond                                 0
% 3.63/1.00  fd_pseudo_cond                          7
% 3.63/1.00  AC symbols                              0
% 3.63/1.00  
% 3.63/1.00  ------ Schedule dynamic 5 is on 
% 3.63/1.00  
% 3.63/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  ------ 
% 3.63/1.00  Current options:
% 3.63/1.00  ------ 
% 3.63/1.00  
% 3.63/1.00  ------ Input Options
% 3.63/1.00  
% 3.63/1.00  --out_options                           all
% 3.63/1.00  --tptp_safe_out                         true
% 3.63/1.00  --problem_path                          ""
% 3.63/1.00  --include_path                          ""
% 3.63/1.00  --clausifier                            res/vclausify_rel
% 3.63/1.00  --clausifier_options                    ""
% 3.63/1.00  --stdin                                 false
% 3.63/1.00  --stats_out                             all
% 3.63/1.00  
% 3.63/1.00  ------ General Options
% 3.63/1.00  
% 3.63/1.00  --fof                                   false
% 3.63/1.00  --time_out_real                         305.
% 3.63/1.00  --time_out_virtual                      -1.
% 3.63/1.00  --symbol_type_check                     false
% 3.63/1.00  --clausify_out                          false
% 3.63/1.00  --sig_cnt_out                           false
% 3.63/1.00  --trig_cnt_out                          false
% 3.63/1.00  --trig_cnt_out_tolerance                1.
% 3.63/1.00  --trig_cnt_out_sk_spl                   false
% 3.63/1.00  --abstr_cl_out                          false
% 3.63/1.00  
% 3.63/1.00  ------ Global Options
% 3.63/1.00  
% 3.63/1.00  --schedule                              default
% 3.63/1.00  --add_important_lit                     false
% 3.63/1.00  --prop_solver_per_cl                    1000
% 3.63/1.00  --min_unsat_core                        false
% 3.63/1.00  --soft_assumptions                      false
% 3.63/1.00  --soft_lemma_size                       3
% 3.63/1.00  --prop_impl_unit_size                   0
% 3.63/1.00  --prop_impl_unit                        []
% 3.63/1.00  --share_sel_clauses                     true
% 3.63/1.00  --reset_solvers                         false
% 3.63/1.00  --bc_imp_inh                            [conj_cone]
% 3.63/1.00  --conj_cone_tolerance                   3.
% 3.63/1.00  --extra_neg_conj                        none
% 3.63/1.00  --large_theory_mode                     true
% 3.63/1.00  --prolific_symb_bound                   200
% 3.63/1.00  --lt_threshold                          2000
% 3.63/1.00  --clause_weak_htbl                      true
% 3.63/1.00  --gc_record_bc_elim                     false
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing Options
% 3.63/1.00  
% 3.63/1.00  --preprocessing_flag                    true
% 3.63/1.00  --time_out_prep_mult                    0.1
% 3.63/1.00  --splitting_mode                        input
% 3.63/1.00  --splitting_grd                         true
% 3.63/1.00  --splitting_cvd                         false
% 3.63/1.00  --splitting_cvd_svl                     false
% 3.63/1.00  --splitting_nvd                         32
% 3.63/1.00  --sub_typing                            true
% 3.63/1.00  --prep_gs_sim                           true
% 3.63/1.00  --prep_unflatten                        true
% 3.63/1.00  --prep_res_sim                          true
% 3.63/1.00  --prep_upred                            true
% 3.63/1.00  --prep_sem_filter                       exhaustive
% 3.63/1.00  --prep_sem_filter_out                   false
% 3.63/1.00  --pred_elim                             true
% 3.63/1.00  --res_sim_input                         true
% 3.63/1.00  --eq_ax_congr_red                       true
% 3.63/1.00  --pure_diseq_elim                       true
% 3.63/1.00  --brand_transform                       false
% 3.63/1.00  --non_eq_to_eq                          false
% 3.63/1.00  --prep_def_merge                        true
% 3.63/1.00  --prep_def_merge_prop_impl              false
% 3.63/1.00  --prep_def_merge_mbd                    true
% 3.63/1.00  --prep_def_merge_tr_red                 false
% 3.63/1.00  --prep_def_merge_tr_cl                  false
% 3.63/1.00  --smt_preprocessing                     true
% 3.63/1.00  --smt_ac_axioms                         fast
% 3.63/1.00  --preprocessed_out                      false
% 3.63/1.00  --preprocessed_stats                    false
% 3.63/1.00  
% 3.63/1.00  ------ Abstraction refinement Options
% 3.63/1.00  
% 3.63/1.00  --abstr_ref                             []
% 3.63/1.00  --abstr_ref_prep                        false
% 3.63/1.00  --abstr_ref_until_sat                   false
% 3.63/1.00  --abstr_ref_sig_restrict                funpre
% 3.63/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/1.00  --abstr_ref_under                       []
% 3.63/1.00  
% 3.63/1.00  ------ SAT Options
% 3.63/1.00  
% 3.63/1.00  --sat_mode                              false
% 3.63/1.00  --sat_fm_restart_options                ""
% 3.63/1.00  --sat_gr_def                            false
% 3.63/1.00  --sat_epr_types                         true
% 3.63/1.00  --sat_non_cyclic_types                  false
% 3.63/1.00  --sat_finite_models                     false
% 3.63/1.00  --sat_fm_lemmas                         false
% 3.63/1.00  --sat_fm_prep                           false
% 3.63/1.00  --sat_fm_uc_incr                        true
% 3.63/1.00  --sat_out_model                         small
% 3.63/1.00  --sat_out_clauses                       false
% 3.63/1.00  
% 3.63/1.00  ------ QBF Options
% 3.63/1.00  
% 3.63/1.00  --qbf_mode                              false
% 3.63/1.00  --qbf_elim_univ                         false
% 3.63/1.00  --qbf_dom_inst                          none
% 3.63/1.00  --qbf_dom_pre_inst                      false
% 3.63/1.00  --qbf_sk_in                             false
% 3.63/1.00  --qbf_pred_elim                         true
% 3.63/1.00  --qbf_split                             512
% 3.63/1.00  
% 3.63/1.00  ------ BMC1 Options
% 3.63/1.00  
% 3.63/1.00  --bmc1_incremental                      false
% 3.63/1.00  --bmc1_axioms                           reachable_all
% 3.63/1.00  --bmc1_min_bound                        0
% 3.63/1.00  --bmc1_max_bound                        -1
% 3.63/1.00  --bmc1_max_bound_default                -1
% 3.63/1.00  --bmc1_symbol_reachability              true
% 3.63/1.00  --bmc1_property_lemmas                  false
% 3.63/1.00  --bmc1_k_induction                      false
% 3.63/1.00  --bmc1_non_equiv_states                 false
% 3.63/1.00  --bmc1_deadlock                         false
% 3.63/1.00  --bmc1_ucm                              false
% 3.63/1.00  --bmc1_add_unsat_core                   none
% 3.63/1.00  --bmc1_unsat_core_children              false
% 3.63/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/1.00  --bmc1_out_stat                         full
% 3.63/1.00  --bmc1_ground_init                      false
% 3.63/1.00  --bmc1_pre_inst_next_state              false
% 3.63/1.00  --bmc1_pre_inst_state                   false
% 3.63/1.00  --bmc1_pre_inst_reach_state             false
% 3.63/1.00  --bmc1_out_unsat_core                   false
% 3.63/1.00  --bmc1_aig_witness_out                  false
% 3.63/1.00  --bmc1_verbose                          false
% 3.63/1.00  --bmc1_dump_clauses_tptp                false
% 3.63/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.63/1.00  --bmc1_dump_file                        -
% 3.63/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.63/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.63/1.00  --bmc1_ucm_extend_mode                  1
% 3.63/1.00  --bmc1_ucm_init_mode                    2
% 3.63/1.00  --bmc1_ucm_cone_mode                    none
% 3.63/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.63/1.00  --bmc1_ucm_relax_model                  4
% 3.63/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.63/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/1.00  --bmc1_ucm_layered_model                none
% 3.63/1.00  --bmc1_ucm_max_lemma_size               10
% 3.63/1.00  
% 3.63/1.00  ------ AIG Options
% 3.63/1.00  
% 3.63/1.00  --aig_mode                              false
% 3.63/1.00  
% 3.63/1.00  ------ Instantiation Options
% 3.63/1.00  
% 3.63/1.00  --instantiation_flag                    true
% 3.63/1.00  --inst_sos_flag                         true
% 3.63/1.00  --inst_sos_phase                        true
% 3.63/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/1.00  --inst_lit_sel_side                     none
% 3.63/1.00  --inst_solver_per_active                1400
% 3.63/1.00  --inst_solver_calls_frac                1.
% 3.63/1.00  --inst_passive_queue_type               priority_queues
% 3.63/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/1.00  --inst_passive_queues_freq              [25;2]
% 3.63/1.00  --inst_dismatching                      true
% 3.63/1.00  --inst_eager_unprocessed_to_passive     true
% 3.63/1.00  --inst_prop_sim_given                   true
% 3.63/1.00  --inst_prop_sim_new                     false
% 3.63/1.00  --inst_subs_new                         false
% 3.63/1.00  --inst_eq_res_simp                      false
% 3.63/1.00  --inst_subs_given                       false
% 3.63/1.00  --inst_orphan_elimination               true
% 3.63/1.00  --inst_learning_loop_flag               true
% 3.63/1.00  --inst_learning_start                   3000
% 3.63/1.00  --inst_learning_factor                  2
% 3.63/1.00  --inst_start_prop_sim_after_learn       3
% 3.63/1.00  --inst_sel_renew                        solver
% 3.63/1.00  --inst_lit_activity_flag                true
% 3.63/1.00  --inst_restr_to_given                   false
% 3.63/1.00  --inst_activity_threshold               500
% 3.63/1.00  --inst_out_proof                        true
% 3.63/1.00  
% 3.63/1.00  ------ Resolution Options
% 3.63/1.00  
% 3.63/1.00  --resolution_flag                       false
% 3.63/1.00  --res_lit_sel                           adaptive
% 3.63/1.00  --res_lit_sel_side                      none
% 3.63/1.00  --res_ordering                          kbo
% 3.63/1.00  --res_to_prop_solver                    active
% 3.63/1.00  --res_prop_simpl_new                    false
% 3.63/1.00  --res_prop_simpl_given                  true
% 3.63/1.00  --res_passive_queue_type                priority_queues
% 3.63/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/1.00  --res_passive_queues_freq               [15;5]
% 3.63/1.00  --res_forward_subs                      full
% 3.63/1.00  --res_backward_subs                     full
% 3.63/1.00  --res_forward_subs_resolution           true
% 3.63/1.00  --res_backward_subs_resolution          true
% 3.63/1.00  --res_orphan_elimination                true
% 3.63/1.00  --res_time_limit                        2.
% 3.63/1.00  --res_out_proof                         true
% 3.63/1.00  
% 3.63/1.00  ------ Superposition Options
% 3.63/1.00  
% 3.63/1.00  --superposition_flag                    true
% 3.63/1.00  --sup_passive_queue_type                priority_queues
% 3.63/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.63/1.00  --demod_completeness_check              fast
% 3.63/1.00  --demod_use_ground                      true
% 3.63/1.00  --sup_to_prop_solver                    passive
% 3.63/1.00  --sup_prop_simpl_new                    true
% 3.63/1.00  --sup_prop_simpl_given                  true
% 3.63/1.00  --sup_fun_splitting                     true
% 3.63/1.00  --sup_smt_interval                      50000
% 3.63/1.00  
% 3.63/1.00  ------ Superposition Simplification Setup
% 3.63/1.00  
% 3.63/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.63/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.63/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.63/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.63/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.63/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.63/1.00  --sup_immed_triv                        [TrivRules]
% 3.63/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.00  --sup_immed_bw_main                     []
% 3.63/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.63/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.00  --sup_input_bw                          []
% 3.63/1.00  
% 3.63/1.00  ------ Combination Options
% 3.63/1.00  
% 3.63/1.00  --comb_res_mult                         3
% 3.63/1.00  --comb_sup_mult                         2
% 3.63/1.00  --comb_inst_mult                        10
% 3.63/1.00  
% 3.63/1.00  ------ Debug Options
% 3.63/1.00  
% 3.63/1.00  --dbg_backtrace                         false
% 3.63/1.00  --dbg_dump_prop_clauses                 false
% 3.63/1.00  --dbg_dump_prop_clauses_file            -
% 3.63/1.00  --dbg_out_stat                          false
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  ------ Proving...
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  % SZS status Theorem for theBenchmark.p
% 3.63/1.00  
% 3.63/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.63/1.00  
% 3.63/1.00  fof(f10,axiom,(
% 3.63/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f17,plain,(
% 3.63/1.00    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.63/1.00    inference(ennf_transformation,[],[f10])).
% 3.63/1.00  
% 3.63/1.00  fof(f18,plain,(
% 3.63/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.63/1.00    inference(flattening,[],[f17])).
% 3.63/1.00  
% 3.63/1.00  fof(f73,plain,(
% 3.63/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f18])).
% 3.63/1.00  
% 3.63/1.00  fof(f11,conjecture,(
% 3.63/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f12,negated_conjecture,(
% 3.63/1.00    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.63/1.00    inference(negated_conjecture,[],[f11])).
% 3.63/1.00  
% 3.63/1.00  fof(f19,plain,(
% 3.63/1.00    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.63/1.00    inference(ennf_transformation,[],[f12])).
% 3.63/1.00  
% 3.63/1.00  fof(f38,plain,(
% 3.63/1.00    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.63/1.00    inference(nnf_transformation,[],[f19])).
% 3.63/1.00  
% 3.63/1.00  fof(f39,plain,(
% 3.63/1.00    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.63/1.00    inference(flattening,[],[f38])).
% 3.63/1.00  
% 3.63/1.00  fof(f41,plain,(
% 3.63/1.00    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK4) | ~r2_hidden(X0,k1_ordinal1(sK4))) & (r1_ordinal1(X0,sK4) | r2_hidden(X0,k1_ordinal1(sK4))) & v3_ordinal1(sK4))) )),
% 3.63/1.00    introduced(choice_axiom,[])).
% 3.63/1.00  
% 3.63/1.00  fof(f40,plain,(
% 3.63/1.00    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK3,X1) | ~r2_hidden(sK3,k1_ordinal1(X1))) & (r1_ordinal1(sK3,X1) | r2_hidden(sK3,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK3))),
% 3.63/1.00    introduced(choice_axiom,[])).
% 3.63/1.00  
% 3.63/1.00  fof(f42,plain,(
% 3.63/1.00    ((~r1_ordinal1(sK3,sK4) | ~r2_hidden(sK3,k1_ordinal1(sK4))) & (r1_ordinal1(sK3,sK4) | r2_hidden(sK3,k1_ordinal1(sK4))) & v3_ordinal1(sK4)) & v3_ordinal1(sK3)),
% 3.63/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f39,f41,f40])).
% 3.63/1.00  
% 3.63/1.00  fof(f77,plain,(
% 3.63/1.00    ~r1_ordinal1(sK3,sK4) | ~r2_hidden(sK3,k1_ordinal1(sK4))),
% 3.63/1.00    inference(cnf_transformation,[],[f42])).
% 3.63/1.00  
% 3.63/1.00  fof(f7,axiom,(
% 3.63/1.00    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f67,plain,(
% 3.63/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f7])).
% 3.63/1.00  
% 3.63/1.00  fof(f4,axiom,(
% 3.63/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f53,plain,(
% 3.63/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f4])).
% 3.63/1.00  
% 3.63/1.00  fof(f5,axiom,(
% 3.63/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f54,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f5])).
% 3.63/1.00  
% 3.63/1.00  fof(f78,plain,(
% 3.63/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.63/1.00    inference(definition_unfolding,[],[f53,f54])).
% 3.63/1.00  
% 3.63/1.00  fof(f79,plain,(
% 3.63/1.00    ( ! [X0] : (k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)) = k1_ordinal1(X0)) )),
% 3.63/1.00    inference(definition_unfolding,[],[f67,f78])).
% 3.63/1.00  
% 3.63/1.00  fof(f83,plain,(
% 3.63/1.00    ~r1_ordinal1(sK3,sK4) | ~r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))),
% 3.63/1.00    inference(definition_unfolding,[],[f77,f79])).
% 3.63/1.00  
% 3.63/1.00  fof(f74,plain,(
% 3.63/1.00    v3_ordinal1(sK3)),
% 3.63/1.00    inference(cnf_transformation,[],[f42])).
% 3.63/1.00  
% 3.63/1.00  fof(f75,plain,(
% 3.63/1.00    v3_ordinal1(sK4)),
% 3.63/1.00    inference(cnf_transformation,[],[f42])).
% 3.63/1.00  
% 3.63/1.00  fof(f8,axiom,(
% 3.63/1.00    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f15,plain,(
% 3.63/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.63/1.00    inference(ennf_transformation,[],[f8])).
% 3.63/1.00  
% 3.63/1.00  fof(f16,plain,(
% 3.63/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.63/1.00    inference(flattening,[],[f15])).
% 3.63/1.00  
% 3.63/1.00  fof(f35,plain,(
% 3.63/1.00    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.63/1.00    inference(nnf_transformation,[],[f16])).
% 3.63/1.00  
% 3.63/1.00  fof(f68,plain,(
% 3.63/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f35])).
% 3.63/1.00  
% 3.63/1.00  fof(f76,plain,(
% 3.63/1.00    r1_ordinal1(sK3,sK4) | r2_hidden(sK3,k1_ordinal1(sK4))),
% 3.63/1.00    inference(cnf_transformation,[],[f42])).
% 3.63/1.00  
% 3.63/1.00  fof(f84,plain,(
% 3.63/1.00    r1_ordinal1(sK3,sK4) | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))),
% 3.63/1.00    inference(definition_unfolding,[],[f76,f79])).
% 3.63/1.00  
% 3.63/1.00  fof(f3,axiom,(
% 3.63/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f27,plain,(
% 3.63/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.63/1.00    inference(nnf_transformation,[],[f3])).
% 3.63/1.00  
% 3.63/1.00  fof(f28,plain,(
% 3.63/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.63/1.00    inference(flattening,[],[f27])).
% 3.63/1.00  
% 3.63/1.00  fof(f50,plain,(
% 3.63/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.63/1.00    inference(cnf_transformation,[],[f28])).
% 3.63/1.00  
% 3.63/1.00  fof(f89,plain,(
% 3.63/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.63/1.00    inference(equality_resolution,[],[f50])).
% 3.63/1.00  
% 3.63/1.00  fof(f52,plain,(
% 3.63/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f28])).
% 3.63/1.00  
% 3.63/1.00  fof(f1,axiom,(
% 3.63/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f13,plain,(
% 3.63/1.00    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 3.63/1.00    inference(ennf_transformation,[],[f1])).
% 3.63/1.00  
% 3.63/1.00  fof(f43,plain,(
% 3.63/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f13])).
% 3.63/1.00  
% 3.63/1.00  fof(f9,axiom,(
% 3.63/1.00    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 3.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f36,plain,(
% 3.63/1.00    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 3.63/1.00    inference(nnf_transformation,[],[f9])).
% 3.63/1.00  
% 3.63/1.00  fof(f37,plain,(
% 3.63/1.00    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 3.63/1.00    inference(flattening,[],[f36])).
% 3.63/1.00  
% 3.63/1.00  fof(f70,plain,(
% 3.63/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 3.63/1.00    inference(cnf_transformation,[],[f37])).
% 3.63/1.00  
% 3.63/1.00  fof(f82,plain,(
% 3.63/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))) )),
% 3.63/1.00    inference(definition_unfolding,[],[f70,f79])).
% 3.63/1.00  
% 3.63/1.00  fof(f69,plain,(
% 3.63/1.00    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f35])).
% 3.63/1.00  
% 3.63/1.00  fof(f71,plain,(
% 3.63/1.00    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f37])).
% 3.63/1.00  
% 3.63/1.00  fof(f81,plain,(
% 3.63/1.00    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) | ~r2_hidden(X0,X1)) )),
% 3.63/1.00    inference(definition_unfolding,[],[f71,f79])).
% 3.63/1.00  
% 3.63/1.00  fof(f72,plain,(
% 3.63/1.00    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 3.63/1.00    inference(cnf_transformation,[],[f37])).
% 3.63/1.00  
% 3.63/1.00  fof(f80,plain,(
% 3.63/1.00    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) | X0 != X1) )),
% 3.63/1.00    inference(definition_unfolding,[],[f72,f79])).
% 3.63/1.00  
% 3.63/1.00  fof(f95,plain,(
% 3.63/1.00    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))) )),
% 3.63/1.00    inference(equality_resolution,[],[f80])).
% 3.63/1.00  
% 3.63/1.00  cnf(c_27,plain,
% 3.63/1.00      ( r1_ordinal1(X0,X1)
% 3.63/1.00      | r2_hidden(X1,X0)
% 3.63/1.00      | ~ v3_ordinal1(X1)
% 3.63/1.00      | ~ v3_ordinal1(X0) ),
% 3.63/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_28,negated_conjecture,
% 3.63/1.00      ( ~ r1_ordinal1(sK3,sK4)
% 3.63/1.00      | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 3.63/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_240,plain,
% 3.63/1.00      ( ~ r1_ordinal1(sK3,sK4)
% 3.63/1.00      | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 3.63/1.00      inference(prop_impl,[status(thm)],[c_28]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_422,plain,
% 3.63/1.00      ( r2_hidden(X0,X1)
% 3.63/1.00      | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.63/1.00      | ~ v3_ordinal1(X1)
% 3.63/1.00      | ~ v3_ordinal1(X0)
% 3.63/1.00      | sK4 != X0
% 3.63/1.00      | sK3 != X1 ),
% 3.63/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_240]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_423,plain,
% 3.63/1.00      ( r2_hidden(sK4,sK3)
% 3.63/1.00      | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.63/1.00      | ~ v3_ordinal1(sK4)
% 3.63/1.00      | ~ v3_ordinal1(sK3) ),
% 3.63/1.00      inference(unflattening,[status(thm)],[c_422]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_31,negated_conjecture,
% 3.63/1.00      ( v3_ordinal1(sK3) ),
% 3.63/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_30,negated_conjecture,
% 3.63/1.00      ( v3_ordinal1(sK4) ),
% 3.63/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_425,plain,
% 3.63/1.00      ( r2_hidden(sK4,sK3)
% 3.63/1.00      | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 3.63/1.00      inference(global_propositional_subsumption,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_423,c_31,c_30]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_23,plain,
% 3.63/1.00      ( ~ r1_ordinal1(X0,X1)
% 3.63/1.00      | r1_tarski(X0,X1)
% 3.63/1.00      | ~ v3_ordinal1(X1)
% 3.63/1.00      | ~ v3_ordinal1(X0) ),
% 3.63/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_29,negated_conjecture,
% 3.63/1.00      ( r1_ordinal1(sK3,sK4)
% 3.63/1.00      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 3.63/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_242,plain,
% 3.63/1.00      ( r1_ordinal1(sK3,sK4)
% 3.63/1.00      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 3.63/1.00      inference(prop_impl,[status(thm)],[c_29]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_450,plain,
% 3.63/1.00      ( r1_tarski(X0,X1)
% 3.63/1.00      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.63/1.00      | ~ v3_ordinal1(X0)
% 3.63/1.00      | ~ v3_ordinal1(X1)
% 3.63/1.00      | sK4 != X1
% 3.63/1.00      | sK3 != X0 ),
% 3.63/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_242]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_451,plain,
% 3.63/1.00      ( r1_tarski(sK3,sK4)
% 3.63/1.00      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.63/1.00      | ~ v3_ordinal1(sK4)
% 3.63/1.00      | ~ v3_ordinal1(sK3) ),
% 3.63/1.00      inference(unflattening,[status(thm)],[c_450]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_453,plain,
% 3.63/1.00      ( r1_tarski(sK3,sK4)
% 3.63/1.00      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 3.63/1.00      inference(global_propositional_subsumption,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_451,c_31,c_30]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1254,plain,
% 3.63/1.00      ( r1_tarski(sK3,sK4)
% 3.63/1.00      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 3.63/1.00      inference(prop_impl,[status(thm)],[c_31,c_30,c_451]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1312,plain,
% 3.63/1.00      ( r1_tarski(sK3,sK4) | r2_hidden(sK4,sK3) ),
% 3.63/1.00      inference(bin_hyper_res,[status(thm)],[c_425,c_1254]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2714,plain,
% 3.63/1.00      ( r1_tarski(sK3,sK4) = iProver_top
% 3.63/1.00      | r2_hidden(sK4,sK3) = iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_1312]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_9,plain,
% 3.63/1.00      ( r1_tarski(X0,X0) ),
% 3.63/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_79,plain,
% 3.63/1.00      ( r1_tarski(sK4,sK4) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_78,plain,
% 3.63/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_80,plain,
% 3.63/1.00      ( r1_tarski(sK4,sK4) = iProver_top ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_78]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_7,plain,
% 3.63/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.63/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_83,plain,
% 3.63/1.00      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_455,plain,
% 3.63/1.00      ( r1_tarski(sK3,sK4) = iProver_top
% 3.63/1.00      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1321,plain,
% 3.63/1.00      ( r1_tarski(sK3,sK4) = iProver_top
% 3.63/1.00      | r2_hidden(sK4,sK3) = iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_1312]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2079,plain,
% 3.63/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.63/1.00      theory(equality) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2782,plain,
% 3.63/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,sK4) | sK4 != X1 | sK3 != X0 ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2079]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2783,plain,
% 3.63/1.00      ( sK4 != X0
% 3.63/1.00      | sK3 != X1
% 3.63/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.63/1.00      | r1_tarski(sK3,sK4) = iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_2782]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2785,plain,
% 3.63/1.00      ( sK4 != sK4
% 3.63/1.00      | sK3 != sK4
% 3.63/1.00      | r1_tarski(sK4,sK4) != iProver_top
% 3.63/1.00      | r1_tarski(sK3,sK4) = iProver_top ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2783]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_0,plain,
% 3.63/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.63/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2789,plain,
% 3.63/1.00      ( ~ r2_hidden(sK4,sK3) | ~ r2_hidden(sK3,sK4) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2790,plain,
% 3.63/1.00      ( r2_hidden(sK4,sK3) != iProver_top
% 3.63/1.00      | r2_hidden(sK3,sK4) != iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_2789]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_26,plain,
% 3.63/1.00      ( r2_hidden(X0,X1)
% 3.63/1.00      | ~ r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))
% 3.63/1.00      | X0 = X1 ),
% 3.63/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2832,plain,
% 3.63/1.00      ( r2_hidden(sK3,X0)
% 3.63/1.00      | ~ r2_hidden(sK3,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)))
% 3.63/1.00      | sK3 = X0 ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2833,plain,
% 3.63/1.00      ( sK3 = X0
% 3.63/1.00      | r2_hidden(sK3,X0) = iProver_top
% 3.63/1.00      | r2_hidden(sK3,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_2832]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2835,plain,
% 3.63/1.00      ( sK3 = sK4
% 3.63/1.00      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top
% 3.63/1.00      | r2_hidden(sK3,sK4) = iProver_top ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2833]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3279,plain,
% 3.63/1.00      ( r1_tarski(sK3,sK4) = iProver_top ),
% 3.63/1.00      inference(global_propositional_subsumption,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_2714,c_79,c_80,c_83,c_455,c_1321,c_2785,c_2790,c_2835]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2736,plain,
% 3.63/1.00      ( X0 = X1
% 3.63/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.63/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_5802,plain,
% 3.63/1.00      ( sK4 = sK3 | r1_tarski(sK4,sK3) != iProver_top ),
% 3.63/1.00      inference(superposition,[status(thm)],[c_3279,c_2736]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_32,plain,
% 3.63/1.00      ( v3_ordinal1(sK3) = iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_33,plain,
% 3.63/1.00      ( v3_ordinal1(sK4) = iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_22,plain,
% 3.63/1.00      ( r1_ordinal1(X0,X1)
% 3.63/1.00      | ~ r1_tarski(X0,X1)
% 3.63/1.00      | ~ v3_ordinal1(X1)
% 3.63/1.00      | ~ v3_ordinal1(X0) ),
% 3.63/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_436,plain,
% 3.63/1.00      ( ~ r1_tarski(X0,X1)
% 3.63/1.00      | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.63/1.00      | ~ v3_ordinal1(X0)
% 3.63/1.00      | ~ v3_ordinal1(X1)
% 3.63/1.00      | sK4 != X1
% 3.63/1.00      | sK3 != X0 ),
% 3.63/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_240]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_437,plain,
% 3.63/1.00      ( ~ r1_tarski(sK3,sK4)
% 3.63/1.00      | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.63/1.00      | ~ v3_ordinal1(sK4)
% 3.63/1.00      | ~ v3_ordinal1(sK3) ),
% 3.63/1.00      inference(unflattening,[status(thm)],[c_436]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_439,plain,
% 3.63/1.00      ( ~ r1_tarski(sK3,sK4)
% 3.63/1.00      | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 3.63/1.00      inference(global_propositional_subsumption,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_437,c_31,c_30]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_441,plain,
% 3.63/1.00      ( r1_tarski(sK3,sK4) != iProver_top
% 3.63/1.00      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_25,plain,
% 3.63/1.00      ( ~ r2_hidden(X0,X1)
% 3.63/1.00      | r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) ),
% 3.63/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2892,plain,
% 3.63/1.00      ( r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.63/1.00      | ~ r2_hidden(sK3,sK4) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2893,plain,
% 3.63/1.00      ( r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top
% 3.63/1.00      | r2_hidden(sK3,sK4) != iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_2892]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_405,plain,
% 3.63/1.00      ( r1_tarski(X0,X1)
% 3.63/1.00      | r2_hidden(X1,X0)
% 3.63/1.00      | ~ v3_ordinal1(X0)
% 3.63/1.00      | ~ v3_ordinal1(X1) ),
% 3.63/1.00      inference(resolution,[status(thm)],[c_27,c_23]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2897,plain,
% 3.63/1.00      ( r1_tarski(X0,sK3)
% 3.63/1.00      | r2_hidden(sK3,X0)
% 3.63/1.00      | ~ v3_ordinal1(X0)
% 3.63/1.00      | ~ v3_ordinal1(sK3) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_405]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2898,plain,
% 3.63/1.00      ( r1_tarski(X0,sK3) = iProver_top
% 3.63/1.00      | r2_hidden(sK3,X0) = iProver_top
% 3.63/1.00      | v3_ordinal1(X0) != iProver_top
% 3.63/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_2897]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2900,plain,
% 3.63/1.00      ( r1_tarski(sK4,sK3) = iProver_top
% 3.63/1.00      | r2_hidden(sK3,sK4) = iProver_top
% 3.63/1.00      | v3_ordinal1(sK4) != iProver_top
% 3.63/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2898]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_6637,plain,
% 3.63/1.00      ( sK4 = sK3 ),
% 3.63/1.00      inference(global_propositional_subsumption,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_5802,c_32,c_33,c_79,c_80,c_83,c_441,c_455,c_1321,
% 3.63/1.00                 c_2785,c_2790,c_2835,c_2893,c_2900]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1252,plain,
% 3.63/1.00      ( ~ r1_tarski(sK3,sK4)
% 3.63/1.00      | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 3.63/1.00      inference(prop_impl,[status(thm)],[c_31,c_30,c_437]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2716,plain,
% 3.63/1.00      ( r1_tarski(sK3,sK4) != iProver_top
% 3.63/1.00      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_1252]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_6360,plain,
% 3.63/1.00      ( r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
% 3.63/1.00      inference(global_propositional_subsumption,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_2716,c_79,c_80,c_83,c_441,c_455,c_1321,c_2785,c_2790,
% 3.63/1.00                 c_2835]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_6640,plain,
% 3.63/1.00      ( r2_hidden(sK3,k2_xboole_0(sK3,k2_enumset1(sK3,sK3,sK3,sK3))) != iProver_top ),
% 3.63/1.00      inference(demodulation,[status(thm)],[c_6637,c_6360]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_24,plain,
% 3.63/1.00      ( r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) ),
% 3.63/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3080,plain,
% 3.63/1.00      ( r2_hidden(sK3,k2_xboole_0(sK3,k2_enumset1(sK3,sK3,sK3,sK3))) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3081,plain,
% 3.63/1.00      ( r2_hidden(sK3,k2_xboole_0(sK3,k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_3080]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(contradiction,plain,
% 3.63/1.00      ( $false ),
% 3.63/1.00      inference(minisat,[status(thm)],[c_6640,c_3081]) ).
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.63/1.00  
% 3.63/1.00  ------                               Statistics
% 3.63/1.00  
% 3.63/1.00  ------ General
% 3.63/1.00  
% 3.63/1.00  abstr_ref_over_cycles:                  0
% 3.63/1.00  abstr_ref_under_cycles:                 0
% 3.63/1.00  gc_basic_clause_elim:                   0
% 3.63/1.00  forced_gc_time:                         0
% 3.63/1.00  parsing_time:                           0.015
% 3.63/1.00  unif_index_cands_time:                  0.
% 3.63/1.00  unif_index_add_time:                    0.
% 3.63/1.00  orderings_time:                         0.
% 3.63/1.00  out_proof_time:                         0.016
% 3.63/1.00  total_time:                             0.263
% 3.63/1.00  num_of_symbols:                         42
% 3.63/1.00  num_of_terms:                           7808
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing
% 3.63/1.00  
% 3.63/1.00  num_of_splits:                          0
% 3.63/1.00  num_of_split_atoms:                     0
% 3.63/1.00  num_of_reused_defs:                     0
% 3.63/1.00  num_eq_ax_congr_red:                    38
% 3.63/1.00  num_of_sem_filtered_clauses:            1
% 3.63/1.00  num_of_subtypes:                        0
% 3.63/1.00  monotx_restored_types:                  0
% 3.63/1.00  sat_num_of_epr_types:                   0
% 3.63/1.00  sat_num_of_non_cyclic_types:            0
% 3.63/1.00  sat_guarded_non_collapsed_types:        0
% 3.63/1.00  num_pure_diseq_elim:                    0
% 3.63/1.00  simp_replaced_by:                       0
% 3.63/1.00  res_preprocessed:                       138
% 3.63/1.00  prep_upred:                             0
% 3.63/1.00  prep_unflattend:                        66
% 3.63/1.00  smt_new_axioms:                         0
% 3.63/1.00  pred_elim_cands:                        4
% 3.63/1.00  pred_elim:                              1
% 3.63/1.00  pred_elim_cl:                           1
% 3.63/1.00  pred_elim_cycles:                       3
% 3.63/1.00  merged_defs:                            8
% 3.63/1.00  merged_defs_ncl:                        0
% 3.63/1.00  bin_hyper_res:                          9
% 3.63/1.00  prep_cycles:                            4
% 3.63/1.00  pred_elim_time:                         0.019
% 3.63/1.00  splitting_time:                         0.
% 3.63/1.00  sem_filter_time:                        0.
% 3.63/1.00  monotx_time:                            0.001
% 3.63/1.00  subtype_inf_time:                       0.
% 3.63/1.00  
% 3.63/1.00  ------ Problem properties
% 3.63/1.00  
% 3.63/1.00  clauses:                                30
% 3.63/1.00  conjectures:                            2
% 3.63/1.00  epr:                                    12
% 3.63/1.00  horn:                                   22
% 3.63/1.00  ground:                                 5
% 3.63/1.00  unary:                                  5
% 3.63/1.00  binary:                                 12
% 3.63/1.00  lits:                                   76
% 3.63/1.00  lits_eq:                                18
% 3.63/1.00  fd_pure:                                0
% 3.63/1.00  fd_pseudo:                              0
% 3.63/1.00  fd_cond:                                0
% 3.63/1.00  fd_pseudo_cond:                         7
% 3.63/1.00  ac_symbols:                             0
% 3.63/1.00  
% 3.63/1.00  ------ Propositional Solver
% 3.63/1.00  
% 3.63/1.00  prop_solver_calls:                      29
% 3.63/1.00  prop_fast_solver_calls:                 1067
% 3.63/1.00  smt_solver_calls:                       0
% 3.63/1.00  smt_fast_solver_calls:                  0
% 3.63/1.00  prop_num_of_clauses:                    2278
% 3.63/1.00  prop_preprocess_simplified:             9426
% 3.63/1.00  prop_fo_subsumed:                       9
% 3.63/1.00  prop_solver_time:                       0.
% 3.63/1.00  smt_solver_time:                        0.
% 3.63/1.00  smt_fast_solver_time:                   0.
% 3.63/1.00  prop_fast_solver_time:                  0.
% 3.63/1.00  prop_unsat_core_time:                   0.
% 3.63/1.00  
% 3.63/1.00  ------ QBF
% 3.63/1.00  
% 3.63/1.00  qbf_q_res:                              0
% 3.63/1.00  qbf_num_tautologies:                    0
% 3.63/1.00  qbf_prep_cycles:                        0
% 3.63/1.00  
% 3.63/1.00  ------ BMC1
% 3.63/1.00  
% 3.63/1.00  bmc1_current_bound:                     -1
% 3.63/1.00  bmc1_last_solved_bound:                 -1
% 3.63/1.00  bmc1_unsat_core_size:                   -1
% 3.63/1.00  bmc1_unsat_core_parents_size:           -1
% 3.63/1.00  bmc1_merge_next_fun:                    0
% 3.63/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.63/1.00  
% 3.63/1.00  ------ Instantiation
% 3.63/1.00  
% 3.63/1.00  inst_num_of_clauses:                    636
% 3.63/1.00  inst_num_in_passive:                    453
% 3.63/1.00  inst_num_in_active:                     124
% 3.63/1.00  inst_num_in_unprocessed:                59
% 3.63/1.00  inst_num_of_loops:                      140
% 3.63/1.00  inst_num_of_learning_restarts:          0
% 3.63/1.00  inst_num_moves_active_passive:          14
% 3.63/1.00  inst_lit_activity:                      0
% 3.63/1.00  inst_lit_activity_moves:                0
% 3.63/1.00  inst_num_tautologies:                   0
% 3.63/1.00  inst_num_prop_implied:                  0
% 3.63/1.00  inst_num_existing_simplified:           0
% 3.63/1.00  inst_num_eq_res_simplified:             0
% 3.63/1.00  inst_num_child_elim:                    0
% 3.63/1.00  inst_num_of_dismatching_blockings:      231
% 3.63/1.00  inst_num_of_non_proper_insts:           269
% 3.63/1.00  inst_num_of_duplicates:                 0
% 3.63/1.00  inst_inst_num_from_inst_to_res:         0
% 3.63/1.00  inst_dismatching_checking_time:         0.
% 3.63/1.00  
% 3.63/1.00  ------ Resolution
% 3.63/1.00  
% 3.63/1.00  res_num_of_clauses:                     0
% 3.63/1.00  res_num_in_passive:                     0
% 3.63/1.00  res_num_in_active:                      0
% 3.63/1.00  res_num_of_loops:                       142
% 3.63/1.00  res_forward_subset_subsumed:            33
% 3.63/1.00  res_backward_subset_subsumed:           2
% 3.63/1.00  res_forward_subsumed:                   0
% 3.63/1.00  res_backward_subsumed:                  0
% 3.63/1.00  res_forward_subsumption_resolution:     0
% 3.63/1.00  res_backward_subsumption_resolution:    0
% 3.63/1.00  res_clause_to_clause_subsumption:       854
% 3.63/1.00  res_orphan_elimination:                 0
% 3.63/1.00  res_tautology_del:                      21
% 3.63/1.00  res_num_eq_res_simplified:              0
% 3.63/1.00  res_num_sel_changes:                    0
% 3.63/1.00  res_moves_from_active_to_pass:          0
% 3.63/1.00  
% 3.63/1.00  ------ Superposition
% 3.63/1.00  
% 3.63/1.00  sup_time_total:                         0.
% 3.63/1.00  sup_time_generating:                    0.
% 3.63/1.00  sup_time_sim_full:                      0.
% 3.63/1.00  sup_time_sim_immed:                     0.
% 3.63/1.00  
% 3.63/1.00  sup_num_of_clauses:                     53
% 3.63/1.00  sup_num_in_active:                      23
% 3.63/1.00  sup_num_in_passive:                     30
% 3.63/1.00  sup_num_of_loops:                       27
% 3.63/1.00  sup_fw_superposition:                   20
% 3.63/1.00  sup_bw_superposition:                   8
% 3.63/1.00  sup_immediate_simplified:               1
% 3.63/1.00  sup_given_eliminated:                   0
% 3.63/1.00  comparisons_done:                       0
% 3.63/1.00  comparisons_avoided:                    0
% 3.63/1.00  
% 3.63/1.00  ------ Simplifications
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  sim_fw_subset_subsumed:                 0
% 3.63/1.00  sim_bw_subset_subsumed:                 1
% 3.63/1.00  sim_fw_subsumed:                        2
% 3.63/1.00  sim_bw_subsumed:                        0
% 3.63/1.00  sim_fw_subsumption_res:                 0
% 3.63/1.00  sim_bw_subsumption_res:                 0
% 3.63/1.00  sim_tautology_del:                      0
% 3.63/1.00  sim_eq_tautology_del:                   1
% 3.63/1.00  sim_eq_res_simp:                        0
% 3.63/1.00  sim_fw_demodulated:                     0
% 3.63/1.00  sim_bw_demodulated:                     4
% 3.63/1.00  sim_light_normalised:                   0
% 3.63/1.00  sim_joinable_taut:                      0
% 3.63/1.00  sim_joinable_simp:                      0
% 3.63/1.00  sim_ac_normalised:                      0
% 3.63/1.00  sim_smt_subsumption:                    0
% 3.63/1.00  
%------------------------------------------------------------------------------
