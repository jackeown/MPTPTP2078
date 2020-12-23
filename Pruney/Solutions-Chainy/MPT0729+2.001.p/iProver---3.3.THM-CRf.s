%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:21 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 510 expanded)
%              Number of clauses        :   47 (  64 expanded)
%              Number of leaves         :   18 ( 151 expanded)
%              Depth                    :   14
%              Number of atoms          :  255 ( 873 expanded)
%              Number of equality atoms :  143 ( 614 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f76,f77])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f75,f89])).

fof(f92,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f74,f90])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f82,f92])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f118,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f26])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f22,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f21,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f91,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f80,f90])).

fof(f93,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f84,f91,f92])).

fof(f112,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f85,f93])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = k1_ordinal1(X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_ordinal1(X0) = k1_ordinal1(X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f24])).

fof(f33,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_ordinal1(X0) = k1_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f47,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_ordinal1(X0) = k1_ordinal1(X1) )
   => ( sK2 != sK3
      & k1_ordinal1(sK2) = k1_ordinal1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( sK2 != sK3
    & k1_ordinal1(sK2) = k1_ordinal1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f47])).

fof(f87,plain,(
    k1_ordinal1(sK2) = k1_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f113,plain,(
    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f87,f93,f93])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f91])).

fof(f88,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f106,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f70,f92])).

fof(f121,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f106])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f71,f92])).

fof(f119,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f105])).

fof(f120,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f119])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_26,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1252,plain,
    ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1263,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_30,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1249,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2565,plain,
    ( r2_hidden(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_1249])).

cnf(c_5133,plain,
    ( k4_xboole_0(X0,k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1252,c_2565])).

cnf(c_18,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1259,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19616,plain,
    ( r1_xboole_0(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5133,c_1259])).

cnf(c_29,plain,
    ( r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1250,plain,
    ( r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_32,negated_conjecture,
    ( k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r2_hidden(X2,X0)
    | r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1265,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) = iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13694,plain,
    ( r1_xboole_0(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_32,c_1265])).

cnf(c_14884,plain,
    ( r1_xboole_0(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1250,c_13694])).

cnf(c_31,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1459,plain,
    ( ~ r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1460,plain,
    ( sK2 = sK3
    | r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1459])).

cnf(c_1728,plain,
    ( r2_hidden(sK3,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_32,c_1250])).

cnf(c_13692,plain,
    ( r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1728,c_1265])).

cnf(c_34,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r2_hidden(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_44,plain,
    ( r2_hidden(sK2,sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_53,plain,
    ( ~ r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_56,plain,
    ( r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_79,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_682,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1457,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_682])).

cnf(c_1458,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1457])).

cnf(c_1583,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(X0,X0,X0,X0,X0))
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1584,plain,
    ( sK3 = X0
    | r2_hidden(sK3,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1583])).

cnf(c_1586,plain,
    ( sK3 = sK2
    | r2_hidden(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1584])).

cnf(c_2308,plain,
    ( ~ r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(X0,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))
    | r2_hidden(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3657,plain,
    ( ~ r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK3,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))
    | r2_hidden(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_2308])).

cnf(c_3659,plain,
    ( r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(sK3,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3657])).

cnf(c_6470,plain,
    ( r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | k4_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_6471,plain,
    ( k4_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != sK2
    | r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6470])).

cnf(c_16914,plain,
    ( r2_hidden(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13692,c_31,c_34,c_44,c_53,c_56,c_79,c_1458,c_1586,c_1728,c_3659,c_6471])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1273,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_16919,plain,
    ( r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_16914,c_1273])).

cnf(c_16927,plain,
    ( r1_xboole_0(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14884,c_31,c_1460,c_16919])).

cnf(c_20085,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_19616,c_16927])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:52:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.71/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.71/1.51  
% 7.71/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.71/1.51  
% 7.71/1.51  ------  iProver source info
% 7.71/1.51  
% 7.71/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.71/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.71/1.51  git: non_committed_changes: false
% 7.71/1.51  git: last_make_outside_of_git: false
% 7.71/1.51  
% 7.71/1.51  ------ 
% 7.71/1.51  
% 7.71/1.51  ------ Input Options
% 7.71/1.51  
% 7.71/1.51  --out_options                           all
% 7.71/1.51  --tptp_safe_out                         true
% 7.71/1.51  --problem_path                          ""
% 7.71/1.51  --include_path                          ""
% 7.71/1.51  --clausifier                            res/vclausify_rel
% 7.71/1.51  --clausifier_options                    --mode clausify
% 7.71/1.51  --stdin                                 false
% 7.71/1.51  --stats_out                             all
% 7.71/1.51  
% 7.71/1.51  ------ General Options
% 7.71/1.51  
% 7.71/1.51  --fof                                   false
% 7.71/1.51  --time_out_real                         305.
% 7.71/1.51  --time_out_virtual                      -1.
% 7.71/1.51  --symbol_type_check                     false
% 7.71/1.51  --clausify_out                          false
% 7.71/1.51  --sig_cnt_out                           false
% 7.71/1.51  --trig_cnt_out                          false
% 7.71/1.51  --trig_cnt_out_tolerance                1.
% 7.71/1.51  --trig_cnt_out_sk_spl                   false
% 7.71/1.51  --abstr_cl_out                          false
% 7.71/1.51  
% 7.71/1.51  ------ Global Options
% 7.71/1.51  
% 7.71/1.51  --schedule                              default
% 7.71/1.51  --add_important_lit                     false
% 7.71/1.51  --prop_solver_per_cl                    1000
% 7.71/1.51  --min_unsat_core                        false
% 7.71/1.51  --soft_assumptions                      false
% 7.71/1.51  --soft_lemma_size                       3
% 7.71/1.51  --prop_impl_unit_size                   0
% 7.71/1.51  --prop_impl_unit                        []
% 7.71/1.51  --share_sel_clauses                     true
% 7.71/1.51  --reset_solvers                         false
% 7.71/1.51  --bc_imp_inh                            [conj_cone]
% 7.71/1.51  --conj_cone_tolerance                   3.
% 7.71/1.51  --extra_neg_conj                        none
% 7.71/1.51  --large_theory_mode                     true
% 7.71/1.51  --prolific_symb_bound                   200
% 7.71/1.51  --lt_threshold                          2000
% 7.71/1.51  --clause_weak_htbl                      true
% 7.71/1.51  --gc_record_bc_elim                     false
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing Options
% 7.71/1.51  
% 7.71/1.51  --preprocessing_flag                    true
% 7.71/1.51  --time_out_prep_mult                    0.1
% 7.71/1.51  --splitting_mode                        input
% 7.71/1.51  --splitting_grd                         true
% 7.71/1.51  --splitting_cvd                         false
% 7.71/1.51  --splitting_cvd_svl                     false
% 7.71/1.51  --splitting_nvd                         32
% 7.71/1.51  --sub_typing                            true
% 7.71/1.51  --prep_gs_sim                           true
% 7.71/1.51  --prep_unflatten                        true
% 7.71/1.51  --prep_res_sim                          true
% 7.71/1.51  --prep_upred                            true
% 7.71/1.51  --prep_sem_filter                       exhaustive
% 7.71/1.51  --prep_sem_filter_out                   false
% 7.71/1.51  --pred_elim                             true
% 7.71/1.51  --res_sim_input                         true
% 7.71/1.51  --eq_ax_congr_red                       true
% 7.71/1.51  --pure_diseq_elim                       true
% 7.71/1.51  --brand_transform                       false
% 7.71/1.51  --non_eq_to_eq                          false
% 7.71/1.51  --prep_def_merge                        true
% 7.71/1.51  --prep_def_merge_prop_impl              false
% 7.71/1.51  --prep_def_merge_mbd                    true
% 7.71/1.51  --prep_def_merge_tr_red                 false
% 7.71/1.51  --prep_def_merge_tr_cl                  false
% 7.71/1.51  --smt_preprocessing                     true
% 7.71/1.51  --smt_ac_axioms                         fast
% 7.71/1.51  --preprocessed_out                      false
% 7.71/1.51  --preprocessed_stats                    false
% 7.71/1.51  
% 7.71/1.51  ------ Abstraction refinement Options
% 7.71/1.51  
% 7.71/1.51  --abstr_ref                             []
% 7.71/1.51  --abstr_ref_prep                        false
% 7.71/1.51  --abstr_ref_until_sat                   false
% 7.71/1.51  --abstr_ref_sig_restrict                funpre
% 7.71/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.71/1.51  --abstr_ref_under                       []
% 7.71/1.51  
% 7.71/1.51  ------ SAT Options
% 7.71/1.51  
% 7.71/1.51  --sat_mode                              false
% 7.71/1.51  --sat_fm_restart_options                ""
% 7.71/1.51  --sat_gr_def                            false
% 7.71/1.51  --sat_epr_types                         true
% 7.71/1.51  --sat_non_cyclic_types                  false
% 7.71/1.51  --sat_finite_models                     false
% 7.71/1.51  --sat_fm_lemmas                         false
% 7.71/1.51  --sat_fm_prep                           false
% 7.71/1.51  --sat_fm_uc_incr                        true
% 7.71/1.51  --sat_out_model                         small
% 7.71/1.51  --sat_out_clauses                       false
% 7.71/1.51  
% 7.71/1.51  ------ QBF Options
% 7.71/1.51  
% 7.71/1.51  --qbf_mode                              false
% 7.71/1.51  --qbf_elim_univ                         false
% 7.71/1.51  --qbf_dom_inst                          none
% 7.71/1.51  --qbf_dom_pre_inst                      false
% 7.71/1.51  --qbf_sk_in                             false
% 7.71/1.51  --qbf_pred_elim                         true
% 7.71/1.51  --qbf_split                             512
% 7.71/1.51  
% 7.71/1.51  ------ BMC1 Options
% 7.71/1.51  
% 7.71/1.51  --bmc1_incremental                      false
% 7.71/1.51  --bmc1_axioms                           reachable_all
% 7.71/1.51  --bmc1_min_bound                        0
% 7.71/1.51  --bmc1_max_bound                        -1
% 7.71/1.51  --bmc1_max_bound_default                -1
% 7.71/1.51  --bmc1_symbol_reachability              true
% 7.71/1.51  --bmc1_property_lemmas                  false
% 7.71/1.51  --bmc1_k_induction                      false
% 7.71/1.51  --bmc1_non_equiv_states                 false
% 7.71/1.51  --bmc1_deadlock                         false
% 7.71/1.51  --bmc1_ucm                              false
% 7.71/1.51  --bmc1_add_unsat_core                   none
% 7.71/1.51  --bmc1_unsat_core_children              false
% 7.71/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.71/1.51  --bmc1_out_stat                         full
% 7.71/1.51  --bmc1_ground_init                      false
% 7.71/1.51  --bmc1_pre_inst_next_state              false
% 7.71/1.51  --bmc1_pre_inst_state                   false
% 7.71/1.51  --bmc1_pre_inst_reach_state             false
% 7.71/1.51  --bmc1_out_unsat_core                   false
% 7.71/1.51  --bmc1_aig_witness_out                  false
% 7.71/1.51  --bmc1_verbose                          false
% 7.71/1.51  --bmc1_dump_clauses_tptp                false
% 7.71/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.71/1.51  --bmc1_dump_file                        -
% 7.71/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.71/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.71/1.51  --bmc1_ucm_extend_mode                  1
% 7.71/1.51  --bmc1_ucm_init_mode                    2
% 7.71/1.51  --bmc1_ucm_cone_mode                    none
% 7.71/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.71/1.51  --bmc1_ucm_relax_model                  4
% 7.71/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.71/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.71/1.51  --bmc1_ucm_layered_model                none
% 7.71/1.51  --bmc1_ucm_max_lemma_size               10
% 7.71/1.51  
% 7.71/1.51  ------ AIG Options
% 7.71/1.51  
% 7.71/1.51  --aig_mode                              false
% 7.71/1.51  
% 7.71/1.51  ------ Instantiation Options
% 7.71/1.51  
% 7.71/1.51  --instantiation_flag                    true
% 7.71/1.51  --inst_sos_flag                         false
% 7.71/1.51  --inst_sos_phase                        true
% 7.71/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.71/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.71/1.51  --inst_lit_sel_side                     num_symb
% 7.71/1.51  --inst_solver_per_active                1400
% 7.71/1.51  --inst_solver_calls_frac                1.
% 7.71/1.51  --inst_passive_queue_type               priority_queues
% 7.71/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.71/1.51  --inst_passive_queues_freq              [25;2]
% 7.71/1.51  --inst_dismatching                      true
% 7.71/1.51  --inst_eager_unprocessed_to_passive     true
% 7.71/1.51  --inst_prop_sim_given                   true
% 7.71/1.51  --inst_prop_sim_new                     false
% 7.71/1.51  --inst_subs_new                         false
% 7.71/1.51  --inst_eq_res_simp                      false
% 7.71/1.51  --inst_subs_given                       false
% 7.71/1.51  --inst_orphan_elimination               true
% 7.71/1.51  --inst_learning_loop_flag               true
% 7.71/1.51  --inst_learning_start                   3000
% 7.71/1.51  --inst_learning_factor                  2
% 7.71/1.51  --inst_start_prop_sim_after_learn       3
% 7.71/1.51  --inst_sel_renew                        solver
% 7.71/1.51  --inst_lit_activity_flag                true
% 7.71/1.51  --inst_restr_to_given                   false
% 7.71/1.51  --inst_activity_threshold               500
% 7.71/1.51  --inst_out_proof                        true
% 7.71/1.51  
% 7.71/1.51  ------ Resolution Options
% 7.71/1.51  
% 7.71/1.51  --resolution_flag                       true
% 7.71/1.51  --res_lit_sel                           adaptive
% 7.71/1.51  --res_lit_sel_side                      none
% 7.71/1.51  --res_ordering                          kbo
% 7.71/1.51  --res_to_prop_solver                    active
% 7.71/1.51  --res_prop_simpl_new                    false
% 7.71/1.51  --res_prop_simpl_given                  true
% 7.71/1.51  --res_passive_queue_type                priority_queues
% 7.71/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.71/1.51  --res_passive_queues_freq               [15;5]
% 7.71/1.51  --res_forward_subs                      full
% 7.71/1.51  --res_backward_subs                     full
% 7.71/1.51  --res_forward_subs_resolution           true
% 7.71/1.51  --res_backward_subs_resolution          true
% 7.71/1.51  --res_orphan_elimination                true
% 7.71/1.51  --res_time_limit                        2.
% 7.71/1.51  --res_out_proof                         true
% 7.71/1.51  
% 7.71/1.51  ------ Superposition Options
% 7.71/1.51  
% 7.71/1.51  --superposition_flag                    true
% 7.71/1.51  --sup_passive_queue_type                priority_queues
% 7.71/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.71/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.71/1.51  --demod_completeness_check              fast
% 7.71/1.51  --demod_use_ground                      true
% 7.71/1.51  --sup_to_prop_solver                    passive
% 7.71/1.51  --sup_prop_simpl_new                    true
% 7.71/1.51  --sup_prop_simpl_given                  true
% 7.71/1.51  --sup_fun_splitting                     false
% 7.71/1.51  --sup_smt_interval                      50000
% 7.71/1.51  
% 7.71/1.51  ------ Superposition Simplification Setup
% 7.71/1.51  
% 7.71/1.51  --sup_indices_passive                   []
% 7.71/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.71/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.51  --sup_full_bw                           [BwDemod]
% 7.71/1.51  --sup_immed_triv                        [TrivRules]
% 7.71/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.51  --sup_immed_bw_main                     []
% 7.71/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.71/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.71/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.71/1.51  
% 7.71/1.51  ------ Combination Options
% 7.71/1.51  
% 7.71/1.51  --comb_res_mult                         3
% 7.71/1.51  --comb_sup_mult                         2
% 7.71/1.51  --comb_inst_mult                        10
% 7.71/1.51  
% 7.71/1.51  ------ Debug Options
% 7.71/1.51  
% 7.71/1.51  --dbg_backtrace                         false
% 7.71/1.51  --dbg_dump_prop_clauses                 false
% 7.71/1.51  --dbg_dump_prop_clauses_file            -
% 7.71/1.51  --dbg_out_stat                          false
% 7.71/1.51  ------ Parsing...
% 7.71/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.71/1.51  ------ Proving...
% 7.71/1.51  ------ Problem Properties 
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  clauses                                 30
% 7.71/1.51  conjectures                             2
% 7.71/1.51  EPR                                     5
% 7.71/1.51  Horn                                    23
% 7.71/1.51  unary                                   9
% 7.71/1.51  binary                                  12
% 7.71/1.51  lits                                    63
% 7.71/1.51  lits eq                                 18
% 7.71/1.51  fd_pure                                 0
% 7.71/1.51  fd_pseudo                               0
% 7.71/1.51  fd_cond                                 0
% 7.71/1.51  fd_pseudo_cond                          6
% 7.71/1.51  AC symbols                              0
% 7.71/1.51  
% 7.71/1.51  ------ Schedule dynamic 5 is on 
% 7.71/1.51  
% 7.71/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  ------ 
% 7.71/1.51  Current options:
% 7.71/1.51  ------ 
% 7.71/1.51  
% 7.71/1.51  ------ Input Options
% 7.71/1.51  
% 7.71/1.51  --out_options                           all
% 7.71/1.51  --tptp_safe_out                         true
% 7.71/1.51  --problem_path                          ""
% 7.71/1.51  --include_path                          ""
% 7.71/1.51  --clausifier                            res/vclausify_rel
% 7.71/1.51  --clausifier_options                    --mode clausify
% 7.71/1.51  --stdin                                 false
% 7.71/1.51  --stats_out                             all
% 7.71/1.51  
% 7.71/1.51  ------ General Options
% 7.71/1.51  
% 7.71/1.51  --fof                                   false
% 7.71/1.51  --time_out_real                         305.
% 7.71/1.51  --time_out_virtual                      -1.
% 7.71/1.51  --symbol_type_check                     false
% 7.71/1.51  --clausify_out                          false
% 7.71/1.51  --sig_cnt_out                           false
% 7.71/1.51  --trig_cnt_out                          false
% 7.71/1.51  --trig_cnt_out_tolerance                1.
% 7.71/1.51  --trig_cnt_out_sk_spl                   false
% 7.71/1.51  --abstr_cl_out                          false
% 7.71/1.51  
% 7.71/1.51  ------ Global Options
% 7.71/1.51  
% 7.71/1.51  --schedule                              default
% 7.71/1.51  --add_important_lit                     false
% 7.71/1.51  --prop_solver_per_cl                    1000
% 7.71/1.51  --min_unsat_core                        false
% 7.71/1.51  --soft_assumptions                      false
% 7.71/1.51  --soft_lemma_size                       3
% 7.71/1.51  --prop_impl_unit_size                   0
% 7.71/1.51  --prop_impl_unit                        []
% 7.71/1.51  --share_sel_clauses                     true
% 7.71/1.51  --reset_solvers                         false
% 7.71/1.51  --bc_imp_inh                            [conj_cone]
% 7.71/1.51  --conj_cone_tolerance                   3.
% 7.71/1.51  --extra_neg_conj                        none
% 7.71/1.51  --large_theory_mode                     true
% 7.71/1.51  --prolific_symb_bound                   200
% 7.71/1.51  --lt_threshold                          2000
% 7.71/1.51  --clause_weak_htbl                      true
% 7.71/1.51  --gc_record_bc_elim                     false
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing Options
% 7.71/1.51  
% 7.71/1.51  --preprocessing_flag                    true
% 7.71/1.51  --time_out_prep_mult                    0.1
% 7.71/1.51  --splitting_mode                        input
% 7.71/1.51  --splitting_grd                         true
% 7.71/1.51  --splitting_cvd                         false
% 7.71/1.51  --splitting_cvd_svl                     false
% 7.71/1.51  --splitting_nvd                         32
% 7.71/1.51  --sub_typing                            true
% 7.71/1.51  --prep_gs_sim                           true
% 7.71/1.51  --prep_unflatten                        true
% 7.71/1.51  --prep_res_sim                          true
% 7.71/1.51  --prep_upred                            true
% 7.71/1.51  --prep_sem_filter                       exhaustive
% 7.71/1.51  --prep_sem_filter_out                   false
% 7.71/1.51  --pred_elim                             true
% 7.71/1.51  --res_sim_input                         true
% 7.71/1.51  --eq_ax_congr_red                       true
% 7.71/1.51  --pure_diseq_elim                       true
% 7.71/1.51  --brand_transform                       false
% 7.71/1.51  --non_eq_to_eq                          false
% 7.71/1.51  --prep_def_merge                        true
% 7.71/1.51  --prep_def_merge_prop_impl              false
% 7.71/1.51  --prep_def_merge_mbd                    true
% 7.71/1.51  --prep_def_merge_tr_red                 false
% 7.71/1.51  --prep_def_merge_tr_cl                  false
% 7.71/1.51  --smt_preprocessing                     true
% 7.71/1.51  --smt_ac_axioms                         fast
% 7.71/1.51  --preprocessed_out                      false
% 7.71/1.51  --preprocessed_stats                    false
% 7.71/1.51  
% 7.71/1.51  ------ Abstraction refinement Options
% 7.71/1.51  
% 7.71/1.51  --abstr_ref                             []
% 7.71/1.51  --abstr_ref_prep                        false
% 7.71/1.51  --abstr_ref_until_sat                   false
% 7.71/1.51  --abstr_ref_sig_restrict                funpre
% 7.71/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.71/1.51  --abstr_ref_under                       []
% 7.71/1.51  
% 7.71/1.51  ------ SAT Options
% 7.71/1.51  
% 7.71/1.51  --sat_mode                              false
% 7.71/1.51  --sat_fm_restart_options                ""
% 7.71/1.51  --sat_gr_def                            false
% 7.71/1.51  --sat_epr_types                         true
% 7.71/1.51  --sat_non_cyclic_types                  false
% 7.71/1.51  --sat_finite_models                     false
% 7.71/1.51  --sat_fm_lemmas                         false
% 7.71/1.51  --sat_fm_prep                           false
% 7.71/1.51  --sat_fm_uc_incr                        true
% 7.71/1.51  --sat_out_model                         small
% 7.71/1.51  --sat_out_clauses                       false
% 7.71/1.51  
% 7.71/1.51  ------ QBF Options
% 7.71/1.51  
% 7.71/1.51  --qbf_mode                              false
% 7.71/1.51  --qbf_elim_univ                         false
% 7.71/1.51  --qbf_dom_inst                          none
% 7.71/1.51  --qbf_dom_pre_inst                      false
% 7.71/1.51  --qbf_sk_in                             false
% 7.71/1.51  --qbf_pred_elim                         true
% 7.71/1.51  --qbf_split                             512
% 7.71/1.51  
% 7.71/1.51  ------ BMC1 Options
% 7.71/1.51  
% 7.71/1.51  --bmc1_incremental                      false
% 7.71/1.51  --bmc1_axioms                           reachable_all
% 7.71/1.51  --bmc1_min_bound                        0
% 7.71/1.51  --bmc1_max_bound                        -1
% 7.71/1.51  --bmc1_max_bound_default                -1
% 7.71/1.51  --bmc1_symbol_reachability              true
% 7.71/1.51  --bmc1_property_lemmas                  false
% 7.71/1.51  --bmc1_k_induction                      false
% 7.71/1.51  --bmc1_non_equiv_states                 false
% 7.71/1.51  --bmc1_deadlock                         false
% 7.71/1.51  --bmc1_ucm                              false
% 7.71/1.51  --bmc1_add_unsat_core                   none
% 7.71/1.51  --bmc1_unsat_core_children              false
% 7.71/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.71/1.51  --bmc1_out_stat                         full
% 7.71/1.51  --bmc1_ground_init                      false
% 7.71/1.51  --bmc1_pre_inst_next_state              false
% 7.71/1.51  --bmc1_pre_inst_state                   false
% 7.71/1.51  --bmc1_pre_inst_reach_state             false
% 7.71/1.51  --bmc1_out_unsat_core                   false
% 7.71/1.51  --bmc1_aig_witness_out                  false
% 7.71/1.51  --bmc1_verbose                          false
% 7.71/1.51  --bmc1_dump_clauses_tptp                false
% 7.71/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.71/1.51  --bmc1_dump_file                        -
% 7.71/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.71/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.71/1.51  --bmc1_ucm_extend_mode                  1
% 7.71/1.51  --bmc1_ucm_init_mode                    2
% 7.71/1.51  --bmc1_ucm_cone_mode                    none
% 7.71/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.71/1.51  --bmc1_ucm_relax_model                  4
% 7.71/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.71/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.71/1.51  --bmc1_ucm_layered_model                none
% 7.71/1.51  --bmc1_ucm_max_lemma_size               10
% 7.71/1.51  
% 7.71/1.51  ------ AIG Options
% 7.71/1.51  
% 7.71/1.51  --aig_mode                              false
% 7.71/1.51  
% 7.71/1.51  ------ Instantiation Options
% 7.71/1.51  
% 7.71/1.51  --instantiation_flag                    true
% 7.71/1.51  --inst_sos_flag                         false
% 7.71/1.51  --inst_sos_phase                        true
% 7.71/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.71/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.71/1.51  --inst_lit_sel_side                     none
% 7.71/1.51  --inst_solver_per_active                1400
% 7.71/1.51  --inst_solver_calls_frac                1.
% 7.71/1.51  --inst_passive_queue_type               priority_queues
% 7.71/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.71/1.51  --inst_passive_queues_freq              [25;2]
% 7.71/1.51  --inst_dismatching                      true
% 7.71/1.51  --inst_eager_unprocessed_to_passive     true
% 7.71/1.51  --inst_prop_sim_given                   true
% 7.71/1.51  --inst_prop_sim_new                     false
% 7.71/1.51  --inst_subs_new                         false
% 7.71/1.51  --inst_eq_res_simp                      false
% 7.71/1.51  --inst_subs_given                       false
% 7.71/1.51  --inst_orphan_elimination               true
% 7.71/1.51  --inst_learning_loop_flag               true
% 7.71/1.51  --inst_learning_start                   3000
% 7.71/1.51  --inst_learning_factor                  2
% 7.71/1.51  --inst_start_prop_sim_after_learn       3
% 7.71/1.51  --inst_sel_renew                        solver
% 7.71/1.51  --inst_lit_activity_flag                true
% 7.71/1.51  --inst_restr_to_given                   false
% 7.71/1.51  --inst_activity_threshold               500
% 7.71/1.51  --inst_out_proof                        true
% 7.71/1.51  
% 7.71/1.51  ------ Resolution Options
% 7.71/1.51  
% 7.71/1.51  --resolution_flag                       false
% 7.71/1.51  --res_lit_sel                           adaptive
% 7.71/1.51  --res_lit_sel_side                      none
% 7.71/1.51  --res_ordering                          kbo
% 7.71/1.51  --res_to_prop_solver                    active
% 7.71/1.51  --res_prop_simpl_new                    false
% 7.71/1.51  --res_prop_simpl_given                  true
% 7.71/1.51  --res_passive_queue_type                priority_queues
% 7.71/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.71/1.51  --res_passive_queues_freq               [15;5]
% 7.71/1.51  --res_forward_subs                      full
% 7.71/1.51  --res_backward_subs                     full
% 7.71/1.51  --res_forward_subs_resolution           true
% 7.71/1.51  --res_backward_subs_resolution          true
% 7.71/1.51  --res_orphan_elimination                true
% 7.71/1.51  --res_time_limit                        2.
% 7.71/1.51  --res_out_proof                         true
% 7.71/1.51  
% 7.71/1.51  ------ Superposition Options
% 7.71/1.51  
% 7.71/1.51  --superposition_flag                    true
% 7.71/1.51  --sup_passive_queue_type                priority_queues
% 7.71/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.71/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.71/1.51  --demod_completeness_check              fast
% 7.71/1.51  --demod_use_ground                      true
% 7.71/1.51  --sup_to_prop_solver                    passive
% 7.71/1.51  --sup_prop_simpl_new                    true
% 7.71/1.51  --sup_prop_simpl_given                  true
% 7.71/1.51  --sup_fun_splitting                     false
% 7.71/1.51  --sup_smt_interval                      50000
% 7.71/1.51  
% 7.71/1.51  ------ Superposition Simplification Setup
% 7.71/1.51  
% 7.71/1.51  --sup_indices_passive                   []
% 7.71/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.71/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.51  --sup_full_bw                           [BwDemod]
% 7.71/1.51  --sup_immed_triv                        [TrivRules]
% 7.71/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.51  --sup_immed_bw_main                     []
% 7.71/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.71/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.71/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.71/1.51  
% 7.71/1.51  ------ Combination Options
% 7.71/1.51  
% 7.71/1.51  --comb_res_mult                         3
% 7.71/1.51  --comb_sup_mult                         2
% 7.71/1.51  --comb_inst_mult                        10
% 7.71/1.51  
% 7.71/1.51  ------ Debug Options
% 7.71/1.51  
% 7.71/1.51  --dbg_backtrace                         false
% 7.71/1.51  --dbg_dump_prop_clauses                 false
% 7.71/1.51  --dbg_dump_prop_clauses_file            -
% 7.71/1.51  --dbg_out_stat                          false
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  ------ Proving...
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  % SZS status Theorem for theBenchmark.p
% 7.71/1.51  
% 7.71/1.51   Resolution empty clause
% 7.71/1.51  
% 7.71/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.71/1.51  
% 7.71/1.51  fof(f19,axiom,(
% 7.71/1.51    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 7.71/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f46,plain,(
% 7.71/1.51    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 7.71/1.51    inference(nnf_transformation,[],[f19])).
% 7.71/1.51  
% 7.71/1.51  fof(f82,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f46])).
% 7.71/1.51  
% 7.71/1.51  fof(f13,axiom,(
% 7.71/1.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.71/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f74,plain,(
% 7.71/1.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f13])).
% 7.71/1.51  
% 7.71/1.51  fof(f14,axiom,(
% 7.71/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.71/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f75,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f14])).
% 7.71/1.51  
% 7.71/1.51  fof(f15,axiom,(
% 7.71/1.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.71/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f76,plain,(
% 7.71/1.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f15])).
% 7.71/1.51  
% 7.71/1.51  fof(f16,axiom,(
% 7.71/1.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.71/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f77,plain,(
% 7.71/1.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f16])).
% 7.71/1.51  
% 7.71/1.51  fof(f89,plain,(
% 7.71/1.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.71/1.51    inference(definition_unfolding,[],[f76,f77])).
% 7.71/1.51  
% 7.71/1.51  fof(f90,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.71/1.51    inference(definition_unfolding,[],[f75,f89])).
% 7.71/1.51  
% 7.71/1.51  fof(f92,plain,(
% 7.71/1.51    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 7.71/1.51    inference(definition_unfolding,[],[f74,f90])).
% 7.71/1.51  
% 7.71/1.51  fof(f109,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 7.71/1.51    inference(definition_unfolding,[],[f82,f92])).
% 7.71/1.51  
% 7.71/1.51  fof(f4,axiom,(
% 7.71/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.71/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f39,plain,(
% 7.71/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.71/1.51    inference(nnf_transformation,[],[f4])).
% 7.71/1.51  
% 7.71/1.51  fof(f40,plain,(
% 7.71/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.71/1.51    inference(flattening,[],[f39])).
% 7.71/1.51  
% 7.71/1.51  fof(f60,plain,(
% 7.71/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.71/1.51    inference(cnf_transformation,[],[f40])).
% 7.71/1.51  
% 7.71/1.51  fof(f118,plain,(
% 7.71/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.71/1.51    inference(equality_resolution,[],[f60])).
% 7.71/1.51  
% 7.71/1.51  fof(f23,axiom,(
% 7.71/1.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.71/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f32,plain,(
% 7.71/1.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.71/1.51    inference(ennf_transformation,[],[f23])).
% 7.71/1.51  
% 7.71/1.51  fof(f86,plain,(
% 7.71/1.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f32])).
% 7.71/1.51  
% 7.71/1.51  fof(f10,axiom,(
% 7.71/1.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.71/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f26,plain,(
% 7.71/1.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 7.71/1.51    inference(unused_predicate_definition_removal,[],[f10])).
% 7.71/1.51  
% 7.71/1.51  fof(f31,plain,(
% 7.71/1.51    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 7.71/1.51    inference(ennf_transformation,[],[f26])).
% 7.71/1.51  
% 7.71/1.51  fof(f68,plain,(
% 7.71/1.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 7.71/1.51    inference(cnf_transformation,[],[f31])).
% 7.71/1.51  
% 7.71/1.51  fof(f22,axiom,(
% 7.71/1.51    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 7.71/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f85,plain,(
% 7.71/1.51    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 7.71/1.51    inference(cnf_transformation,[],[f22])).
% 7.71/1.51  
% 7.71/1.51  fof(f21,axiom,(
% 7.71/1.51    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 7.71/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f84,plain,(
% 7.71/1.51    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f21])).
% 7.71/1.51  
% 7.71/1.51  fof(f18,axiom,(
% 7.71/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.71/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f80,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.71/1.51    inference(cnf_transformation,[],[f18])).
% 7.71/1.51  
% 7.71/1.51  fof(f91,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 7.71/1.51    inference(definition_unfolding,[],[f80,f90])).
% 7.71/1.51  
% 7.71/1.51  fof(f93,plain,(
% 7.71/1.51    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 7.71/1.51    inference(definition_unfolding,[],[f84,f91,f92])).
% 7.71/1.51  
% 7.71/1.51  fof(f112,plain,(
% 7.71/1.51    ( ! [X0] : (r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))))) )),
% 7.71/1.51    inference(definition_unfolding,[],[f85,f93])).
% 7.71/1.51  
% 7.71/1.51  fof(f24,conjecture,(
% 7.71/1.51    ! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 7.71/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f25,negated_conjecture,(
% 7.71/1.51    ~! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 7.71/1.51    inference(negated_conjecture,[],[f24])).
% 7.71/1.51  
% 7.71/1.51  fof(f33,plain,(
% 7.71/1.51    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1))),
% 7.71/1.51    inference(ennf_transformation,[],[f25])).
% 7.71/1.51  
% 7.71/1.51  fof(f47,plain,(
% 7.71/1.51    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1)) => (sK2 != sK3 & k1_ordinal1(sK2) = k1_ordinal1(sK3))),
% 7.71/1.51    introduced(choice_axiom,[])).
% 7.71/1.51  
% 7.71/1.51  fof(f48,plain,(
% 7.71/1.51    sK2 != sK3 & k1_ordinal1(sK2) = k1_ordinal1(sK3)),
% 7.71/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f47])).
% 7.71/1.51  
% 7.71/1.51  fof(f87,plain,(
% 7.71/1.51    k1_ordinal1(sK2) = k1_ordinal1(sK3)),
% 7.71/1.51    inference(cnf_transformation,[],[f48])).
% 7.71/1.51  
% 7.71/1.51  fof(f113,plain,(
% 7.71/1.51    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),
% 7.71/1.51    inference(definition_unfolding,[],[f87,f93,f93])).
% 7.71/1.51  
% 7.71/1.51  fof(f3,axiom,(
% 7.71/1.51    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 7.71/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f28,plain,(
% 7.71/1.51    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 7.71/1.51    inference(ennf_transformation,[],[f3])).
% 7.71/1.51  
% 7.71/1.51  fof(f56,plain,(
% 7.71/1.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f28])).
% 7.71/1.51  
% 7.71/1.51  fof(f97,plain,(
% 7.71/1.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~r2_hidden(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 7.71/1.51    inference(definition_unfolding,[],[f56,f91])).
% 7.71/1.51  
% 7.71/1.51  fof(f88,plain,(
% 7.71/1.51    sK2 != sK3),
% 7.71/1.51    inference(cnf_transformation,[],[f48])).
% 7.71/1.51  
% 7.71/1.51  fof(f12,axiom,(
% 7.71/1.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.71/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f41,plain,(
% 7.71/1.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.71/1.51    inference(nnf_transformation,[],[f12])).
% 7.71/1.51  
% 7.71/1.51  fof(f42,plain,(
% 7.71/1.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.71/1.51    inference(rectify,[],[f41])).
% 7.71/1.51  
% 7.71/1.51  fof(f43,plain,(
% 7.71/1.51    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 7.71/1.51    introduced(choice_axiom,[])).
% 7.71/1.51  
% 7.71/1.51  fof(f44,plain,(
% 7.71/1.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.71/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).
% 7.71/1.51  
% 7.71/1.51  fof(f70,plain,(
% 7.71/1.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.71/1.51    inference(cnf_transformation,[],[f44])).
% 7.71/1.51  
% 7.71/1.51  fof(f106,plain,(
% 7.71/1.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 7.71/1.51    inference(definition_unfolding,[],[f70,f92])).
% 7.71/1.51  
% 7.71/1.51  fof(f121,plain,(
% 7.71/1.51    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 7.71/1.51    inference(equality_resolution,[],[f106])).
% 7.71/1.51  
% 7.71/1.51  fof(f71,plain,(
% 7.71/1.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.71/1.51    inference(cnf_transformation,[],[f44])).
% 7.71/1.51  
% 7.71/1.51  fof(f105,plain,(
% 7.71/1.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 7.71/1.51    inference(definition_unfolding,[],[f71,f92])).
% 7.71/1.51  
% 7.71/1.51  fof(f119,plain,(
% 7.71/1.51    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 7.71/1.51    inference(equality_resolution,[],[f105])).
% 7.71/1.51  
% 7.71/1.51  fof(f120,plain,(
% 7.71/1.51    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 7.71/1.51    inference(equality_resolution,[],[f119])).
% 7.71/1.51  
% 7.71/1.51  fof(f1,axiom,(
% 7.71/1.51    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 7.71/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f27,plain,(
% 7.71/1.51    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 7.71/1.51    inference(ennf_transformation,[],[f1])).
% 7.71/1.51  
% 7.71/1.51  fof(f49,plain,(
% 7.71/1.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f27])).
% 7.71/1.51  
% 7.71/1.51  cnf(c_26,plain,
% 7.71/1.51      ( r2_hidden(X0,X1) | k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) = X1 ),
% 7.71/1.51      inference(cnf_transformation,[],[f109]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1252,plain,
% 7.71/1.51      ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0
% 7.71/1.51      | r2_hidden(X1,X0) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_13,plain,
% 7.71/1.51      ( r1_tarski(X0,X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f118]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1263,plain,
% 7.71/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_30,plain,
% 7.71/1.51      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1249,plain,
% 7.71/1.51      ( r1_tarski(X0,X1) != iProver_top | r2_hidden(X1,X0) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2565,plain,
% 7.71/1.51      ( r2_hidden(X0,X0) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1263,c_1249]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_5133,plain,
% 7.71/1.51      ( k4_xboole_0(X0,k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1252,c_2565]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_18,plain,
% 7.71/1.51      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 7.71/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1259,plain,
% 7.71/1.51      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_19616,plain,
% 7.71/1.51      ( r1_xboole_0(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_5133,c_1259]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_29,plain,
% 7.71/1.51      ( r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) ),
% 7.71/1.51      inference(cnf_transformation,[],[f112]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1250,plain,
% 7.71/1.51      ( r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_32,negated_conjecture,
% 7.71/1.51      ( k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 7.71/1.51      inference(cnf_transformation,[],[f113]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_10,plain,
% 7.71/1.51      ( ~ r1_xboole_0(X0,X1)
% 7.71/1.51      | r2_hidden(X2,X0)
% 7.71/1.51      | r2_hidden(X2,X1)
% 7.71/1.51      | ~ r2_hidden(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 7.71/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1265,plain,
% 7.71/1.51      ( r1_xboole_0(X0,X1) != iProver_top
% 7.71/1.51      | r2_hidden(X2,X0) = iProver_top
% 7.71/1.51      | r2_hidden(X2,X1) = iProver_top
% 7.71/1.51      | r2_hidden(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_13694,plain,
% 7.71/1.51      ( r1_xboole_0(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 7.71/1.51      | r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 7.71/1.51      | r2_hidden(X0,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != iProver_top
% 7.71/1.51      | r2_hidden(X0,sK3) = iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_32,c_1265]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_14884,plain,
% 7.71/1.51      ( r1_xboole_0(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 7.71/1.51      | r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 7.71/1.51      | r2_hidden(sK2,sK3) = iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1250,c_13694]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_31,negated_conjecture,
% 7.71/1.51      ( sK2 != sK3 ),
% 7.71/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_23,plain,
% 7.71/1.51      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 7.71/1.51      inference(cnf_transformation,[],[f121]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1459,plain,
% 7.71/1.51      ( ~ r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | sK2 = sK3 ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_23]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1460,plain,
% 7.71/1.51      ( sK2 = sK3
% 7.71/1.51      | r2_hidden(sK2,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_1459]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1728,plain,
% 7.71/1.51      ( r2_hidden(sK3,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_32,c_1250]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_13692,plain,
% 7.71/1.51      ( r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 7.71/1.51      | r2_hidden(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top
% 7.71/1.51      | r2_hidden(sK3,sK2) = iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1728,c_1265]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_34,plain,
% 7.71/1.51      ( ~ r1_tarski(sK2,sK2) | ~ r2_hidden(sK2,sK2) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_30]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_44,plain,
% 7.71/1.51      ( r2_hidden(sK2,sK2)
% 7.71/1.51      | k4_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = sK2 ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_26]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_53,plain,
% 7.71/1.51      ( ~ r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | sK2 = sK2 ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_23]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_22,plain,
% 7.71/1.51      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 7.71/1.51      inference(cnf_transformation,[],[f120]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_56,plain,
% 7.71/1.51      ( r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_22]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_79,plain,
% 7.71/1.51      ( r1_tarski(sK2,sK2) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_13]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_682,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1457,plain,
% 7.71/1.51      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_682]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1458,plain,
% 7.71/1.51      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_1457]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1583,plain,
% 7.71/1.51      ( ~ r2_hidden(sK3,k3_enumset1(X0,X0,X0,X0,X0)) | sK3 = X0 ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_23]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1584,plain,
% 7.71/1.51      ( sK3 = X0 | r2_hidden(sK3,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_1583]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1586,plain,
% 7.71/1.51      ( sK3 = sK2
% 7.71/1.51      | r2_hidden(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_1584]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2308,plain,
% 7.71/1.51      ( ~ r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 7.71/1.51      | r2_hidden(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 7.71/1.51      | ~ r2_hidden(X0,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))
% 7.71/1.51      | r2_hidden(X0,sK2) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_10]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3657,plain,
% 7.71/1.51      ( ~ r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 7.71/1.51      | r2_hidden(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 7.71/1.51      | ~ r2_hidden(sK3,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))
% 7.71/1.51      | r2_hidden(sK3,sK2) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_2308]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3659,plain,
% 7.71/1.51      ( r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 7.71/1.51      | r2_hidden(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top
% 7.71/1.51      | r2_hidden(sK3,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != iProver_top
% 7.71/1.51      | r2_hidden(sK3,sK2) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_3657]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_6470,plain,
% 7.71/1.51      ( r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
% 7.71/1.51      | k4_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != sK2 ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_18]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_6471,plain,
% 7.71/1.51      ( k4_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != sK2
% 7.71/1.51      | r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_6470]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_16914,plain,
% 7.71/1.51      ( r2_hidden(sK3,sK2) = iProver_top ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_13692,c_31,c_34,c_44,c_53,c_56,c_79,c_1458,c_1586,c_1728,
% 7.71/1.51                 c_3659,c_6471]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_0,plain,
% 7.71/1.51      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f49]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1273,plain,
% 7.71/1.51      ( r2_hidden(X0,X1) != iProver_top | r2_hidden(X1,X0) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_16919,plain,
% 7.71/1.51      ( r2_hidden(sK2,sK3) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_16914,c_1273]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_16927,plain,
% 7.71/1.51      ( r1_xboole_0(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_14884,c_31,c_1460,c_16919]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_20085,plain,
% 7.71/1.51      ( $false ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_19616,c_16927]) ).
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.71/1.51  
% 7.71/1.51  ------                               Statistics
% 7.71/1.51  
% 7.71/1.51  ------ General
% 7.71/1.51  
% 7.71/1.51  abstr_ref_over_cycles:                  0
% 7.71/1.51  abstr_ref_under_cycles:                 0
% 7.71/1.51  gc_basic_clause_elim:                   0
% 7.71/1.51  forced_gc_time:                         0
% 7.71/1.51  parsing_time:                           0.039
% 7.71/1.51  unif_index_cands_time:                  0.
% 7.71/1.51  unif_index_add_time:                    0.
% 7.71/1.51  orderings_time:                         0.
% 7.71/1.51  out_proof_time:                         0.012
% 7.71/1.51  total_time:                             0.973
% 7.71/1.51  num_of_symbols:                         42
% 7.71/1.51  num_of_terms:                           28326
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing
% 7.71/1.51  
% 7.71/1.51  num_of_splits:                          0
% 7.71/1.51  num_of_split_atoms:                     0
% 7.71/1.51  num_of_reused_defs:                     0
% 7.71/1.51  num_eq_ax_congr_red:                    24
% 7.71/1.51  num_of_sem_filtered_clauses:            1
% 7.71/1.51  num_of_subtypes:                        0
% 7.71/1.51  monotx_restored_types:                  0
% 7.71/1.51  sat_num_of_epr_types:                   0
% 7.71/1.51  sat_num_of_non_cyclic_types:            0
% 7.71/1.51  sat_guarded_non_collapsed_types:        0
% 7.71/1.51  num_pure_diseq_elim:                    0
% 7.71/1.51  simp_replaced_by:                       0
% 7.71/1.51  res_preprocessed:                       137
% 7.71/1.51  prep_upred:                             0
% 7.71/1.51  prep_unflattend:                        0
% 7.71/1.51  smt_new_axioms:                         0
% 7.71/1.51  pred_elim_cands:                        3
% 7.71/1.51  pred_elim:                              0
% 7.71/1.51  pred_elim_cl:                           0
% 7.71/1.51  pred_elim_cycles:                       2
% 7.71/1.51  merged_defs:                            16
% 7.71/1.51  merged_defs_ncl:                        0
% 7.71/1.51  bin_hyper_res:                          16
% 7.71/1.51  prep_cycles:                            4
% 7.71/1.51  pred_elim_time:                         0.002
% 7.71/1.51  splitting_time:                         0.
% 7.71/1.51  sem_filter_time:                        0.
% 7.71/1.51  monotx_time:                            0.001
% 7.71/1.51  subtype_inf_time:                       0.
% 7.71/1.51  
% 7.71/1.51  ------ Problem properties
% 7.71/1.51  
% 7.71/1.51  clauses:                                30
% 7.71/1.51  conjectures:                            2
% 7.71/1.51  epr:                                    5
% 7.71/1.51  horn:                                   23
% 7.71/1.51  ground:                                 2
% 7.71/1.51  unary:                                  9
% 7.71/1.51  binary:                                 12
% 7.71/1.51  lits:                                   63
% 7.71/1.51  lits_eq:                                18
% 7.71/1.51  fd_pure:                                0
% 7.71/1.51  fd_pseudo:                              0
% 7.71/1.51  fd_cond:                                0
% 7.71/1.51  fd_pseudo_cond:                         6
% 7.71/1.51  ac_symbols:                             0
% 7.71/1.51  
% 7.71/1.51  ------ Propositional Solver
% 7.71/1.51  
% 7.71/1.51  prop_solver_calls:                      28
% 7.71/1.51  prop_fast_solver_calls:                 921
% 7.71/1.51  smt_solver_calls:                       0
% 7.71/1.51  smt_fast_solver_calls:                  0
% 7.71/1.51  prop_num_of_clauses:                    8500
% 7.71/1.51  prop_preprocess_simplified:             19964
% 7.71/1.51  prop_fo_subsumed:                       64
% 7.71/1.51  prop_solver_time:                       0.
% 7.71/1.51  smt_solver_time:                        0.
% 7.71/1.51  smt_fast_solver_time:                   0.
% 7.71/1.51  prop_fast_solver_time:                  0.
% 7.71/1.51  prop_unsat_core_time:                   0.
% 7.71/1.51  
% 7.71/1.51  ------ QBF
% 7.71/1.51  
% 7.71/1.51  qbf_q_res:                              0
% 7.71/1.51  qbf_num_tautologies:                    0
% 7.71/1.51  qbf_prep_cycles:                        0
% 7.71/1.51  
% 7.71/1.51  ------ BMC1
% 7.71/1.51  
% 7.71/1.51  bmc1_current_bound:                     -1
% 7.71/1.51  bmc1_last_solved_bound:                 -1
% 7.71/1.51  bmc1_unsat_core_size:                   -1
% 7.71/1.51  bmc1_unsat_core_parents_size:           -1
% 7.71/1.51  bmc1_merge_next_fun:                    0
% 7.71/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.71/1.51  
% 7.71/1.51  ------ Instantiation
% 7.71/1.51  
% 7.71/1.51  inst_num_of_clauses:                    2324
% 7.71/1.51  inst_num_in_passive:                    952
% 7.71/1.51  inst_num_in_active:                     587
% 7.71/1.51  inst_num_in_unprocessed:                785
% 7.71/1.51  inst_num_of_loops:                      630
% 7.71/1.51  inst_num_of_learning_restarts:          0
% 7.71/1.51  inst_num_moves_active_passive:          41
% 7.71/1.51  inst_lit_activity:                      0
% 7.71/1.51  inst_lit_activity_moves:                0
% 7.71/1.51  inst_num_tautologies:                   0
% 7.71/1.51  inst_num_prop_implied:                  0
% 7.71/1.51  inst_num_existing_simplified:           0
% 7.71/1.51  inst_num_eq_res_simplified:             0
% 7.71/1.51  inst_num_child_elim:                    0
% 7.71/1.51  inst_num_of_dismatching_blockings:      1642
% 7.71/1.51  inst_num_of_non_proper_insts:           2105
% 7.71/1.51  inst_num_of_duplicates:                 0
% 7.71/1.51  inst_inst_num_from_inst_to_res:         0
% 7.71/1.51  inst_dismatching_checking_time:         0.
% 7.71/1.51  
% 7.71/1.51  ------ Resolution
% 7.71/1.51  
% 7.71/1.51  res_num_of_clauses:                     0
% 7.71/1.51  res_num_in_passive:                     0
% 7.71/1.51  res_num_in_active:                      0
% 7.71/1.51  res_num_of_loops:                       141
% 7.71/1.51  res_forward_subset_subsumed:            172
% 7.71/1.51  res_backward_subset_subsumed:           6
% 7.71/1.51  res_forward_subsumed:                   0
% 7.71/1.51  res_backward_subsumed:                  0
% 7.71/1.51  res_forward_subsumption_resolution:     0
% 7.71/1.51  res_backward_subsumption_resolution:    0
% 7.71/1.51  res_clause_to_clause_subsumption:       2526
% 7.71/1.51  res_orphan_elimination:                 0
% 7.71/1.51  res_tautology_del:                      91
% 7.71/1.51  res_num_eq_res_simplified:              0
% 7.71/1.51  res_num_sel_changes:                    0
% 7.71/1.51  res_moves_from_active_to_pass:          0
% 7.71/1.51  
% 7.71/1.51  ------ Superposition
% 7.71/1.51  
% 7.71/1.51  sup_time_total:                         0.
% 7.71/1.51  sup_time_generating:                    0.
% 7.71/1.51  sup_time_sim_full:                      0.
% 7.71/1.51  sup_time_sim_immed:                     0.
% 7.71/1.51  
% 7.71/1.51  sup_num_of_clauses:                     401
% 7.71/1.51  sup_num_in_active:                      120
% 7.71/1.51  sup_num_in_passive:                     281
% 7.71/1.51  sup_num_of_loops:                       125
% 7.71/1.51  sup_fw_superposition:                   527
% 7.71/1.51  sup_bw_superposition:                   526
% 7.71/1.51  sup_immediate_simplified:               143
% 7.71/1.51  sup_given_eliminated:                   0
% 7.71/1.51  comparisons_done:                       0
% 7.71/1.51  comparisons_avoided:                    2
% 7.71/1.51  
% 7.71/1.51  ------ Simplifications
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  sim_fw_subset_subsumed:                 10
% 7.71/1.51  sim_bw_subset_subsumed:                 4
% 7.71/1.51  sim_fw_subsumed:                        89
% 7.71/1.51  sim_bw_subsumed:                        7
% 7.71/1.51  sim_fw_subsumption_res:                 2
% 7.71/1.51  sim_bw_subsumption_res:                 0
% 7.71/1.51  sim_tautology_del:                      40
% 7.71/1.51  sim_eq_tautology_del:                   3
% 7.71/1.51  sim_eq_res_simp:                        1
% 7.71/1.51  sim_fw_demodulated:                     27
% 7.71/1.51  sim_bw_demodulated:                     2
% 7.71/1.51  sim_light_normalised:                   16
% 7.71/1.51  sim_joinable_taut:                      0
% 7.71/1.51  sim_joinable_simp:                      0
% 7.71/1.51  sim_ac_normalised:                      0
% 7.71/1.51  sim_smt_subsumption:                    0
% 7.71/1.51  
%------------------------------------------------------------------------------
