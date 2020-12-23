%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:36 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 225 expanded)
%              Number of clauses        :   67 (  81 expanded)
%              Number of leaves         :   15 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  343 (1069 expanded)
%              Number of equality atoms :   96 ( 169 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK1(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK1(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK1(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK1(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ~ ( ! [X2] :
              ( v3_ordinal1(X2)
             => ~ ( ! [X3] :
                      ( v3_ordinal1(X3)
                     => ( r2_hidden(X3,X0)
                       => r1_ordinal1(X2,X3) ) )
                  & r2_hidden(X2,X0) ) )
          & k1_xboole_0 != X0
          & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ~ ( ! [X2] :
                ( v3_ordinal1(X2)
               => ~ ( ! [X3] :
                        ( v3_ordinal1(X3)
                       => ( r2_hidden(X3,X0)
                         => r1_ordinal1(X2,X3) ) )
                    & r2_hidden(X2,X0) ) )
            & k1_xboole_0 != X0
            & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f29,plain,(
    ! [X0,X2] :
      ( ? [X3] :
          ( ~ r1_ordinal1(X2,X3)
          & r2_hidden(X3,X0)
          & v3_ordinal1(X3) )
     => ( ~ r1_ordinal1(X2,sK4(X2))
        & r2_hidden(sK4(X2),X0)
        & v3_ordinal1(sK4(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( ~ r1_ordinal1(X2,X3)
                & r2_hidden(X3,X0)
                & v3_ordinal1(X3) )
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1)
        & v3_ordinal1(X1) )
   => ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,sK2)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,sK2)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != sK2
      & r1_tarski(sK2,sK3)
      & v3_ordinal1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ! [X2] :
        ( ( ~ r1_ordinal1(X2,sK4(X2))
          & r2_hidden(sK4(X2),sK2)
          & v3_ordinal1(sK4(X2)) )
        | ~ r2_hidden(X2,sK2)
        | ~ v3_ordinal1(X2) )
    & k1_xboole_0 != sK2
    & r1_tarski(sK2,sK3)
    & v3_ordinal1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f29,f28])).

fof(f43,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X2] :
      ( r2_hidden(sK4(X2),sK2)
      | ~ r2_hidden(X2,sK2)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X2] :
      ( ~ r1_ordinal1(X2,sK4(X2))
      | ~ r2_hidden(X2,sK2)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X2] :
      ( v3_ordinal1(sK4(X2))
      | ~ r2_hidden(X2,sK2)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK1(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_739,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_737,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_731,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1082,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_731])).

cnf(c_1689,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_739,c_1082])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(X1),X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_733,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK1(X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2496,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1689,c_733])).

cnf(c_4,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_736,plain,
    ( r1_tarski(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_728,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_738,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1660,plain,
    ( r1_tarski(X0,sK3) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_728,c_738])).

cnf(c_2091,plain,
    ( r1_tarski(k1_tarski(X0),sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_1660])).

cnf(c_5,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_735,plain,
    ( r1_tarski(k1_tarski(X0),X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2276,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2091,c_735])).

cnf(c_3393,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK1(sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2496,c_2276])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(sK4(X0),sK2)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_730,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK4(X0),sK2) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_11,negated_conjecture,
    ( ~ r1_ordinal1(X0,sK4(X0))
    | ~ r2_hidden(X0,sK2)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_215,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,sK2)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | X2 != X1
    | sK4(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_11])).

cnf(c_216,plain,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(sK4(X0),X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK4(X0)) ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ v3_ordinal1(X0)
    | v3_ordinal1(sK4(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_220,plain,
    ( ~ v3_ordinal1(X0)
    | r2_hidden(sK4(X0),X0)
    | ~ r2_hidden(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_216,c_13])).

cnf(c_221,plain,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(sK4(X0),X0)
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_220])).

cnf(c_726,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK4(X0),X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,sK1(X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_734,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,sK1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1947,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK4(sK1(X1)),X1) != iProver_top
    | r2_hidden(sK1(X1),sK2) != iProver_top
    | v3_ordinal1(sK1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_726,c_734])).

cnf(c_2334,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK1(sK2),sK2) != iProver_top
    | v3_ordinal1(sK1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_730,c_1947])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_888,plain,
    ( r2_hidden(sK0(sK2,k1_xboole_0),sK2)
    | r2_hidden(sK0(sK2,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_889,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK0(sK2,k1_xboole_0),sK2) = iProver_top
    | r2_hidden(sK0(sK2,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_888])).

cnf(c_951,plain,
    ( ~ r2_hidden(sK0(sK2,k1_xboole_0),sK2)
    | r2_hidden(sK1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_955,plain,
    ( r2_hidden(sK0(sK2,k1_xboole_0),sK2) != iProver_top
    | r2_hidden(sK1(sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_951])).

cnf(c_863,plain,
    ( ~ r1_tarski(k1_xboole_0,X0)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1072,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0))
    | ~ r2_hidden(sK0(sK2,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_1073,plain,
    ( r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0)) != iProver_top
    | r2_hidden(sK0(sK2,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1072])).

cnf(c_1245,plain,
    ( r2_hidden(sK4(sK1(sK2)),sK2)
    | ~ r2_hidden(sK1(sK2),sK2)
    | ~ v3_ordinal1(sK1(sK2)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1246,plain,
    ( r2_hidden(sK4(sK1(sK2)),sK2) = iProver_top
    | r2_hidden(sK1(sK2),sK2) != iProver_top
    | v3_ordinal1(sK1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1245])).

cnf(c_1243,plain,
    ( r2_hidden(sK4(sK1(sK2)),sK1(sK2))
    | ~ r2_hidden(sK1(sK2),sK2)
    | ~ v3_ordinal1(sK1(sK2)) ),
    inference(instantiation,[status(thm)],[c_221])).

cnf(c_1250,plain,
    ( r2_hidden(sK4(sK1(sK2)),sK1(sK2)) = iProver_top
    | r2_hidden(sK1(sK2),sK2) != iProver_top
    | v3_ordinal1(sK1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1243])).

cnf(c_1285,plain,
    ( r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1286,plain,
    ( r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1285])).

cnf(c_950,plain,
    ( ~ r2_hidden(X0,sK1(sK2))
    | ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(sK0(sK2,k1_xboole_0),sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1826,plain,
    ( ~ r2_hidden(sK0(sK2,k1_xboole_0),sK2)
    | ~ r2_hidden(sK4(sK1(sK2)),sK1(sK2))
    | ~ r2_hidden(sK4(sK1(sK2)),sK2) ),
    inference(instantiation,[status(thm)],[c_950])).

cnf(c_1836,plain,
    ( r2_hidden(sK0(sK2,k1_xboole_0),sK2) != iProver_top
    | r2_hidden(sK4(sK1(sK2)),sK1(sK2)) != iProver_top
    | r2_hidden(sK4(sK1(sK2)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1826])).

cnf(c_2339,plain,
    ( v3_ordinal1(sK1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2334,c_14,c_889,c_955,c_1073,c_1246,c_1250,c_1286,c_1836])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_858,plain,
    ( ~ r2_hidden(X0,sK3)
    | v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2175,plain,
    ( ~ r2_hidden(sK1(sK2),sK3)
    | v3_ordinal1(sK1(sK2))
    | ~ v3_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_858])).

cnf(c_2176,plain,
    ( r2_hidden(sK1(sK2),sK3) != iProver_top
    | v3_ordinal1(sK1(sK2)) = iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2175])).

cnf(c_372,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1016,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_373,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_884,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_1015,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_16,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3393,c_2339,c_2176,c_1016,c_1015,c_14,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.38/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.02  
% 2.38/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.38/1.02  
% 2.38/1.02  ------  iProver source info
% 2.38/1.02  
% 2.38/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.38/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.38/1.02  git: non_committed_changes: false
% 2.38/1.02  git: last_make_outside_of_git: false
% 2.38/1.02  
% 2.38/1.02  ------ 
% 2.38/1.02  
% 2.38/1.02  ------ Input Options
% 2.38/1.02  
% 2.38/1.02  --out_options                           all
% 2.38/1.02  --tptp_safe_out                         true
% 2.38/1.02  --problem_path                          ""
% 2.38/1.02  --include_path                          ""
% 2.38/1.02  --clausifier                            res/vclausify_rel
% 2.38/1.02  --clausifier_options                    --mode clausify
% 2.38/1.02  --stdin                                 false
% 2.38/1.02  --stats_out                             all
% 2.38/1.02  
% 2.38/1.02  ------ General Options
% 2.38/1.02  
% 2.38/1.02  --fof                                   false
% 2.38/1.02  --time_out_real                         305.
% 2.38/1.02  --time_out_virtual                      -1.
% 2.38/1.02  --symbol_type_check                     false
% 2.38/1.02  --clausify_out                          false
% 2.38/1.02  --sig_cnt_out                           false
% 2.38/1.02  --trig_cnt_out                          false
% 2.38/1.02  --trig_cnt_out_tolerance                1.
% 2.38/1.02  --trig_cnt_out_sk_spl                   false
% 2.38/1.02  --abstr_cl_out                          false
% 2.38/1.02  
% 2.38/1.02  ------ Global Options
% 2.38/1.02  
% 2.38/1.02  --schedule                              default
% 2.38/1.02  --add_important_lit                     false
% 2.38/1.02  --prop_solver_per_cl                    1000
% 2.38/1.02  --min_unsat_core                        false
% 2.38/1.02  --soft_assumptions                      false
% 2.38/1.02  --soft_lemma_size                       3
% 2.38/1.02  --prop_impl_unit_size                   0
% 2.38/1.02  --prop_impl_unit                        []
% 2.38/1.02  --share_sel_clauses                     true
% 2.38/1.02  --reset_solvers                         false
% 2.38/1.02  --bc_imp_inh                            [conj_cone]
% 2.38/1.02  --conj_cone_tolerance                   3.
% 2.38/1.02  --extra_neg_conj                        none
% 2.38/1.02  --large_theory_mode                     true
% 2.38/1.02  --prolific_symb_bound                   200
% 2.38/1.02  --lt_threshold                          2000
% 2.38/1.02  --clause_weak_htbl                      true
% 2.38/1.02  --gc_record_bc_elim                     false
% 2.38/1.02  
% 2.38/1.02  ------ Preprocessing Options
% 2.38/1.02  
% 2.38/1.02  --preprocessing_flag                    true
% 2.38/1.02  --time_out_prep_mult                    0.1
% 2.38/1.02  --splitting_mode                        input
% 2.38/1.02  --splitting_grd                         true
% 2.38/1.02  --splitting_cvd                         false
% 2.38/1.02  --splitting_cvd_svl                     false
% 2.38/1.02  --splitting_nvd                         32
% 2.38/1.02  --sub_typing                            true
% 2.38/1.02  --prep_gs_sim                           true
% 2.38/1.02  --prep_unflatten                        true
% 2.38/1.02  --prep_res_sim                          true
% 2.38/1.02  --prep_upred                            true
% 2.38/1.02  --prep_sem_filter                       exhaustive
% 2.38/1.02  --prep_sem_filter_out                   false
% 2.38/1.02  --pred_elim                             true
% 2.38/1.02  --res_sim_input                         true
% 2.38/1.02  --eq_ax_congr_red                       true
% 2.38/1.02  --pure_diseq_elim                       true
% 2.38/1.02  --brand_transform                       false
% 2.38/1.02  --non_eq_to_eq                          false
% 2.38/1.02  --prep_def_merge                        true
% 2.38/1.02  --prep_def_merge_prop_impl              false
% 2.38/1.02  --prep_def_merge_mbd                    true
% 2.38/1.02  --prep_def_merge_tr_red                 false
% 2.38/1.02  --prep_def_merge_tr_cl                  false
% 2.38/1.02  --smt_preprocessing                     true
% 2.38/1.02  --smt_ac_axioms                         fast
% 2.38/1.02  --preprocessed_out                      false
% 2.38/1.02  --preprocessed_stats                    false
% 2.38/1.02  
% 2.38/1.02  ------ Abstraction refinement Options
% 2.38/1.02  
% 2.38/1.02  --abstr_ref                             []
% 2.38/1.02  --abstr_ref_prep                        false
% 2.38/1.02  --abstr_ref_until_sat                   false
% 2.38/1.02  --abstr_ref_sig_restrict                funpre
% 2.38/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.38/1.02  --abstr_ref_under                       []
% 2.38/1.02  
% 2.38/1.02  ------ SAT Options
% 2.38/1.02  
% 2.38/1.02  --sat_mode                              false
% 2.38/1.02  --sat_fm_restart_options                ""
% 2.38/1.02  --sat_gr_def                            false
% 2.38/1.02  --sat_epr_types                         true
% 2.38/1.02  --sat_non_cyclic_types                  false
% 2.38/1.02  --sat_finite_models                     false
% 2.38/1.02  --sat_fm_lemmas                         false
% 2.38/1.02  --sat_fm_prep                           false
% 2.38/1.02  --sat_fm_uc_incr                        true
% 2.38/1.02  --sat_out_model                         small
% 2.38/1.02  --sat_out_clauses                       false
% 2.38/1.02  
% 2.38/1.02  ------ QBF Options
% 2.38/1.02  
% 2.38/1.02  --qbf_mode                              false
% 2.38/1.02  --qbf_elim_univ                         false
% 2.38/1.02  --qbf_dom_inst                          none
% 2.38/1.02  --qbf_dom_pre_inst                      false
% 2.38/1.02  --qbf_sk_in                             false
% 2.38/1.02  --qbf_pred_elim                         true
% 2.38/1.02  --qbf_split                             512
% 2.38/1.02  
% 2.38/1.02  ------ BMC1 Options
% 2.38/1.02  
% 2.38/1.02  --bmc1_incremental                      false
% 2.38/1.02  --bmc1_axioms                           reachable_all
% 2.38/1.02  --bmc1_min_bound                        0
% 2.38/1.02  --bmc1_max_bound                        -1
% 2.38/1.02  --bmc1_max_bound_default                -1
% 2.38/1.02  --bmc1_symbol_reachability              true
% 2.38/1.02  --bmc1_property_lemmas                  false
% 2.38/1.02  --bmc1_k_induction                      false
% 2.38/1.02  --bmc1_non_equiv_states                 false
% 2.38/1.02  --bmc1_deadlock                         false
% 2.38/1.02  --bmc1_ucm                              false
% 2.38/1.02  --bmc1_add_unsat_core                   none
% 2.38/1.02  --bmc1_unsat_core_children              false
% 2.38/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.38/1.02  --bmc1_out_stat                         full
% 2.38/1.02  --bmc1_ground_init                      false
% 2.38/1.02  --bmc1_pre_inst_next_state              false
% 2.38/1.02  --bmc1_pre_inst_state                   false
% 2.38/1.02  --bmc1_pre_inst_reach_state             false
% 2.38/1.02  --bmc1_out_unsat_core                   false
% 2.38/1.02  --bmc1_aig_witness_out                  false
% 2.38/1.02  --bmc1_verbose                          false
% 2.38/1.02  --bmc1_dump_clauses_tptp                false
% 2.38/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.38/1.02  --bmc1_dump_file                        -
% 2.38/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.38/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.38/1.02  --bmc1_ucm_extend_mode                  1
% 2.38/1.02  --bmc1_ucm_init_mode                    2
% 2.38/1.02  --bmc1_ucm_cone_mode                    none
% 2.38/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.38/1.02  --bmc1_ucm_relax_model                  4
% 2.38/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.38/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.38/1.02  --bmc1_ucm_layered_model                none
% 2.38/1.02  --bmc1_ucm_max_lemma_size               10
% 2.38/1.02  
% 2.38/1.02  ------ AIG Options
% 2.38/1.02  
% 2.38/1.02  --aig_mode                              false
% 2.38/1.02  
% 2.38/1.02  ------ Instantiation Options
% 2.38/1.02  
% 2.38/1.02  --instantiation_flag                    true
% 2.38/1.02  --inst_sos_flag                         false
% 2.38/1.02  --inst_sos_phase                        true
% 2.38/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.38/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.38/1.02  --inst_lit_sel_side                     num_symb
% 2.38/1.02  --inst_solver_per_active                1400
% 2.38/1.02  --inst_solver_calls_frac                1.
% 2.38/1.02  --inst_passive_queue_type               priority_queues
% 2.38/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.38/1.02  --inst_passive_queues_freq              [25;2]
% 2.38/1.02  --inst_dismatching                      true
% 2.38/1.02  --inst_eager_unprocessed_to_passive     true
% 2.38/1.02  --inst_prop_sim_given                   true
% 2.38/1.02  --inst_prop_sim_new                     false
% 2.38/1.02  --inst_subs_new                         false
% 2.38/1.02  --inst_eq_res_simp                      false
% 2.38/1.02  --inst_subs_given                       false
% 2.38/1.02  --inst_orphan_elimination               true
% 2.38/1.02  --inst_learning_loop_flag               true
% 2.38/1.02  --inst_learning_start                   3000
% 2.38/1.02  --inst_learning_factor                  2
% 2.38/1.02  --inst_start_prop_sim_after_learn       3
% 2.38/1.02  --inst_sel_renew                        solver
% 2.38/1.02  --inst_lit_activity_flag                true
% 2.38/1.02  --inst_restr_to_given                   false
% 2.38/1.02  --inst_activity_threshold               500
% 2.38/1.02  --inst_out_proof                        true
% 2.38/1.02  
% 2.38/1.02  ------ Resolution Options
% 2.38/1.02  
% 2.38/1.02  --resolution_flag                       true
% 2.38/1.02  --res_lit_sel                           adaptive
% 2.38/1.02  --res_lit_sel_side                      none
% 2.38/1.02  --res_ordering                          kbo
% 2.38/1.02  --res_to_prop_solver                    active
% 2.38/1.02  --res_prop_simpl_new                    false
% 2.38/1.02  --res_prop_simpl_given                  true
% 2.38/1.02  --res_passive_queue_type                priority_queues
% 2.38/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.38/1.02  --res_passive_queues_freq               [15;5]
% 2.38/1.02  --res_forward_subs                      full
% 2.38/1.02  --res_backward_subs                     full
% 2.38/1.02  --res_forward_subs_resolution           true
% 2.38/1.02  --res_backward_subs_resolution          true
% 2.38/1.02  --res_orphan_elimination                true
% 2.38/1.02  --res_time_limit                        2.
% 2.38/1.02  --res_out_proof                         true
% 2.38/1.02  
% 2.38/1.02  ------ Superposition Options
% 2.38/1.02  
% 2.38/1.02  --superposition_flag                    true
% 2.38/1.02  --sup_passive_queue_type                priority_queues
% 2.38/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.38/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.38/1.02  --demod_completeness_check              fast
% 2.38/1.02  --demod_use_ground                      true
% 2.38/1.02  --sup_to_prop_solver                    passive
% 2.38/1.02  --sup_prop_simpl_new                    true
% 2.38/1.02  --sup_prop_simpl_given                  true
% 2.38/1.02  --sup_fun_splitting                     false
% 2.38/1.02  --sup_smt_interval                      50000
% 2.38/1.02  
% 2.38/1.02  ------ Superposition Simplification Setup
% 2.38/1.02  
% 2.38/1.02  --sup_indices_passive                   []
% 2.38/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.38/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.02  --sup_full_bw                           [BwDemod]
% 2.38/1.02  --sup_immed_triv                        [TrivRules]
% 2.38/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.38/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.02  --sup_immed_bw_main                     []
% 2.38/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.38/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.02  
% 2.38/1.02  ------ Combination Options
% 2.38/1.02  
% 2.38/1.02  --comb_res_mult                         3
% 2.38/1.02  --comb_sup_mult                         2
% 2.38/1.02  --comb_inst_mult                        10
% 2.38/1.02  
% 2.38/1.02  ------ Debug Options
% 2.38/1.02  
% 2.38/1.02  --dbg_backtrace                         false
% 2.38/1.02  --dbg_dump_prop_clauses                 false
% 2.38/1.02  --dbg_dump_prop_clauses_file            -
% 2.38/1.02  --dbg_out_stat                          false
% 2.38/1.02  ------ Parsing...
% 2.38/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.38/1.02  
% 2.38/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.38/1.02  
% 2.38/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.38/1.02  
% 2.38/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.38/1.02  ------ Proving...
% 2.38/1.02  ------ Problem Properties 
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  clauses                                 16
% 2.38/1.02  conjectures                             5
% 2.38/1.02  EPR                                     7
% 2.38/1.02  Horn                                    15
% 2.38/1.02  unary                                   4
% 2.38/1.02  binary                                  4
% 2.38/1.02  lits                                    36
% 2.38/1.02  lits eq                                 3
% 2.38/1.02  fd_pure                                 0
% 2.38/1.02  fd_pseudo                               0
% 2.38/1.02  fd_cond                                 0
% 2.38/1.02  fd_pseudo_cond                          2
% 2.38/1.02  AC symbols                              0
% 2.38/1.02  
% 2.38/1.02  ------ Schedule dynamic 5 is on 
% 2.38/1.02  
% 2.38/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  ------ 
% 2.38/1.02  Current options:
% 2.38/1.02  ------ 
% 2.38/1.02  
% 2.38/1.02  ------ Input Options
% 2.38/1.02  
% 2.38/1.02  --out_options                           all
% 2.38/1.02  --tptp_safe_out                         true
% 2.38/1.02  --problem_path                          ""
% 2.38/1.02  --include_path                          ""
% 2.38/1.02  --clausifier                            res/vclausify_rel
% 2.38/1.02  --clausifier_options                    --mode clausify
% 2.38/1.02  --stdin                                 false
% 2.38/1.02  --stats_out                             all
% 2.38/1.02  
% 2.38/1.02  ------ General Options
% 2.38/1.02  
% 2.38/1.02  --fof                                   false
% 2.38/1.02  --time_out_real                         305.
% 2.38/1.02  --time_out_virtual                      -1.
% 2.38/1.02  --symbol_type_check                     false
% 2.38/1.02  --clausify_out                          false
% 2.38/1.02  --sig_cnt_out                           false
% 2.38/1.02  --trig_cnt_out                          false
% 2.38/1.02  --trig_cnt_out_tolerance                1.
% 2.38/1.02  --trig_cnt_out_sk_spl                   false
% 2.38/1.02  --abstr_cl_out                          false
% 2.38/1.02  
% 2.38/1.02  ------ Global Options
% 2.38/1.02  
% 2.38/1.02  --schedule                              default
% 2.38/1.02  --add_important_lit                     false
% 2.38/1.02  --prop_solver_per_cl                    1000
% 2.38/1.02  --min_unsat_core                        false
% 2.38/1.02  --soft_assumptions                      false
% 2.38/1.02  --soft_lemma_size                       3
% 2.38/1.02  --prop_impl_unit_size                   0
% 2.38/1.02  --prop_impl_unit                        []
% 2.38/1.02  --share_sel_clauses                     true
% 2.38/1.02  --reset_solvers                         false
% 2.38/1.02  --bc_imp_inh                            [conj_cone]
% 2.38/1.02  --conj_cone_tolerance                   3.
% 2.38/1.02  --extra_neg_conj                        none
% 2.38/1.02  --large_theory_mode                     true
% 2.38/1.02  --prolific_symb_bound                   200
% 2.38/1.02  --lt_threshold                          2000
% 2.38/1.02  --clause_weak_htbl                      true
% 2.38/1.02  --gc_record_bc_elim                     false
% 2.38/1.02  
% 2.38/1.02  ------ Preprocessing Options
% 2.38/1.02  
% 2.38/1.02  --preprocessing_flag                    true
% 2.38/1.02  --time_out_prep_mult                    0.1
% 2.38/1.02  --splitting_mode                        input
% 2.38/1.02  --splitting_grd                         true
% 2.38/1.02  --splitting_cvd                         false
% 2.38/1.02  --splitting_cvd_svl                     false
% 2.38/1.02  --splitting_nvd                         32
% 2.38/1.02  --sub_typing                            true
% 2.38/1.02  --prep_gs_sim                           true
% 2.38/1.02  --prep_unflatten                        true
% 2.38/1.02  --prep_res_sim                          true
% 2.38/1.02  --prep_upred                            true
% 2.38/1.02  --prep_sem_filter                       exhaustive
% 2.38/1.02  --prep_sem_filter_out                   false
% 2.38/1.02  --pred_elim                             true
% 2.38/1.02  --res_sim_input                         true
% 2.38/1.02  --eq_ax_congr_red                       true
% 2.38/1.02  --pure_diseq_elim                       true
% 2.38/1.02  --brand_transform                       false
% 2.38/1.02  --non_eq_to_eq                          false
% 2.38/1.02  --prep_def_merge                        true
% 2.38/1.02  --prep_def_merge_prop_impl              false
% 2.38/1.02  --prep_def_merge_mbd                    true
% 2.38/1.02  --prep_def_merge_tr_red                 false
% 2.38/1.02  --prep_def_merge_tr_cl                  false
% 2.38/1.02  --smt_preprocessing                     true
% 2.38/1.02  --smt_ac_axioms                         fast
% 2.38/1.02  --preprocessed_out                      false
% 2.38/1.02  --preprocessed_stats                    false
% 2.38/1.02  
% 2.38/1.02  ------ Abstraction refinement Options
% 2.38/1.02  
% 2.38/1.02  --abstr_ref                             []
% 2.38/1.02  --abstr_ref_prep                        false
% 2.38/1.02  --abstr_ref_until_sat                   false
% 2.38/1.02  --abstr_ref_sig_restrict                funpre
% 2.38/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.38/1.02  --abstr_ref_under                       []
% 2.38/1.02  
% 2.38/1.02  ------ SAT Options
% 2.38/1.02  
% 2.38/1.02  --sat_mode                              false
% 2.38/1.02  --sat_fm_restart_options                ""
% 2.38/1.02  --sat_gr_def                            false
% 2.38/1.02  --sat_epr_types                         true
% 2.38/1.02  --sat_non_cyclic_types                  false
% 2.38/1.02  --sat_finite_models                     false
% 2.38/1.02  --sat_fm_lemmas                         false
% 2.38/1.02  --sat_fm_prep                           false
% 2.38/1.02  --sat_fm_uc_incr                        true
% 2.38/1.02  --sat_out_model                         small
% 2.38/1.02  --sat_out_clauses                       false
% 2.38/1.02  
% 2.38/1.02  ------ QBF Options
% 2.38/1.02  
% 2.38/1.02  --qbf_mode                              false
% 2.38/1.02  --qbf_elim_univ                         false
% 2.38/1.02  --qbf_dom_inst                          none
% 2.38/1.02  --qbf_dom_pre_inst                      false
% 2.38/1.02  --qbf_sk_in                             false
% 2.38/1.02  --qbf_pred_elim                         true
% 2.38/1.02  --qbf_split                             512
% 2.38/1.02  
% 2.38/1.02  ------ BMC1 Options
% 2.38/1.02  
% 2.38/1.02  --bmc1_incremental                      false
% 2.38/1.02  --bmc1_axioms                           reachable_all
% 2.38/1.02  --bmc1_min_bound                        0
% 2.38/1.02  --bmc1_max_bound                        -1
% 2.38/1.02  --bmc1_max_bound_default                -1
% 2.38/1.02  --bmc1_symbol_reachability              true
% 2.38/1.02  --bmc1_property_lemmas                  false
% 2.38/1.02  --bmc1_k_induction                      false
% 2.38/1.02  --bmc1_non_equiv_states                 false
% 2.38/1.02  --bmc1_deadlock                         false
% 2.38/1.02  --bmc1_ucm                              false
% 2.38/1.02  --bmc1_add_unsat_core                   none
% 2.38/1.02  --bmc1_unsat_core_children              false
% 2.38/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.38/1.02  --bmc1_out_stat                         full
% 2.38/1.02  --bmc1_ground_init                      false
% 2.38/1.02  --bmc1_pre_inst_next_state              false
% 2.38/1.02  --bmc1_pre_inst_state                   false
% 2.38/1.02  --bmc1_pre_inst_reach_state             false
% 2.38/1.02  --bmc1_out_unsat_core                   false
% 2.38/1.02  --bmc1_aig_witness_out                  false
% 2.38/1.02  --bmc1_verbose                          false
% 2.38/1.02  --bmc1_dump_clauses_tptp                false
% 2.38/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.38/1.02  --bmc1_dump_file                        -
% 2.38/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.38/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.38/1.02  --bmc1_ucm_extend_mode                  1
% 2.38/1.02  --bmc1_ucm_init_mode                    2
% 2.38/1.02  --bmc1_ucm_cone_mode                    none
% 2.38/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.38/1.02  --bmc1_ucm_relax_model                  4
% 2.38/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.38/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.38/1.02  --bmc1_ucm_layered_model                none
% 2.38/1.02  --bmc1_ucm_max_lemma_size               10
% 2.38/1.02  
% 2.38/1.02  ------ AIG Options
% 2.38/1.02  
% 2.38/1.02  --aig_mode                              false
% 2.38/1.02  
% 2.38/1.02  ------ Instantiation Options
% 2.38/1.02  
% 2.38/1.02  --instantiation_flag                    true
% 2.38/1.02  --inst_sos_flag                         false
% 2.38/1.02  --inst_sos_phase                        true
% 2.38/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.38/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.38/1.02  --inst_lit_sel_side                     none
% 2.38/1.02  --inst_solver_per_active                1400
% 2.38/1.02  --inst_solver_calls_frac                1.
% 2.38/1.02  --inst_passive_queue_type               priority_queues
% 2.38/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.38/1.02  --inst_passive_queues_freq              [25;2]
% 2.38/1.02  --inst_dismatching                      true
% 2.38/1.02  --inst_eager_unprocessed_to_passive     true
% 2.38/1.02  --inst_prop_sim_given                   true
% 2.38/1.02  --inst_prop_sim_new                     false
% 2.38/1.02  --inst_subs_new                         false
% 2.38/1.02  --inst_eq_res_simp                      false
% 2.38/1.02  --inst_subs_given                       false
% 2.38/1.02  --inst_orphan_elimination               true
% 2.38/1.02  --inst_learning_loop_flag               true
% 2.38/1.02  --inst_learning_start                   3000
% 2.38/1.02  --inst_learning_factor                  2
% 2.38/1.02  --inst_start_prop_sim_after_learn       3
% 2.38/1.02  --inst_sel_renew                        solver
% 2.38/1.02  --inst_lit_activity_flag                true
% 2.38/1.02  --inst_restr_to_given                   false
% 2.38/1.02  --inst_activity_threshold               500
% 2.38/1.02  --inst_out_proof                        true
% 2.38/1.02  
% 2.38/1.02  ------ Resolution Options
% 2.38/1.02  
% 2.38/1.02  --resolution_flag                       false
% 2.38/1.02  --res_lit_sel                           adaptive
% 2.38/1.02  --res_lit_sel_side                      none
% 2.38/1.02  --res_ordering                          kbo
% 2.38/1.02  --res_to_prop_solver                    active
% 2.38/1.02  --res_prop_simpl_new                    false
% 2.38/1.02  --res_prop_simpl_given                  true
% 2.38/1.02  --res_passive_queue_type                priority_queues
% 2.38/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.38/1.02  --res_passive_queues_freq               [15;5]
% 2.38/1.02  --res_forward_subs                      full
% 2.38/1.02  --res_backward_subs                     full
% 2.38/1.02  --res_forward_subs_resolution           true
% 2.38/1.02  --res_backward_subs_resolution          true
% 2.38/1.02  --res_orphan_elimination                true
% 2.38/1.02  --res_time_limit                        2.
% 2.38/1.02  --res_out_proof                         true
% 2.38/1.02  
% 2.38/1.02  ------ Superposition Options
% 2.38/1.02  
% 2.38/1.02  --superposition_flag                    true
% 2.38/1.02  --sup_passive_queue_type                priority_queues
% 2.38/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.38/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.38/1.02  --demod_completeness_check              fast
% 2.38/1.02  --demod_use_ground                      true
% 2.38/1.02  --sup_to_prop_solver                    passive
% 2.38/1.02  --sup_prop_simpl_new                    true
% 2.38/1.02  --sup_prop_simpl_given                  true
% 2.38/1.02  --sup_fun_splitting                     false
% 2.38/1.02  --sup_smt_interval                      50000
% 2.38/1.02  
% 2.38/1.02  ------ Superposition Simplification Setup
% 2.38/1.02  
% 2.38/1.02  --sup_indices_passive                   []
% 2.38/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.38/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.02  --sup_full_bw                           [BwDemod]
% 2.38/1.02  --sup_immed_triv                        [TrivRules]
% 2.38/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.38/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.02  --sup_immed_bw_main                     []
% 2.38/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.38/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.02  
% 2.38/1.02  ------ Combination Options
% 2.38/1.02  
% 2.38/1.02  --comb_res_mult                         3
% 2.38/1.02  --comb_sup_mult                         2
% 2.38/1.02  --comb_inst_mult                        10
% 2.38/1.02  
% 2.38/1.02  ------ Debug Options
% 2.38/1.02  
% 2.38/1.02  --dbg_backtrace                         false
% 2.38/1.02  --dbg_dump_prop_clauses                 false
% 2.38/1.02  --dbg_dump_prop_clauses_file            -
% 2.38/1.02  --dbg_out_stat                          false
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  ------ Proving...
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  % SZS status Theorem for theBenchmark.p
% 2.38/1.02  
% 2.38/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.38/1.02  
% 2.38/1.02  fof(f1,axiom,(
% 2.38/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f11,plain,(
% 2.38/1.02    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.38/1.02    inference(ennf_transformation,[],[f1])).
% 2.38/1.02  
% 2.38/1.02  fof(f22,plain,(
% 2.38/1.02    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.38/1.02    inference(nnf_transformation,[],[f11])).
% 2.38/1.02  
% 2.38/1.02  fof(f23,plain,(
% 2.38/1.02    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f24,plain,(
% 2.38/1.02    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.38/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 2.38/1.02  
% 2.38/1.02  fof(f31,plain,(
% 2.38/1.02    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f24])).
% 2.38/1.02  
% 2.38/1.02  fof(f3,axiom,(
% 2.38/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f34,plain,(
% 2.38/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f3])).
% 2.38/1.02  
% 2.38/1.02  fof(f8,axiom,(
% 2.38/1.02    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f19,plain,(
% 2.38/1.02    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.38/1.02    inference(ennf_transformation,[],[f8])).
% 2.38/1.02  
% 2.38/1.02  fof(f41,plain,(
% 2.38/1.02    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f19])).
% 2.38/1.02  
% 2.38/1.02  fof(f5,axiom,(
% 2.38/1.02    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f14,plain,(
% 2.38/1.02    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 2.38/1.02    inference(ennf_transformation,[],[f5])).
% 2.38/1.02  
% 2.38/1.02  fof(f26,plain,(
% 2.38/1.02    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK1(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK1(X1),X1)))),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f27,plain,(
% 2.38/1.02    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK1(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK1(X1),X1)) | ~r2_hidden(X0,X1))),
% 2.38/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f26])).
% 2.38/1.02  
% 2.38/1.02  fof(f37,plain,(
% 2.38/1.02    ( ! [X0,X1] : (r2_hidden(sK1(X1),X1) | ~r2_hidden(X0,X1)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f27])).
% 2.38/1.02  
% 2.38/1.02  fof(f4,axiom,(
% 2.38/1.02    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f25,plain,(
% 2.38/1.02    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.38/1.02    inference(nnf_transformation,[],[f4])).
% 2.38/1.02  
% 2.38/1.02  fof(f36,plain,(
% 2.38/1.02    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f25])).
% 2.38/1.02  
% 2.38/1.02  fof(f9,conjecture,(
% 2.38/1.02    ! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f10,negated_conjecture,(
% 2.38/1.02    ~! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 2.38/1.02    inference(negated_conjecture,[],[f9])).
% 2.38/1.02  
% 2.38/1.02  fof(f20,plain,(
% 2.38/1.02    ? [X0,X1] : ((! [X2] : ((? [X3] : ((~r1_ordinal1(X2,X3) & r2_hidden(X3,X0)) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0)) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1)) & v3_ordinal1(X1))),
% 2.38/1.02    inference(ennf_transformation,[],[f10])).
% 2.38/1.02  
% 2.38/1.02  fof(f21,plain,(
% 2.38/1.02    ? [X0,X1] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1))),
% 2.38/1.02    inference(flattening,[],[f20])).
% 2.38/1.02  
% 2.38/1.02  fof(f29,plain,(
% 2.38/1.02    ( ! [X0] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) => (~r1_ordinal1(X2,sK4(X2)) & r2_hidden(sK4(X2),X0) & v3_ordinal1(sK4(X2))))) )),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f28,plain,(
% 2.38/1.02    ? [X0,X1] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1)) => (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,sK2) & v3_ordinal1(X3)) | ~r2_hidden(X2,sK2) | ~v3_ordinal1(X2)) & k1_xboole_0 != sK2 & r1_tarski(sK2,sK3) & v3_ordinal1(sK3))),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f30,plain,(
% 2.38/1.02    ! [X2] : ((~r1_ordinal1(X2,sK4(X2)) & r2_hidden(sK4(X2),sK2) & v3_ordinal1(sK4(X2))) | ~r2_hidden(X2,sK2) | ~v3_ordinal1(X2)) & k1_xboole_0 != sK2 & r1_tarski(sK2,sK3) & v3_ordinal1(sK3)),
% 2.38/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f29,f28])).
% 2.38/1.02  
% 2.38/1.02  fof(f43,plain,(
% 2.38/1.02    r1_tarski(sK2,sK3)),
% 2.38/1.02    inference(cnf_transformation,[],[f30])).
% 2.38/1.02  
% 2.38/1.02  fof(f2,axiom,(
% 2.38/1.02    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f12,plain,(
% 2.38/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.38/1.02    inference(ennf_transformation,[],[f2])).
% 2.38/1.02  
% 2.38/1.02  fof(f13,plain,(
% 2.38/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.38/1.02    inference(flattening,[],[f12])).
% 2.38/1.02  
% 2.38/1.02  fof(f33,plain,(
% 2.38/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f13])).
% 2.38/1.02  
% 2.38/1.02  fof(f35,plain,(
% 2.38/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f25])).
% 2.38/1.02  
% 2.38/1.02  fof(f46,plain,(
% 2.38/1.02    ( ! [X2] : (r2_hidden(sK4(X2),sK2) | ~r2_hidden(X2,sK2) | ~v3_ordinal1(X2)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f30])).
% 2.38/1.02  
% 2.38/1.02  fof(f7,axiom,(
% 2.38/1.02    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f17,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.38/1.02    inference(ennf_transformation,[],[f7])).
% 2.38/1.02  
% 2.38/1.02  fof(f18,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.38/1.02    inference(flattening,[],[f17])).
% 2.38/1.02  
% 2.38/1.02  fof(f40,plain,(
% 2.38/1.02    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f18])).
% 2.38/1.02  
% 2.38/1.02  fof(f47,plain,(
% 2.38/1.02    ( ! [X2] : (~r1_ordinal1(X2,sK4(X2)) | ~r2_hidden(X2,sK2) | ~v3_ordinal1(X2)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f30])).
% 2.38/1.02  
% 2.38/1.02  fof(f45,plain,(
% 2.38/1.02    ( ! [X2] : (v3_ordinal1(sK4(X2)) | ~r2_hidden(X2,sK2) | ~v3_ordinal1(X2)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f30])).
% 2.38/1.02  
% 2.38/1.02  fof(f38,plain,(
% 2.38/1.02    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK1(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f27])).
% 2.38/1.02  
% 2.38/1.02  fof(f44,plain,(
% 2.38/1.02    k1_xboole_0 != sK2),
% 2.38/1.02    inference(cnf_transformation,[],[f30])).
% 2.38/1.02  
% 2.38/1.02  fof(f6,axiom,(
% 2.38/1.02    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f15,plain,(
% 2.38/1.02    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 2.38/1.02    inference(ennf_transformation,[],[f6])).
% 2.38/1.02  
% 2.38/1.02  fof(f16,plain,(
% 2.38/1.02    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 2.38/1.02    inference(flattening,[],[f15])).
% 2.38/1.02  
% 2.38/1.02  fof(f39,plain,(
% 2.38/1.02    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f16])).
% 2.38/1.02  
% 2.38/1.02  fof(f42,plain,(
% 2.38/1.02    v3_ordinal1(sK3)),
% 2.38/1.02    inference(cnf_transformation,[],[f30])).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1,plain,
% 2.38/1.02      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 2.38/1.02      inference(cnf_transformation,[],[f31]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_739,plain,
% 2.38/1.02      ( X0 = X1
% 2.38/1.02      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 2.38/1.02      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3,plain,
% 2.38/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f34]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_737,plain,
% 2.38/1.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_10,plain,
% 2.38/1.02      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_731,plain,
% 2.38/1.02      ( r1_tarski(X0,X1) != iProver_top
% 2.38/1.02      | r2_hidden(X1,X0) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1082,plain,
% 2.38/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_737,c_731]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1689,plain,
% 2.38/1.02      ( k1_xboole_0 = X0
% 2.38/1.02      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_739,c_1082]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_7,plain,
% 2.38/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(sK1(X1),X1) ),
% 2.38/1.02      inference(cnf_transformation,[],[f37]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_733,plain,
% 2.38/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.38/1.02      | r2_hidden(sK1(X1),X1) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2496,plain,
% 2.38/1.02      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_1689,c_733]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4,plain,
% 2.38/1.02      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 2.38/1.02      inference(cnf_transformation,[],[f36]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_736,plain,
% 2.38/1.02      ( r1_tarski(k1_tarski(X0),X1) = iProver_top
% 2.38/1.02      | r2_hidden(X0,X1) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_15,negated_conjecture,
% 2.38/1.02      ( r1_tarski(sK2,sK3) ),
% 2.38/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_728,plain,
% 2.38/1.02      ( r1_tarski(sK2,sK3) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2,plain,
% 2.38/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 2.38/1.02      inference(cnf_transformation,[],[f33]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_738,plain,
% 2.38/1.02      ( r1_tarski(X0,X1) != iProver_top
% 2.38/1.02      | r1_tarski(X2,X0) != iProver_top
% 2.38/1.02      | r1_tarski(X2,X1) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1660,plain,
% 2.38/1.02      ( r1_tarski(X0,sK3) = iProver_top
% 2.38/1.02      | r1_tarski(X0,sK2) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_728,c_738]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2091,plain,
% 2.38/1.02      ( r1_tarski(k1_tarski(X0),sK3) = iProver_top
% 2.38/1.02      | r2_hidden(X0,sK2) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_736,c_1660]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_5,plain,
% 2.38/1.02      ( ~ r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 2.38/1.02      inference(cnf_transformation,[],[f35]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_735,plain,
% 2.38/1.02      ( r1_tarski(k1_tarski(X0),X1) != iProver_top
% 2.38/1.02      | r2_hidden(X0,X1) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2276,plain,
% 2.38/1.02      ( r2_hidden(X0,sK3) = iProver_top
% 2.38/1.02      | r2_hidden(X0,sK2) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_2091,c_735]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3393,plain,
% 2.38/1.02      ( sK2 = k1_xboole_0 | r2_hidden(sK1(sK2),sK3) = iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_2496,c_2276]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_12,negated_conjecture,
% 2.38/1.02      ( ~ r2_hidden(X0,sK2)
% 2.38/1.02      | r2_hidden(sK4(X0),sK2)
% 2.38/1.02      | ~ v3_ordinal1(X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_730,plain,
% 2.38/1.02      ( r2_hidden(X0,sK2) != iProver_top
% 2.38/1.02      | r2_hidden(sK4(X0),sK2) = iProver_top
% 2.38/1.02      | v3_ordinal1(X0) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_9,plain,
% 2.38/1.02      ( r1_ordinal1(X0,X1)
% 2.38/1.02      | r2_hidden(X1,X0)
% 2.38/1.02      | ~ v3_ordinal1(X1)
% 2.38/1.02      | ~ v3_ordinal1(X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_11,negated_conjecture,
% 2.38/1.02      ( ~ r1_ordinal1(X0,sK4(X0))
% 2.38/1.02      | ~ r2_hidden(X0,sK2)
% 2.38/1.02      | ~ v3_ordinal1(X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_215,plain,
% 2.38/1.02      ( r2_hidden(X0,X1)
% 2.38/1.02      | ~ r2_hidden(X2,sK2)
% 2.38/1.02      | ~ v3_ordinal1(X0)
% 2.38/1.02      | ~ v3_ordinal1(X1)
% 2.38/1.02      | ~ v3_ordinal1(X2)
% 2.38/1.02      | X2 != X1
% 2.38/1.02      | sK4(X2) != X0 ),
% 2.38/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_11]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_216,plain,
% 2.38/1.02      ( ~ r2_hidden(X0,sK2)
% 2.38/1.02      | r2_hidden(sK4(X0),X0)
% 2.38/1.02      | ~ v3_ordinal1(X0)
% 2.38/1.02      | ~ v3_ordinal1(sK4(X0)) ),
% 2.38/1.02      inference(unflattening,[status(thm)],[c_215]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_13,negated_conjecture,
% 2.38/1.02      ( ~ r2_hidden(X0,sK2) | ~ v3_ordinal1(X0) | v3_ordinal1(sK4(X0)) ),
% 2.38/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_220,plain,
% 2.38/1.02      ( ~ v3_ordinal1(X0) | r2_hidden(sK4(X0),X0) | ~ r2_hidden(X0,sK2) ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_216,c_13]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_221,plain,
% 2.38/1.02      ( ~ r2_hidden(X0,sK2) | r2_hidden(sK4(X0),X0) | ~ v3_ordinal1(X0) ),
% 2.38/1.02      inference(renaming,[status(thm)],[c_220]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_726,plain,
% 2.38/1.02      ( r2_hidden(X0,sK2) != iProver_top
% 2.38/1.02      | r2_hidden(sK4(X0),X0) = iProver_top
% 2.38/1.02      | v3_ordinal1(X0) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_6,plain,
% 2.38/1.02      ( ~ r2_hidden(X0,X1)
% 2.38/1.02      | ~ r2_hidden(X2,X1)
% 2.38/1.02      | ~ r2_hidden(X2,sK1(X1)) ),
% 2.38/1.02      inference(cnf_transformation,[],[f38]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_734,plain,
% 2.38/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.38/1.02      | r2_hidden(X2,X1) != iProver_top
% 2.38/1.02      | r2_hidden(X2,sK1(X1)) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1947,plain,
% 2.38/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.38/1.02      | r2_hidden(sK4(sK1(X1)),X1) != iProver_top
% 2.38/1.02      | r2_hidden(sK1(X1),sK2) != iProver_top
% 2.38/1.02      | v3_ordinal1(sK1(X1)) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_726,c_734]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2334,plain,
% 2.38/1.02      ( r2_hidden(X0,sK2) != iProver_top
% 2.38/1.02      | r2_hidden(sK1(sK2),sK2) != iProver_top
% 2.38/1.02      | v3_ordinal1(sK1(sK2)) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_730,c_1947]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_14,negated_conjecture,
% 2.38/1.02      ( k1_xboole_0 != sK2 ),
% 2.38/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_888,plain,
% 2.38/1.02      ( r2_hidden(sK0(sK2,k1_xboole_0),sK2)
% 2.38/1.02      | r2_hidden(sK0(sK2,k1_xboole_0),k1_xboole_0)
% 2.38/1.02      | k1_xboole_0 = sK2 ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_889,plain,
% 2.38/1.02      ( k1_xboole_0 = sK2
% 2.38/1.02      | r2_hidden(sK0(sK2,k1_xboole_0),sK2) = iProver_top
% 2.38/1.02      | r2_hidden(sK0(sK2,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_888]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_951,plain,
% 2.38/1.02      ( ~ r2_hidden(sK0(sK2,k1_xboole_0),sK2) | r2_hidden(sK1(sK2),sK2) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_955,plain,
% 2.38/1.02      ( r2_hidden(sK0(sK2,k1_xboole_0),sK2) != iProver_top
% 2.38/1.02      | r2_hidden(sK1(sK2),sK2) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_951]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_863,plain,
% 2.38/1.02      ( ~ r1_tarski(k1_xboole_0,X0) | ~ r2_hidden(X0,k1_xboole_0) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1072,plain,
% 2.38/1.02      ( ~ r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0))
% 2.38/1.02      | ~ r2_hidden(sK0(sK2,k1_xboole_0),k1_xboole_0) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_863]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1073,plain,
% 2.38/1.02      ( r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0)) != iProver_top
% 2.38/1.02      | r2_hidden(sK0(sK2,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1072]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1245,plain,
% 2.38/1.02      ( r2_hidden(sK4(sK1(sK2)),sK2)
% 2.38/1.02      | ~ r2_hidden(sK1(sK2),sK2)
% 2.38/1.02      | ~ v3_ordinal1(sK1(sK2)) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1246,plain,
% 2.38/1.02      ( r2_hidden(sK4(sK1(sK2)),sK2) = iProver_top
% 2.38/1.02      | r2_hidden(sK1(sK2),sK2) != iProver_top
% 2.38/1.02      | v3_ordinal1(sK1(sK2)) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1245]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1243,plain,
% 2.38/1.02      ( r2_hidden(sK4(sK1(sK2)),sK1(sK2))
% 2.38/1.02      | ~ r2_hidden(sK1(sK2),sK2)
% 2.38/1.02      | ~ v3_ordinal1(sK1(sK2)) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_221]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1250,plain,
% 2.38/1.02      ( r2_hidden(sK4(sK1(sK2)),sK1(sK2)) = iProver_top
% 2.38/1.02      | r2_hidden(sK1(sK2),sK2) != iProver_top
% 2.38/1.02      | v3_ordinal1(sK1(sK2)) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1243]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1285,plain,
% 2.38/1.02      ( r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0)) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1286,plain,
% 2.38/1.02      ( r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0)) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1285]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_950,plain,
% 2.38/1.02      ( ~ r2_hidden(X0,sK1(sK2))
% 2.38/1.02      | ~ r2_hidden(X0,sK2)
% 2.38/1.02      | ~ r2_hidden(sK0(sK2,k1_xboole_0),sK2) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1826,plain,
% 2.38/1.02      ( ~ r2_hidden(sK0(sK2,k1_xboole_0),sK2)
% 2.38/1.02      | ~ r2_hidden(sK4(sK1(sK2)),sK1(sK2))
% 2.38/1.02      | ~ r2_hidden(sK4(sK1(sK2)),sK2) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_950]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1836,plain,
% 2.38/1.02      ( r2_hidden(sK0(sK2,k1_xboole_0),sK2) != iProver_top
% 2.38/1.02      | r2_hidden(sK4(sK1(sK2)),sK1(sK2)) != iProver_top
% 2.38/1.02      | r2_hidden(sK4(sK1(sK2)),sK2) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1826]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2339,plain,
% 2.38/1.02      ( v3_ordinal1(sK1(sK2)) != iProver_top ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_2334,c_14,c_889,c_955,c_1073,c_1246,c_1250,c_1286,
% 2.38/1.02                 c_1836]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_8,plain,
% 2.38/1.02      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_858,plain,
% 2.38/1.02      ( ~ r2_hidden(X0,sK3) | v3_ordinal1(X0) | ~ v3_ordinal1(sK3) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2175,plain,
% 2.38/1.02      ( ~ r2_hidden(sK1(sK2),sK3)
% 2.38/1.02      | v3_ordinal1(sK1(sK2))
% 2.38/1.02      | ~ v3_ordinal1(sK3) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_858]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2176,plain,
% 2.38/1.02      ( r2_hidden(sK1(sK2),sK3) != iProver_top
% 2.38/1.02      | v3_ordinal1(sK1(sK2)) = iProver_top
% 2.38/1.02      | v3_ordinal1(sK3) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_2175]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_372,plain,( X0 = X0 ),theory(equality) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1016,plain,
% 2.38/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_372]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_373,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_884,plain,
% 2.38/1.02      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_373]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1015,plain,
% 2.38/1.02      ( sK2 != k1_xboole_0
% 2.38/1.02      | k1_xboole_0 = sK2
% 2.38/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_884]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_16,negated_conjecture,
% 2.38/1.02      ( v3_ordinal1(sK3) ),
% 2.38/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_17,plain,
% 2.38/1.02      ( v3_ordinal1(sK3) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(contradiction,plain,
% 2.38/1.02      ( $false ),
% 2.38/1.02      inference(minisat,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_3393,c_2339,c_2176,c_1016,c_1015,c_14,c_17]) ).
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.38/1.02  
% 2.38/1.02  ------                               Statistics
% 2.38/1.02  
% 2.38/1.02  ------ General
% 2.38/1.02  
% 2.38/1.02  abstr_ref_over_cycles:                  0
% 2.38/1.02  abstr_ref_under_cycles:                 0
% 2.38/1.02  gc_basic_clause_elim:                   0
% 2.38/1.02  forced_gc_time:                         0
% 2.38/1.02  parsing_time:                           0.012
% 2.38/1.02  unif_index_cands_time:                  0.
% 2.38/1.02  unif_index_add_time:                    0.
% 2.38/1.02  orderings_time:                         0.
% 2.38/1.02  out_proof_time:                         0.011
% 2.38/1.02  total_time:                             0.135
% 2.38/1.02  num_of_symbols:                         42
% 2.38/1.02  num_of_terms:                           2269
% 2.38/1.02  
% 2.38/1.02  ------ Preprocessing
% 2.38/1.02  
% 2.38/1.02  num_of_splits:                          0
% 2.38/1.02  num_of_split_atoms:                     0
% 2.38/1.02  num_of_reused_defs:                     0
% 2.38/1.02  num_eq_ax_congr_red:                    16
% 2.38/1.02  num_of_sem_filtered_clauses:            1
% 2.38/1.02  num_of_subtypes:                        0
% 2.38/1.02  monotx_restored_types:                  0
% 2.38/1.02  sat_num_of_epr_types:                   0
% 2.38/1.02  sat_num_of_non_cyclic_types:            0
% 2.38/1.02  sat_guarded_non_collapsed_types:        0
% 2.38/1.02  num_pure_diseq_elim:                    0
% 2.38/1.02  simp_replaced_by:                       0
% 2.38/1.02  res_preprocessed:                       76
% 2.38/1.02  prep_upred:                             0
% 2.38/1.02  prep_unflattend:                        2
% 2.38/1.02  smt_new_axioms:                         0
% 2.38/1.02  pred_elim_cands:                        3
% 2.38/1.02  pred_elim:                              1
% 2.38/1.02  pred_elim_cl:                           1
% 2.38/1.02  pred_elim_cycles:                       3
% 2.38/1.02  merged_defs:                            8
% 2.38/1.02  merged_defs_ncl:                        0
% 2.38/1.02  bin_hyper_res:                          8
% 2.38/1.02  prep_cycles:                            4
% 2.38/1.02  pred_elim_time:                         0.001
% 2.38/1.02  splitting_time:                         0.
% 2.38/1.02  sem_filter_time:                        0.
% 2.38/1.02  monotx_time:                            0.
% 2.38/1.02  subtype_inf_time:                       0.
% 2.38/1.02  
% 2.38/1.02  ------ Problem properties
% 2.38/1.02  
% 2.38/1.02  clauses:                                16
% 2.38/1.02  conjectures:                            5
% 2.38/1.02  epr:                                    7
% 2.38/1.02  horn:                                   15
% 2.38/1.02  ground:                                 3
% 2.38/1.02  unary:                                  4
% 2.38/1.02  binary:                                 4
% 2.38/1.02  lits:                                   36
% 2.38/1.02  lits_eq:                                3
% 2.38/1.02  fd_pure:                                0
% 2.38/1.02  fd_pseudo:                              0
% 2.38/1.02  fd_cond:                                0
% 2.38/1.02  fd_pseudo_cond:                         2
% 2.38/1.02  ac_symbols:                             0
% 2.38/1.02  
% 2.38/1.02  ------ Propositional Solver
% 2.38/1.02  
% 2.38/1.02  prop_solver_calls:                      26
% 2.38/1.02  prop_fast_solver_calls:                 518
% 2.38/1.02  smt_solver_calls:                       0
% 2.38/1.02  smt_fast_solver_calls:                  0
% 2.38/1.02  prop_num_of_clauses:                    1171
% 2.38/1.02  prop_preprocess_simplified:             3605
% 2.38/1.02  prop_fo_subsumed:                       13
% 2.38/1.02  prop_solver_time:                       0.
% 2.38/1.02  smt_solver_time:                        0.
% 2.38/1.02  smt_fast_solver_time:                   0.
% 2.38/1.02  prop_fast_solver_time:                  0.
% 2.38/1.02  prop_unsat_core_time:                   0.
% 2.38/1.02  
% 2.38/1.02  ------ QBF
% 2.38/1.02  
% 2.38/1.02  qbf_q_res:                              0
% 2.38/1.02  qbf_num_tautologies:                    0
% 2.38/1.02  qbf_prep_cycles:                        0
% 2.38/1.02  
% 2.38/1.02  ------ BMC1
% 2.38/1.02  
% 2.38/1.02  bmc1_current_bound:                     -1
% 2.38/1.02  bmc1_last_solved_bound:                 -1
% 2.38/1.02  bmc1_unsat_core_size:                   -1
% 2.38/1.02  bmc1_unsat_core_parents_size:           -1
% 2.38/1.02  bmc1_merge_next_fun:                    0
% 2.38/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.38/1.02  
% 2.38/1.02  ------ Instantiation
% 2.38/1.02  
% 2.38/1.02  inst_num_of_clauses:                    348
% 2.38/1.02  inst_num_in_passive:                    2
% 2.38/1.02  inst_num_in_active:                     187
% 2.38/1.02  inst_num_in_unprocessed:                160
% 2.38/1.02  inst_num_of_loops:                      240
% 2.38/1.02  inst_num_of_learning_restarts:          0
% 2.38/1.02  inst_num_moves_active_passive:          50
% 2.38/1.02  inst_lit_activity:                      0
% 2.38/1.02  inst_lit_activity_moves:                0
% 2.38/1.02  inst_num_tautologies:                   0
% 2.38/1.02  inst_num_prop_implied:                  0
% 2.38/1.02  inst_num_existing_simplified:           0
% 2.38/1.02  inst_num_eq_res_simplified:             0
% 2.38/1.02  inst_num_child_elim:                    0
% 2.38/1.02  inst_num_of_dismatching_blockings:      90
% 2.38/1.02  inst_num_of_non_proper_insts:           296
% 2.38/1.02  inst_num_of_duplicates:                 0
% 2.38/1.02  inst_inst_num_from_inst_to_res:         0
% 2.38/1.02  inst_dismatching_checking_time:         0.
% 2.38/1.02  
% 2.38/1.02  ------ Resolution
% 2.38/1.02  
% 2.38/1.02  res_num_of_clauses:                     0
% 2.38/1.02  res_num_in_passive:                     0
% 2.38/1.02  res_num_in_active:                      0
% 2.38/1.02  res_num_of_loops:                       80
% 2.38/1.02  res_forward_subset_subsumed:            47
% 2.38/1.02  res_backward_subset_subsumed:           2
% 2.38/1.02  res_forward_subsumed:                   0
% 2.38/1.02  res_backward_subsumed:                  0
% 2.38/1.02  res_forward_subsumption_resolution:     0
% 2.38/1.02  res_backward_subsumption_resolution:    0
% 2.38/1.02  res_clause_to_clause_subsumption:       298
% 2.38/1.02  res_orphan_elimination:                 0
% 2.38/1.02  res_tautology_del:                      40
% 2.38/1.02  res_num_eq_res_simplified:              0
% 2.38/1.02  res_num_sel_changes:                    0
% 2.38/1.02  res_moves_from_active_to_pass:          0
% 2.38/1.02  
% 2.38/1.02  ------ Superposition
% 2.38/1.02  
% 2.38/1.02  sup_time_total:                         0.
% 2.38/1.02  sup_time_generating:                    0.
% 2.38/1.02  sup_time_sim_full:                      0.
% 2.38/1.02  sup_time_sim_immed:                     0.
% 2.38/1.02  
% 2.38/1.02  sup_num_of_clauses:                     90
% 2.38/1.02  sup_num_in_active:                      47
% 2.38/1.02  sup_num_in_passive:                     43
% 2.38/1.02  sup_num_of_loops:                       46
% 2.38/1.02  sup_fw_superposition:                   45
% 2.38/1.02  sup_bw_superposition:                   71
% 2.38/1.02  sup_immediate_simplified:               10
% 2.38/1.02  sup_given_eliminated:                   0
% 2.38/1.02  comparisons_done:                       0
% 2.38/1.02  comparisons_avoided:                    0
% 2.38/1.02  
% 2.38/1.02  ------ Simplifications
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  sim_fw_subset_subsumed:                 4
% 2.38/1.02  sim_bw_subset_subsumed:                 0
% 2.38/1.02  sim_fw_subsumed:                        4
% 2.38/1.02  sim_bw_subsumed:                        2
% 2.38/1.02  sim_fw_subsumption_res:                 0
% 2.38/1.02  sim_bw_subsumption_res:                 0
% 2.38/1.02  sim_tautology_del:                      5
% 2.38/1.02  sim_eq_tautology_del:                   10
% 2.38/1.02  sim_eq_res_simp:                        0
% 2.38/1.02  sim_fw_demodulated:                     0
% 2.38/1.02  sim_bw_demodulated:                     0
% 2.38/1.02  sim_light_normalised:                   0
% 2.38/1.02  sim_joinable_taut:                      0
% 2.38/1.02  sim_joinable_simp:                      0
% 2.38/1.02  sim_ac_normalised:                      0
% 2.38/1.02  sim_smt_subsumption:                    0
% 2.38/1.02  
%------------------------------------------------------------------------------
