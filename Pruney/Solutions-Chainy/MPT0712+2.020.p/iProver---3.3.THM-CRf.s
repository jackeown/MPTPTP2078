%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:48 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 355 expanded)
%              Number of clauses        :   50 (  99 expanded)
%              Number of leaves         :   14 (  84 expanded)
%              Depth                    :   20
%              Number of atoms          :  233 ( 829 expanded)
%              Number of equality atoms :  109 ( 325 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).

fof(f40,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f42])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f38,f42,f42])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f42])).

fof(f46,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f41,f43,f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f10,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_387,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_392,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_390,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1625,plain,
    ( k7_relat_1(X0,k2_enumset1(X1,X1,X1,X2)) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | r2_hidden(X2,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_392,c_390])).

cnf(c_2369,plain,
    ( k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1625])).

cnf(c_2371,plain,
    ( k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2369])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_389,plain,
    ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X2)) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2466,plain,
    ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X2)) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X2))
    | k7_relat_1(X0,k2_enumset1(X2,X2,X2,X2)) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2371,c_389])).

cnf(c_2981,plain,
    ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X2)) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X2))
    | k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
    | k7_relat_1(X0,k2_enumset1(X2,X2,X2,X2)) = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2371,c_2466])).

cnf(c_3541,plain,
    ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
    | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
    | k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_387,c_2981])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3542,plain,
    ( ~ v1_relat_1(sK1)
    | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
    | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
    | k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3541])).

cnf(c_3703,plain,
    ( k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
    | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
    | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3541,c_13,c_3542])).

cnf(c_3704,plain,
    ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
    | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
    | k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3703])).

cnf(c_386,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_391,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_956,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_386,c_391])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_388,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1049,plain,
    ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_956,c_388])).

cnf(c_3714,plain,
    ( k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3704,c_1049])).

cnf(c_516,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | ~ r2_hidden(X1,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_518,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_491,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_616,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_623,plain,
    ( r2_hidden(X0,k1_relat_1(sK1))
    | r2_hidden(X1,k1_relat_1(sK1))
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_625,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_168,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_511,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X1
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X0 ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_615,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X0
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_762,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_763,plain,
    ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1011,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1013,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_3775,plain,
    ( k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3714,c_13,c_12,c_11,c_518,c_616,c_625,c_762,c_763,c_1013])).

cnf(c_3778,plain,
    ( k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3775,c_956])).

cnf(c_9,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_568,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_7])).

cnf(c_3779,plain,
    ( k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3778,c_568])).

cnf(c_4985,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3779,c_1049])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_393,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5598,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4985,c_393])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:24:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.23/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.23/0.99  
% 3.23/0.99  ------  iProver source info
% 3.23/0.99  
% 3.23/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.23/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.23/0.99  git: non_committed_changes: false
% 3.23/0.99  git: last_make_outside_of_git: false
% 3.23/0.99  
% 3.23/0.99  ------ 
% 3.23/0.99  ------ Parsing...
% 3.23/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.23/0.99  ------ Proving...
% 3.23/0.99  ------ Problem Properties 
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  clauses                                 13
% 3.23/0.99  conjectures                             3
% 3.23/0.99  EPR                                     5
% 3.23/0.99  Horn                                    12
% 3.23/0.99  unary                                   8
% 3.23/0.99  binary                                  1
% 3.23/0.99  lits                                    24
% 3.23/0.99  lits eq                                 7
% 3.23/0.99  fd_pure                                 0
% 3.23/0.99  fd_pseudo                               0
% 3.23/0.99  fd_cond                                 0
% 3.23/0.99  fd_pseudo_cond                          1
% 3.23/0.99  AC symbols                              0
% 3.23/0.99  
% 3.23/0.99  ------ Input Options Time Limit: Unbounded
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  ------ 
% 3.23/0.99  Current options:
% 3.23/0.99  ------ 
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  ------ Proving...
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  % SZS status Theorem for theBenchmark.p
% 3.23/0.99  
% 3.23/0.99   Resolution empty clause
% 3.23/0.99  
% 3.23/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  fof(f12,conjecture,(
% 3.23/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f13,negated_conjecture,(
% 3.23/0.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 3.23/0.99    inference(negated_conjecture,[],[f12])).
% 3.23/0.99  
% 3.23/0.99  fof(f19,plain,(
% 3.23/0.99    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.23/0.99    inference(ennf_transformation,[],[f13])).
% 3.23/0.99  
% 3.23/0.99  fof(f20,plain,(
% 3.23/0.99    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.23/0.99    inference(flattening,[],[f19])).
% 3.23/0.99  
% 3.23/0.99  fof(f23,plain,(
% 3.23/0.99    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 3.23/0.99    introduced(choice_axiom,[])).
% 3.23/0.99  
% 3.23/0.99  fof(f24,plain,(
% 3.23/0.99    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 3.23/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).
% 3.23/0.99  
% 3.23/0.99  fof(f40,plain,(
% 3.23/0.99    v1_funct_1(sK1)),
% 3.23/0.99    inference(cnf_transformation,[],[f24])).
% 3.23/0.99  
% 3.23/0.99  fof(f6,axiom,(
% 3.23/0.99    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f14,plain,(
% 3.23/0.99    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 3.23/0.99    inference(ennf_transformation,[],[f6])).
% 3.23/0.99  
% 3.23/0.99  fof(f32,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f14])).
% 3.23/0.99  
% 3.23/0.99  fof(f4,axiom,(
% 3.23/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f30,plain,(
% 3.23/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f4])).
% 3.23/0.99  
% 3.23/0.99  fof(f5,axiom,(
% 3.23/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f31,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f5])).
% 3.23/0.99  
% 3.23/0.99  fof(f42,plain,(
% 3.23/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.23/0.99    inference(definition_unfolding,[],[f30,f31])).
% 3.23/0.99  
% 3.23/0.99  fof(f44,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 3.23/0.99    inference(definition_unfolding,[],[f32,f42])).
% 3.23/0.99  
% 3.23/0.99  fof(f8,axiom,(
% 3.23/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f16,plain,(
% 3.23/0.99    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.23/0.99    inference(ennf_transformation,[],[f8])).
% 3.23/0.99  
% 3.23/0.99  fof(f34,plain,(
% 3.23/0.99    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f16])).
% 3.23/0.99  
% 3.23/0.99  fof(f11,axiom,(
% 3.23/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f17,plain,(
% 3.23/0.99    ! [X0,X1,X2] : ((k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.23/0.99    inference(ennf_transformation,[],[f11])).
% 3.23/0.99  
% 3.23/0.99  fof(f18,plain,(
% 3.23/0.99    ! [X0,X1,X2] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.23/0.99    inference(flattening,[],[f17])).
% 3.23/0.99  
% 3.23/0.99  fof(f38,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f18])).
% 3.23/0.99  
% 3.23/0.99  fof(f45,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.23/0.99    inference(definition_unfolding,[],[f38,f42,f42])).
% 3.23/0.99  
% 3.23/0.99  fof(f39,plain,(
% 3.23/0.99    v1_relat_1(sK1)),
% 3.23/0.99    inference(cnf_transformation,[],[f24])).
% 3.23/0.99  
% 3.23/0.99  fof(f7,axiom,(
% 3.23/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f15,plain,(
% 3.23/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.23/0.99    inference(ennf_transformation,[],[f7])).
% 3.23/0.99  
% 3.23/0.99  fof(f33,plain,(
% 3.23/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f15])).
% 3.23/0.99  
% 3.23/0.99  fof(f41,plain,(
% 3.23/0.99    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 3.23/0.99    inference(cnf_transformation,[],[f24])).
% 3.23/0.99  
% 3.23/0.99  fof(f3,axiom,(
% 3.23/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f29,plain,(
% 3.23/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f3])).
% 3.23/0.99  
% 3.23/0.99  fof(f43,plain,(
% 3.23/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.23/0.99    inference(definition_unfolding,[],[f29,f42])).
% 3.23/0.99  
% 3.23/0.99  fof(f46,plain,(
% 3.23/0.99    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 3.23/0.99    inference(definition_unfolding,[],[f41,f43,f43])).
% 3.23/0.99  
% 3.23/0.99  fof(f1,axiom,(
% 3.23/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f21,plain,(
% 3.23/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.23/0.99    inference(nnf_transformation,[],[f1])).
% 3.23/0.99  
% 3.23/0.99  fof(f22,plain,(
% 3.23/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.23/0.99    inference(flattening,[],[f21])).
% 3.23/0.99  
% 3.23/0.99  fof(f25,plain,(
% 3.23/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.23/0.99    inference(cnf_transformation,[],[f22])).
% 3.23/0.99  
% 3.23/0.99  fof(f48,plain,(
% 3.23/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.23/0.99    inference(equality_resolution,[],[f25])).
% 3.23/0.99  
% 3.23/0.99  fof(f10,axiom,(
% 3.23/0.99    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f37,plain,(
% 3.23/0.99    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.23/0.99    inference(cnf_transformation,[],[f10])).
% 3.23/0.99  
% 3.23/0.99  fof(f9,axiom,(
% 3.23/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f36,plain,(
% 3.23/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.23/0.99    inference(cnf_transformation,[],[f9])).
% 3.23/0.99  
% 3.23/0.99  fof(f2,axiom,(
% 3.23/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f28,plain,(
% 3.23/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f2])).
% 3.23/0.99  
% 3.23/0.99  cnf(c_12,negated_conjecture,
% 3.23/0.99      ( v1_funct_1(sK1) ),
% 3.23/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_387,plain,
% 3.23/0.99      ( v1_funct_1(sK1) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4,plain,
% 3.23/0.99      ( r2_hidden(X0,X1)
% 3.23/0.99      | r2_hidden(X2,X1)
% 3.23/0.99      | r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) ),
% 3.23/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_392,plain,
% 3.23/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.23/0.99      | r2_hidden(X2,X1) = iProver_top
% 3.23/0.99      | r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_6,plain,
% 3.23/0.99      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 3.23/0.99      | ~ v1_relat_1(X1)
% 3.23/0.99      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 3.23/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_390,plain,
% 3.23/0.99      ( k7_relat_1(X0,X1) = k1_xboole_0
% 3.23/0.99      | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
% 3.23/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1625,plain,
% 3.23/0.99      ( k7_relat_1(X0,k2_enumset1(X1,X1,X1,X2)) = k1_xboole_0
% 3.23/0.99      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 3.23/0.99      | r2_hidden(X2,k1_relat_1(X0)) = iProver_top
% 3.23/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_392,c_390]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2369,plain,
% 3.23/0.99      ( k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
% 3.23/0.99      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 3.23/0.99      | v1_relat_1(X0) != iProver_top
% 3.23/0.99      | iProver_top != iProver_top ),
% 3.23/0.99      inference(equality_factoring,[status(thm)],[c_1625]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2371,plain,
% 3.23/0.99      ( k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
% 3.23/0.99      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 3.23/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.23/0.99      inference(equality_resolution_simp,[status(thm)],[c_2369]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_10,plain,
% 3.23/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.23/0.99      | ~ r2_hidden(X2,k1_relat_1(X1))
% 3.23/0.99      | ~ v1_funct_1(X1)
% 3.23/0.99      | ~ v1_relat_1(X1)
% 3.23/0.99      | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0)) ),
% 3.23/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_389,plain,
% 3.23/0.99      ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X2)) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X2))
% 3.23/0.99      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 3.23/0.99      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.23/0.99      | v1_funct_1(X0) != iProver_top
% 3.23/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2466,plain,
% 3.23/0.99      ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X2)) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X2))
% 3.23/0.99      | k7_relat_1(X0,k2_enumset1(X2,X2,X2,X2)) = k1_xboole_0
% 3.23/0.99      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.23/0.99      | v1_funct_1(X0) != iProver_top
% 3.23/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_2371,c_389]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2981,plain,
% 3.23/0.99      ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X2)) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X2))
% 3.23/0.99      | k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
% 3.23/0.99      | k7_relat_1(X0,k2_enumset1(X2,X2,X2,X2)) = k1_xboole_0
% 3.23/0.99      | v1_funct_1(X0) != iProver_top
% 3.23/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_2371,c_2466]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3541,plain,
% 3.23/0.99      ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
% 3.23/0.99      | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
% 3.23/0.99      | k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
% 3.23/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_387,c_2981]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_13,negated_conjecture,
% 3.23/0.99      ( v1_relat_1(sK1) ),
% 3.23/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3542,plain,
% 3.23/0.99      ( ~ v1_relat_1(sK1)
% 3.23/0.99      | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
% 3.23/0.99      | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
% 3.23/0.99      | k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0 ),
% 3.23/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3541]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3703,plain,
% 3.23/0.99      ( k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
% 3.23/0.99      | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
% 3.23/0.99      | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_3541,c_13,c_3542]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3704,plain,
% 3.23/0.99      ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
% 3.23/0.99      | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
% 3.23/0.99      | k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0 ),
% 3.23/0.99      inference(renaming,[status(thm)],[c_3703]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_386,plain,
% 3.23/0.99      ( v1_relat_1(sK1) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5,plain,
% 3.23/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.23/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_391,plain,
% 3.23/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.23/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_956,plain,
% 3.23/0.99      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_386,c_391]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_11,negated_conjecture,
% 3.23/0.99      ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
% 3.23/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_388,plain,
% 3.23/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1049,plain,
% 3.23/0.99      ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_956,c_388]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3714,plain,
% 3.23/0.99      ( k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
% 3.23/0.99      | r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_3704,c_1049]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_516,plain,
% 3.23/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK1))
% 3.23/0.99      | ~ r2_hidden(X1,k1_relat_1(sK1))
% 3.23/0.99      | ~ v1_funct_1(sK1)
% 3.23/0.99      | ~ v1_relat_1(sK1)
% 3.23/0.99      | k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_518,plain,
% 3.23/0.99      ( ~ r2_hidden(sK0,k1_relat_1(sK1))
% 3.23/0.99      | ~ v1_funct_1(sK1)
% 3.23/0.99      | ~ v1_relat_1(sK1)
% 3.23/0.99      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_516]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_491,plain,
% 3.23/0.99      ( ~ v1_relat_1(sK1)
% 3.23/0.99      | k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_616,plain,
% 3.23/0.99      ( ~ v1_relat_1(sK1)
% 3.23/0.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_491]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_623,plain,
% 3.23/0.99      ( r2_hidden(X0,k1_relat_1(sK1))
% 3.23/0.99      | r2_hidden(X1,k1_relat_1(sK1))
% 3.23/0.99      | r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_relat_1(sK1)) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_625,plain,
% 3.23/0.99      ( r2_hidden(sK0,k1_relat_1(sK1))
% 3.23/0.99      | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_623]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_168,plain,
% 3.23/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.23/0.99      theory(equality) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_511,plain,
% 3.23/0.99      ( ~ r1_tarski(X0,X1)
% 3.23/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 3.23/0.99      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X1
% 3.23/0.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X0 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_168]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_615,plain,
% 3.23/0.99      ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
% 3.23/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 3.23/0.99      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X0
% 3.23/0.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_511]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_762,plain,
% 3.23/0.99      ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 3.23/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 3.23/0.99      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 3.23/0.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_615]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f48]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_763,plain,
% 3.23/0.99      ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1011,plain,
% 3.23/0.99      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_relat_1(sK1))
% 3.23/0.99      | ~ v1_relat_1(sK1)
% 3.23/0.99      | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1013,plain,
% 3.23/0.99      ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1))
% 3.23/0.99      | ~ v1_relat_1(sK1)
% 3.23/0.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_1011]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3775,plain,
% 3.23/0.99      ( k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_3714,c_13,c_12,c_11,c_518,c_616,c_625,c_762,c_763,c_1013]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3778,plain,
% 3.23/0.99      ( k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(k1_xboole_0) ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_3775,c_956]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_9,plain,
% 3.23/0.99      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.23/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_7,plain,
% 3.23/0.99      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.23/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_568,plain,
% 3.23/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_9,c_7]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3779,plain,
% 3.23/0.99      ( k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 3.23/0.99      inference(light_normalisation,[status(thm)],[c_3778,c_568]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4985,plain,
% 3.23/0.99      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_3779,c_1049]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3,plain,
% 3.23/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_393,plain,
% 3.23/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5598,plain,
% 3.23/0.99      ( $false ),
% 3.23/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_4985,c_393]) ).
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  ------                               Statistics
% 3.23/0.99  
% 3.23/0.99  ------ Selected
% 3.23/0.99  
% 3.23/0.99  total_time:                             0.165
% 3.23/0.99  
%------------------------------------------------------------------------------
