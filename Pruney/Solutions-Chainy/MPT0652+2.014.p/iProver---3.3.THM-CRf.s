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
% DateTime   : Thu Dec  3 11:50:35 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 284 expanded)
%              Number of clauses        :   60 (  90 expanded)
%              Number of leaves         :   12 (  57 expanded)
%              Depth                    :   16
%              Number of atoms          :  302 (1141 expanded)
%              Number of equality atoms :  160 ( 477 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f24,plain,
    ( ? [X0] :
        ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
        | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f24])).

fof(f40,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f43,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_483,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_179,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_180,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_179])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_25,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_182,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_180,c_17,c_16,c_15,c_25])).

cnf(c_5,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k2_relat_1(X1) != k2_relat_1(X2)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(k5_relat_1(X2,X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_491,plain,
    ( k2_relat_1(X0) != k2_relat_1(X1)
    | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1811,plain,
    ( k2_relat_1(X0) != X1
    | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_491])).

cnf(c_11,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_485,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2188,plain,
    ( k2_relat_1(X0) != X1
    | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1811,c_485])).

cnf(c_2193,plain,
    ( k1_relat_1(sK0) != X0
    | k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_182,c_2188])).

cnf(c_18,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_33,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_35,plain,
    ( v1_funct_1(sK0) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_2843,plain,
    ( v1_relat_1(X1) != iProver_top
    | k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
    | k1_relat_1(sK0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2193,c_18,c_19,c_35])).

cnf(c_2844,plain,
    ( k1_relat_1(sK0) != X0
    | k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2843])).

cnf(c_2852,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2844])).

cnf(c_3708,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(superposition,[status(thm)],[c_483,c_2852])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_489,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_995,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_483,c_489])).

cnf(c_3710,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_3708,c_995])).

cnf(c_269,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_638,plain,
    ( X0 != X1
    | k2_relat_1(sK0) != X1
    | k2_relat_1(sK0) = X0 ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_677,plain,
    ( X0 != k2_relat_1(X1)
    | k2_relat_1(sK0) = X0
    | k2_relat_1(sK0) != k2_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_798,plain,
    ( k2_relat_1(X0) != k2_relat_1(X1)
    | k2_relat_1(sK0) != k2_relat_1(X1)
    | k2_relat_1(sK0) = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_1732,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(X0)
    | k2_relat_1(sK0) != k2_relat_1(X0)
    | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_1734,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)
    | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_1732])).

cnf(c_4,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_490,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1477,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k1_relat_1(k2_funct_1(sK0))
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_182,c_490])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_171,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_172,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_171])).

cnf(c_22,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_174,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_172,c_17,c_16,c_15,c_22])).

cnf(c_1500,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k2_relat_1(sK0)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1477,c_174])).

cnf(c_1521,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1500])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_751,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_754,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_591,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != X0
    | k2_relat_1(sK0) != X0
    | k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_634,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(X0)
    | k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_591])).

cnf(c_636,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_272,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_280,plain,
    ( k2_relat_1(sK0) = k2_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_55,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_51,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_14,negated_conjecture,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3710,c_1734,c_1521,c_754,c_636,c_280,c_55,c_51,c_35,c_14,c_19,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.34/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.01  
% 2.34/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.34/1.01  
% 2.34/1.01  ------  iProver source info
% 2.34/1.01  
% 2.34/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.34/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.34/1.01  git: non_committed_changes: false
% 2.34/1.01  git: last_make_outside_of_git: false
% 2.34/1.01  
% 2.34/1.01  ------ 
% 2.34/1.01  
% 2.34/1.01  ------ Input Options
% 2.34/1.01  
% 2.34/1.01  --out_options                           all
% 2.34/1.01  --tptp_safe_out                         true
% 2.34/1.01  --problem_path                          ""
% 2.34/1.01  --include_path                          ""
% 2.34/1.01  --clausifier                            res/vclausify_rel
% 2.34/1.01  --clausifier_options                    --mode clausify
% 2.34/1.01  --stdin                                 false
% 2.34/1.01  --stats_out                             all
% 2.34/1.01  
% 2.34/1.01  ------ General Options
% 2.34/1.01  
% 2.34/1.01  --fof                                   false
% 2.34/1.01  --time_out_real                         305.
% 2.34/1.01  --time_out_virtual                      -1.
% 2.34/1.01  --symbol_type_check                     false
% 2.34/1.01  --clausify_out                          false
% 2.34/1.01  --sig_cnt_out                           false
% 2.34/1.01  --trig_cnt_out                          false
% 2.34/1.01  --trig_cnt_out_tolerance                1.
% 2.34/1.01  --trig_cnt_out_sk_spl                   false
% 2.34/1.01  --abstr_cl_out                          false
% 2.34/1.01  
% 2.34/1.01  ------ Global Options
% 2.34/1.01  
% 2.34/1.01  --schedule                              default
% 2.34/1.01  --add_important_lit                     false
% 2.34/1.01  --prop_solver_per_cl                    1000
% 2.34/1.01  --min_unsat_core                        false
% 2.34/1.01  --soft_assumptions                      false
% 2.34/1.01  --soft_lemma_size                       3
% 2.34/1.01  --prop_impl_unit_size                   0
% 2.34/1.01  --prop_impl_unit                        []
% 2.34/1.01  --share_sel_clauses                     true
% 2.34/1.01  --reset_solvers                         false
% 2.34/1.01  --bc_imp_inh                            [conj_cone]
% 2.34/1.01  --conj_cone_tolerance                   3.
% 2.34/1.01  --extra_neg_conj                        none
% 2.34/1.01  --large_theory_mode                     true
% 2.34/1.01  --prolific_symb_bound                   200
% 2.34/1.01  --lt_threshold                          2000
% 2.34/1.01  --clause_weak_htbl                      true
% 2.34/1.01  --gc_record_bc_elim                     false
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing Options
% 2.34/1.01  
% 2.34/1.01  --preprocessing_flag                    true
% 2.34/1.01  --time_out_prep_mult                    0.1
% 2.34/1.01  --splitting_mode                        input
% 2.34/1.01  --splitting_grd                         true
% 2.34/1.01  --splitting_cvd                         false
% 2.34/1.01  --splitting_cvd_svl                     false
% 2.34/1.01  --splitting_nvd                         32
% 2.34/1.01  --sub_typing                            true
% 2.34/1.01  --prep_gs_sim                           true
% 2.34/1.01  --prep_unflatten                        true
% 2.34/1.01  --prep_res_sim                          true
% 2.34/1.01  --prep_upred                            true
% 2.34/1.01  --prep_sem_filter                       exhaustive
% 2.34/1.01  --prep_sem_filter_out                   false
% 2.34/1.01  --pred_elim                             true
% 2.34/1.01  --res_sim_input                         true
% 2.34/1.01  --eq_ax_congr_red                       true
% 2.34/1.01  --pure_diseq_elim                       true
% 2.34/1.01  --brand_transform                       false
% 2.34/1.01  --non_eq_to_eq                          false
% 2.34/1.01  --prep_def_merge                        true
% 2.34/1.01  --prep_def_merge_prop_impl              false
% 2.34/1.01  --prep_def_merge_mbd                    true
% 2.34/1.01  --prep_def_merge_tr_red                 false
% 2.34/1.01  --prep_def_merge_tr_cl                  false
% 2.34/1.01  --smt_preprocessing                     true
% 2.34/1.01  --smt_ac_axioms                         fast
% 2.34/1.01  --preprocessed_out                      false
% 2.34/1.01  --preprocessed_stats                    false
% 2.34/1.01  
% 2.34/1.01  ------ Abstraction refinement Options
% 2.34/1.01  
% 2.34/1.01  --abstr_ref                             []
% 2.34/1.01  --abstr_ref_prep                        false
% 2.34/1.01  --abstr_ref_until_sat                   false
% 2.34/1.01  --abstr_ref_sig_restrict                funpre
% 2.34/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/1.01  --abstr_ref_under                       []
% 2.34/1.01  
% 2.34/1.01  ------ SAT Options
% 2.34/1.01  
% 2.34/1.01  --sat_mode                              false
% 2.34/1.01  --sat_fm_restart_options                ""
% 2.34/1.01  --sat_gr_def                            false
% 2.34/1.01  --sat_epr_types                         true
% 2.34/1.01  --sat_non_cyclic_types                  false
% 2.34/1.01  --sat_finite_models                     false
% 2.34/1.01  --sat_fm_lemmas                         false
% 2.34/1.01  --sat_fm_prep                           false
% 2.34/1.01  --sat_fm_uc_incr                        true
% 2.34/1.01  --sat_out_model                         small
% 2.34/1.01  --sat_out_clauses                       false
% 2.34/1.01  
% 2.34/1.01  ------ QBF Options
% 2.34/1.01  
% 2.34/1.01  --qbf_mode                              false
% 2.34/1.01  --qbf_elim_univ                         false
% 2.34/1.01  --qbf_dom_inst                          none
% 2.34/1.01  --qbf_dom_pre_inst                      false
% 2.34/1.01  --qbf_sk_in                             false
% 2.34/1.01  --qbf_pred_elim                         true
% 2.34/1.01  --qbf_split                             512
% 2.34/1.01  
% 2.34/1.01  ------ BMC1 Options
% 2.34/1.01  
% 2.34/1.01  --bmc1_incremental                      false
% 2.34/1.01  --bmc1_axioms                           reachable_all
% 2.34/1.01  --bmc1_min_bound                        0
% 2.34/1.01  --bmc1_max_bound                        -1
% 2.34/1.01  --bmc1_max_bound_default                -1
% 2.34/1.01  --bmc1_symbol_reachability              true
% 2.34/1.01  --bmc1_property_lemmas                  false
% 2.34/1.01  --bmc1_k_induction                      false
% 2.34/1.01  --bmc1_non_equiv_states                 false
% 2.34/1.01  --bmc1_deadlock                         false
% 2.34/1.01  --bmc1_ucm                              false
% 2.34/1.01  --bmc1_add_unsat_core                   none
% 2.34/1.01  --bmc1_unsat_core_children              false
% 2.34/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/1.01  --bmc1_out_stat                         full
% 2.34/1.01  --bmc1_ground_init                      false
% 2.34/1.01  --bmc1_pre_inst_next_state              false
% 2.34/1.01  --bmc1_pre_inst_state                   false
% 2.34/1.01  --bmc1_pre_inst_reach_state             false
% 2.34/1.01  --bmc1_out_unsat_core                   false
% 2.34/1.01  --bmc1_aig_witness_out                  false
% 2.34/1.01  --bmc1_verbose                          false
% 2.34/1.01  --bmc1_dump_clauses_tptp                false
% 2.34/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.34/1.01  --bmc1_dump_file                        -
% 2.34/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.34/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.34/1.01  --bmc1_ucm_extend_mode                  1
% 2.34/1.01  --bmc1_ucm_init_mode                    2
% 2.34/1.01  --bmc1_ucm_cone_mode                    none
% 2.34/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.34/1.01  --bmc1_ucm_relax_model                  4
% 2.34/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.34/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/1.01  --bmc1_ucm_layered_model                none
% 2.34/1.01  --bmc1_ucm_max_lemma_size               10
% 2.34/1.01  
% 2.34/1.01  ------ AIG Options
% 2.34/1.01  
% 2.34/1.01  --aig_mode                              false
% 2.34/1.01  
% 2.34/1.01  ------ Instantiation Options
% 2.34/1.01  
% 2.34/1.01  --instantiation_flag                    true
% 2.34/1.01  --inst_sos_flag                         false
% 2.34/1.01  --inst_sos_phase                        true
% 2.34/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/1.01  --inst_lit_sel_side                     num_symb
% 2.34/1.01  --inst_solver_per_active                1400
% 2.34/1.01  --inst_solver_calls_frac                1.
% 2.34/1.01  --inst_passive_queue_type               priority_queues
% 2.34/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/1.01  --inst_passive_queues_freq              [25;2]
% 2.34/1.01  --inst_dismatching                      true
% 2.34/1.01  --inst_eager_unprocessed_to_passive     true
% 2.34/1.01  --inst_prop_sim_given                   true
% 2.34/1.01  --inst_prop_sim_new                     false
% 2.34/1.01  --inst_subs_new                         false
% 2.34/1.01  --inst_eq_res_simp                      false
% 2.34/1.01  --inst_subs_given                       false
% 2.34/1.01  --inst_orphan_elimination               true
% 2.34/1.01  --inst_learning_loop_flag               true
% 2.34/1.01  --inst_learning_start                   3000
% 2.34/1.01  --inst_learning_factor                  2
% 2.34/1.01  --inst_start_prop_sim_after_learn       3
% 2.34/1.01  --inst_sel_renew                        solver
% 2.34/1.01  --inst_lit_activity_flag                true
% 2.34/1.01  --inst_restr_to_given                   false
% 2.34/1.01  --inst_activity_threshold               500
% 2.34/1.01  --inst_out_proof                        true
% 2.34/1.01  
% 2.34/1.01  ------ Resolution Options
% 2.34/1.01  
% 2.34/1.01  --resolution_flag                       true
% 2.34/1.01  --res_lit_sel                           adaptive
% 2.34/1.01  --res_lit_sel_side                      none
% 2.34/1.01  --res_ordering                          kbo
% 2.34/1.01  --res_to_prop_solver                    active
% 2.34/1.01  --res_prop_simpl_new                    false
% 2.34/1.01  --res_prop_simpl_given                  true
% 2.34/1.01  --res_passive_queue_type                priority_queues
% 2.34/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/1.01  --res_passive_queues_freq               [15;5]
% 2.34/1.01  --res_forward_subs                      full
% 2.34/1.01  --res_backward_subs                     full
% 2.34/1.01  --res_forward_subs_resolution           true
% 2.34/1.01  --res_backward_subs_resolution          true
% 2.34/1.01  --res_orphan_elimination                true
% 2.34/1.01  --res_time_limit                        2.
% 2.34/1.01  --res_out_proof                         true
% 2.34/1.01  
% 2.34/1.01  ------ Superposition Options
% 2.34/1.01  
% 2.34/1.01  --superposition_flag                    true
% 2.34/1.01  --sup_passive_queue_type                priority_queues
% 2.34/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.34/1.01  --demod_completeness_check              fast
% 2.34/1.01  --demod_use_ground                      true
% 2.34/1.01  --sup_to_prop_solver                    passive
% 2.34/1.01  --sup_prop_simpl_new                    true
% 2.34/1.01  --sup_prop_simpl_given                  true
% 2.34/1.01  --sup_fun_splitting                     false
% 2.34/1.01  --sup_smt_interval                      50000
% 2.34/1.01  
% 2.34/1.01  ------ Superposition Simplification Setup
% 2.34/1.01  
% 2.34/1.01  --sup_indices_passive                   []
% 2.34/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_full_bw                           [BwDemod]
% 2.34/1.01  --sup_immed_triv                        [TrivRules]
% 2.34/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_immed_bw_main                     []
% 2.34/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.01  
% 2.34/1.01  ------ Combination Options
% 2.34/1.01  
% 2.34/1.01  --comb_res_mult                         3
% 2.34/1.01  --comb_sup_mult                         2
% 2.34/1.01  --comb_inst_mult                        10
% 2.34/1.01  
% 2.34/1.01  ------ Debug Options
% 2.34/1.01  
% 2.34/1.01  --dbg_backtrace                         false
% 2.34/1.01  --dbg_dump_prop_clauses                 false
% 2.34/1.01  --dbg_dump_prop_clauses_file            -
% 2.34/1.01  --dbg_out_stat                          false
% 2.34/1.01  ------ Parsing...
% 2.34/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.34/1.01  ------ Proving...
% 2.34/1.01  ------ Problem Properties 
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  clauses                                 16
% 2.34/1.01  conjectures                             3
% 2.34/1.01  EPR                                     4
% 2.34/1.01  Horn                                    16
% 2.34/1.01  unary                                   9
% 2.34/1.01  binary                                  2
% 2.34/1.01  lits                                    31
% 2.34/1.01  lits eq                                 11
% 2.34/1.01  fd_pure                                 0
% 2.34/1.01  fd_pseudo                               0
% 2.34/1.01  fd_cond                                 0
% 2.34/1.01  fd_pseudo_cond                          1
% 2.34/1.01  AC symbols                              0
% 2.34/1.01  
% 2.34/1.01  ------ Schedule dynamic 5 is on 
% 2.34/1.01  
% 2.34/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  ------ 
% 2.34/1.01  Current options:
% 2.34/1.01  ------ 
% 2.34/1.01  
% 2.34/1.01  ------ Input Options
% 2.34/1.01  
% 2.34/1.01  --out_options                           all
% 2.34/1.01  --tptp_safe_out                         true
% 2.34/1.01  --problem_path                          ""
% 2.34/1.01  --include_path                          ""
% 2.34/1.01  --clausifier                            res/vclausify_rel
% 2.34/1.01  --clausifier_options                    --mode clausify
% 2.34/1.01  --stdin                                 false
% 2.34/1.01  --stats_out                             all
% 2.34/1.01  
% 2.34/1.01  ------ General Options
% 2.34/1.01  
% 2.34/1.01  --fof                                   false
% 2.34/1.01  --time_out_real                         305.
% 2.34/1.01  --time_out_virtual                      -1.
% 2.34/1.01  --symbol_type_check                     false
% 2.34/1.01  --clausify_out                          false
% 2.34/1.01  --sig_cnt_out                           false
% 2.34/1.01  --trig_cnt_out                          false
% 2.34/1.01  --trig_cnt_out_tolerance                1.
% 2.34/1.01  --trig_cnt_out_sk_spl                   false
% 2.34/1.01  --abstr_cl_out                          false
% 2.34/1.01  
% 2.34/1.01  ------ Global Options
% 2.34/1.01  
% 2.34/1.01  --schedule                              default
% 2.34/1.01  --add_important_lit                     false
% 2.34/1.01  --prop_solver_per_cl                    1000
% 2.34/1.01  --min_unsat_core                        false
% 2.34/1.01  --soft_assumptions                      false
% 2.34/1.01  --soft_lemma_size                       3
% 2.34/1.01  --prop_impl_unit_size                   0
% 2.34/1.01  --prop_impl_unit                        []
% 2.34/1.01  --share_sel_clauses                     true
% 2.34/1.01  --reset_solvers                         false
% 2.34/1.01  --bc_imp_inh                            [conj_cone]
% 2.34/1.01  --conj_cone_tolerance                   3.
% 2.34/1.01  --extra_neg_conj                        none
% 2.34/1.01  --large_theory_mode                     true
% 2.34/1.01  --prolific_symb_bound                   200
% 2.34/1.01  --lt_threshold                          2000
% 2.34/1.01  --clause_weak_htbl                      true
% 2.34/1.01  --gc_record_bc_elim                     false
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing Options
% 2.34/1.01  
% 2.34/1.01  --preprocessing_flag                    true
% 2.34/1.01  --time_out_prep_mult                    0.1
% 2.34/1.01  --splitting_mode                        input
% 2.34/1.01  --splitting_grd                         true
% 2.34/1.01  --splitting_cvd                         false
% 2.34/1.01  --splitting_cvd_svl                     false
% 2.34/1.01  --splitting_nvd                         32
% 2.34/1.01  --sub_typing                            true
% 2.34/1.01  --prep_gs_sim                           true
% 2.34/1.01  --prep_unflatten                        true
% 2.34/1.01  --prep_res_sim                          true
% 2.34/1.01  --prep_upred                            true
% 2.34/1.01  --prep_sem_filter                       exhaustive
% 2.34/1.01  --prep_sem_filter_out                   false
% 2.34/1.01  --pred_elim                             true
% 2.34/1.01  --res_sim_input                         true
% 2.34/1.01  --eq_ax_congr_red                       true
% 2.34/1.01  --pure_diseq_elim                       true
% 2.34/1.01  --brand_transform                       false
% 2.34/1.01  --non_eq_to_eq                          false
% 2.34/1.01  --prep_def_merge                        true
% 2.34/1.01  --prep_def_merge_prop_impl              false
% 2.34/1.01  --prep_def_merge_mbd                    true
% 2.34/1.01  --prep_def_merge_tr_red                 false
% 2.34/1.01  --prep_def_merge_tr_cl                  false
% 2.34/1.01  --smt_preprocessing                     true
% 2.34/1.01  --smt_ac_axioms                         fast
% 2.34/1.01  --preprocessed_out                      false
% 2.34/1.01  --preprocessed_stats                    false
% 2.34/1.01  
% 2.34/1.01  ------ Abstraction refinement Options
% 2.34/1.01  
% 2.34/1.01  --abstr_ref                             []
% 2.34/1.01  --abstr_ref_prep                        false
% 2.34/1.01  --abstr_ref_until_sat                   false
% 2.34/1.01  --abstr_ref_sig_restrict                funpre
% 2.34/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/1.01  --abstr_ref_under                       []
% 2.34/1.01  
% 2.34/1.01  ------ SAT Options
% 2.34/1.01  
% 2.34/1.01  --sat_mode                              false
% 2.34/1.01  --sat_fm_restart_options                ""
% 2.34/1.01  --sat_gr_def                            false
% 2.34/1.01  --sat_epr_types                         true
% 2.34/1.01  --sat_non_cyclic_types                  false
% 2.34/1.01  --sat_finite_models                     false
% 2.34/1.01  --sat_fm_lemmas                         false
% 2.34/1.01  --sat_fm_prep                           false
% 2.34/1.01  --sat_fm_uc_incr                        true
% 2.34/1.01  --sat_out_model                         small
% 2.34/1.01  --sat_out_clauses                       false
% 2.34/1.01  
% 2.34/1.01  ------ QBF Options
% 2.34/1.01  
% 2.34/1.01  --qbf_mode                              false
% 2.34/1.01  --qbf_elim_univ                         false
% 2.34/1.01  --qbf_dom_inst                          none
% 2.34/1.01  --qbf_dom_pre_inst                      false
% 2.34/1.01  --qbf_sk_in                             false
% 2.34/1.01  --qbf_pred_elim                         true
% 2.34/1.01  --qbf_split                             512
% 2.34/1.01  
% 2.34/1.01  ------ BMC1 Options
% 2.34/1.01  
% 2.34/1.01  --bmc1_incremental                      false
% 2.34/1.01  --bmc1_axioms                           reachable_all
% 2.34/1.01  --bmc1_min_bound                        0
% 2.34/1.01  --bmc1_max_bound                        -1
% 2.34/1.01  --bmc1_max_bound_default                -1
% 2.34/1.01  --bmc1_symbol_reachability              true
% 2.34/1.01  --bmc1_property_lemmas                  false
% 2.34/1.01  --bmc1_k_induction                      false
% 2.34/1.01  --bmc1_non_equiv_states                 false
% 2.34/1.01  --bmc1_deadlock                         false
% 2.34/1.01  --bmc1_ucm                              false
% 2.34/1.01  --bmc1_add_unsat_core                   none
% 2.34/1.01  --bmc1_unsat_core_children              false
% 2.34/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/1.01  --bmc1_out_stat                         full
% 2.34/1.01  --bmc1_ground_init                      false
% 2.34/1.01  --bmc1_pre_inst_next_state              false
% 2.34/1.01  --bmc1_pre_inst_state                   false
% 2.34/1.01  --bmc1_pre_inst_reach_state             false
% 2.34/1.01  --bmc1_out_unsat_core                   false
% 2.34/1.01  --bmc1_aig_witness_out                  false
% 2.34/1.01  --bmc1_verbose                          false
% 2.34/1.01  --bmc1_dump_clauses_tptp                false
% 2.34/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.34/1.01  --bmc1_dump_file                        -
% 2.34/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.34/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.34/1.01  --bmc1_ucm_extend_mode                  1
% 2.34/1.01  --bmc1_ucm_init_mode                    2
% 2.34/1.01  --bmc1_ucm_cone_mode                    none
% 2.34/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.34/1.01  --bmc1_ucm_relax_model                  4
% 2.34/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.34/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/1.01  --bmc1_ucm_layered_model                none
% 2.34/1.01  --bmc1_ucm_max_lemma_size               10
% 2.34/1.01  
% 2.34/1.01  ------ AIG Options
% 2.34/1.01  
% 2.34/1.01  --aig_mode                              false
% 2.34/1.01  
% 2.34/1.01  ------ Instantiation Options
% 2.34/1.01  
% 2.34/1.01  --instantiation_flag                    true
% 2.34/1.01  --inst_sos_flag                         false
% 2.34/1.01  --inst_sos_phase                        true
% 2.34/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/1.01  --inst_lit_sel_side                     none
% 2.34/1.01  --inst_solver_per_active                1400
% 2.34/1.01  --inst_solver_calls_frac                1.
% 2.34/1.01  --inst_passive_queue_type               priority_queues
% 2.34/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/1.01  --inst_passive_queues_freq              [25;2]
% 2.34/1.01  --inst_dismatching                      true
% 2.34/1.01  --inst_eager_unprocessed_to_passive     true
% 2.34/1.01  --inst_prop_sim_given                   true
% 2.34/1.01  --inst_prop_sim_new                     false
% 2.34/1.01  --inst_subs_new                         false
% 2.34/1.01  --inst_eq_res_simp                      false
% 2.34/1.01  --inst_subs_given                       false
% 2.34/1.01  --inst_orphan_elimination               true
% 2.34/1.01  --inst_learning_loop_flag               true
% 2.34/1.01  --inst_learning_start                   3000
% 2.34/1.01  --inst_learning_factor                  2
% 2.34/1.01  --inst_start_prop_sim_after_learn       3
% 2.34/1.01  --inst_sel_renew                        solver
% 2.34/1.01  --inst_lit_activity_flag                true
% 2.34/1.01  --inst_restr_to_given                   false
% 2.34/1.01  --inst_activity_threshold               500
% 2.34/1.01  --inst_out_proof                        true
% 2.34/1.01  
% 2.34/1.01  ------ Resolution Options
% 2.34/1.01  
% 2.34/1.01  --resolution_flag                       false
% 2.34/1.01  --res_lit_sel                           adaptive
% 2.34/1.01  --res_lit_sel_side                      none
% 2.34/1.01  --res_ordering                          kbo
% 2.34/1.01  --res_to_prop_solver                    active
% 2.34/1.01  --res_prop_simpl_new                    false
% 2.34/1.01  --res_prop_simpl_given                  true
% 2.34/1.01  --res_passive_queue_type                priority_queues
% 2.34/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/1.01  --res_passive_queues_freq               [15;5]
% 2.34/1.01  --res_forward_subs                      full
% 2.34/1.01  --res_backward_subs                     full
% 2.34/1.01  --res_forward_subs_resolution           true
% 2.34/1.01  --res_backward_subs_resolution          true
% 2.34/1.01  --res_orphan_elimination                true
% 2.34/1.01  --res_time_limit                        2.
% 2.34/1.01  --res_out_proof                         true
% 2.34/1.01  
% 2.34/1.01  ------ Superposition Options
% 2.34/1.01  
% 2.34/1.01  --superposition_flag                    true
% 2.34/1.01  --sup_passive_queue_type                priority_queues
% 2.34/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.34/1.01  --demod_completeness_check              fast
% 2.34/1.01  --demod_use_ground                      true
% 2.34/1.01  --sup_to_prop_solver                    passive
% 2.34/1.01  --sup_prop_simpl_new                    true
% 2.34/1.01  --sup_prop_simpl_given                  true
% 2.34/1.01  --sup_fun_splitting                     false
% 2.34/1.01  --sup_smt_interval                      50000
% 2.34/1.01  
% 2.34/1.01  ------ Superposition Simplification Setup
% 2.34/1.01  
% 2.34/1.01  --sup_indices_passive                   []
% 2.34/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_full_bw                           [BwDemod]
% 2.34/1.01  --sup_immed_triv                        [TrivRules]
% 2.34/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_immed_bw_main                     []
% 2.34/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.01  
% 2.34/1.01  ------ Combination Options
% 2.34/1.01  
% 2.34/1.01  --comb_res_mult                         3
% 2.34/1.01  --comb_sup_mult                         2
% 2.34/1.01  --comb_inst_mult                        10
% 2.34/1.01  
% 2.34/1.01  ------ Debug Options
% 2.34/1.01  
% 2.34/1.01  --dbg_backtrace                         false
% 2.34/1.01  --dbg_dump_prop_clauses                 false
% 2.34/1.01  --dbg_dump_prop_clauses_file            -
% 2.34/1.01  --dbg_out_stat                          false
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  ------ Proving...
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  % SZS status Theorem for theBenchmark.p
% 2.34/1.01  
% 2.34/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.34/1.01  
% 2.34/1.01  fof(f9,conjecture,(
% 2.34/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f10,negated_conjecture,(
% 2.34/1.01    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 2.34/1.01    inference(negated_conjecture,[],[f9])).
% 2.34/1.01  
% 2.34/1.01  fof(f20,plain,(
% 2.34/1.01    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.34/1.01    inference(ennf_transformation,[],[f10])).
% 2.34/1.01  
% 2.34/1.01  fof(f21,plain,(
% 2.34/1.01    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.34/1.01    inference(flattening,[],[f20])).
% 2.34/1.01  
% 2.34/1.01  fof(f24,plain,(
% 2.34/1.01    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.34/1.01    introduced(choice_axiom,[])).
% 2.34/1.01  
% 2.34/1.01  fof(f25,plain,(
% 2.34/1.01    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.34/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f24])).
% 2.34/1.01  
% 2.34/1.01  fof(f40,plain,(
% 2.34/1.01    v1_relat_1(sK0)),
% 2.34/1.01    inference(cnf_transformation,[],[f25])).
% 2.34/1.01  
% 2.34/1.01  fof(f8,axiom,(
% 2.34/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f18,plain,(
% 2.34/1.01    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.34/1.01    inference(ennf_transformation,[],[f8])).
% 2.34/1.01  
% 2.34/1.01  fof(f19,plain,(
% 2.34/1.01    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.34/1.01    inference(flattening,[],[f18])).
% 2.34/1.01  
% 2.34/1.01  fof(f39,plain,(
% 2.34/1.01    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f19])).
% 2.34/1.01  
% 2.34/1.01  fof(f42,plain,(
% 2.34/1.01    v2_funct_1(sK0)),
% 2.34/1.01    inference(cnf_transformation,[],[f25])).
% 2.34/1.01  
% 2.34/1.01  fof(f41,plain,(
% 2.34/1.01    v1_funct_1(sK0)),
% 2.34/1.01    inference(cnf_transformation,[],[f25])).
% 2.34/1.01  
% 2.34/1.01  fof(f4,axiom,(
% 2.34/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f32,plain,(
% 2.34/1.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.34/1.01    inference(cnf_transformation,[],[f4])).
% 2.34/1.01  
% 2.34/1.01  fof(f2,axiom,(
% 2.34/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f11,plain,(
% 2.34/1.01    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.34/1.01    inference(ennf_transformation,[],[f2])).
% 2.34/1.01  
% 2.34/1.01  fof(f12,plain,(
% 2.34/1.01    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.34/1.01    inference(flattening,[],[f11])).
% 2.34/1.01  
% 2.34/1.01  fof(f29,plain,(
% 2.34/1.01    ( ! [X2,X0,X1] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f12])).
% 2.34/1.01  
% 2.34/1.01  fof(f7,axiom,(
% 2.34/1.01    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f36,plain,(
% 2.34/1.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.34/1.01    inference(cnf_transformation,[],[f7])).
% 2.34/1.01  
% 2.34/1.01  fof(f6,axiom,(
% 2.34/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f16,plain,(
% 2.34/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.34/1.01    inference(ennf_transformation,[],[f6])).
% 2.34/1.01  
% 2.34/1.01  fof(f17,plain,(
% 2.34/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.34/1.01    inference(flattening,[],[f16])).
% 2.34/1.01  
% 2.34/1.01  fof(f34,plain,(
% 2.34/1.01    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f17])).
% 2.34/1.01  
% 2.34/1.01  fof(f5,axiom,(
% 2.34/1.01    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f15,plain,(
% 2.34/1.01    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.34/1.01    inference(ennf_transformation,[],[f5])).
% 2.34/1.01  
% 2.34/1.01  fof(f33,plain,(
% 2.34/1.01    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f15])).
% 2.34/1.01  
% 2.34/1.01  fof(f3,axiom,(
% 2.34/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f13,plain,(
% 2.34/1.01    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.34/1.01    inference(ennf_transformation,[],[f3])).
% 2.34/1.01  
% 2.34/1.01  fof(f14,plain,(
% 2.34/1.01    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.34/1.01    inference(flattening,[],[f13])).
% 2.34/1.01  
% 2.34/1.01  fof(f30,plain,(
% 2.34/1.01    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f14])).
% 2.34/1.01  
% 2.34/1.01  fof(f38,plain,(
% 2.34/1.01    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f19])).
% 2.34/1.01  
% 2.34/1.01  fof(f1,axiom,(
% 2.34/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.34/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.01  
% 2.34/1.01  fof(f22,plain,(
% 2.34/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.34/1.01    inference(nnf_transformation,[],[f1])).
% 2.34/1.01  
% 2.34/1.01  fof(f23,plain,(
% 2.34/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.34/1.01    inference(flattening,[],[f22])).
% 2.34/1.01  
% 2.34/1.01  fof(f27,plain,(
% 2.34/1.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.34/1.01    inference(cnf_transformation,[],[f23])).
% 2.34/1.01  
% 2.34/1.01  fof(f44,plain,(
% 2.34/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.34/1.01    inference(equality_resolution,[],[f27])).
% 2.34/1.01  
% 2.34/1.01  fof(f28,plain,(
% 2.34/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.34/1.01    inference(cnf_transformation,[],[f23])).
% 2.34/1.01  
% 2.34/1.01  fof(f26,plain,(
% 2.34/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.34/1.01    inference(cnf_transformation,[],[f23])).
% 2.34/1.01  
% 2.34/1.01  fof(f45,plain,(
% 2.34/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.34/1.01    inference(equality_resolution,[],[f26])).
% 2.34/1.01  
% 2.34/1.01  fof(f43,plain,(
% 2.34/1.01    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 2.34/1.01    inference(cnf_transformation,[],[f25])).
% 2.34/1.01  
% 2.34/1.01  cnf(c_17,negated_conjecture,
% 2.34/1.01      ( v1_relat_1(sK0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_483,plain,
% 2.34/1.01      ( v1_relat_1(sK0) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_12,plain,
% 2.34/1.01      ( ~ v2_funct_1(X0)
% 2.34/1.01      | ~ v1_funct_1(X0)
% 2.34/1.01      | ~ v1_relat_1(X0)
% 2.34/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_15,negated_conjecture,
% 2.34/1.01      ( v2_funct_1(sK0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_179,plain,
% 2.34/1.01      ( ~ v1_funct_1(X0)
% 2.34/1.01      | ~ v1_relat_1(X0)
% 2.34/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.34/1.01      | sK0 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_180,plain,
% 2.34/1.01      ( ~ v1_funct_1(sK0)
% 2.34/1.01      | ~ v1_relat_1(sK0)
% 2.34/1.01      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_179]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_16,negated_conjecture,
% 2.34/1.01      ( v1_funct_1(sK0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_25,plain,
% 2.34/1.01      ( ~ v2_funct_1(sK0)
% 2.34/1.01      | ~ v1_funct_1(sK0)
% 2.34/1.01      | ~ v1_relat_1(sK0)
% 2.34/1.01      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_182,plain,
% 2.34/1.01      ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_180,c_17,c_16,c_15,c_25]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_5,plain,
% 2.34/1.01      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 2.34/1.01      inference(cnf_transformation,[],[f32]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3,plain,
% 2.34/1.01      ( ~ v1_relat_1(X0)
% 2.34/1.01      | ~ v1_relat_1(X1)
% 2.34/1.01      | ~ v1_relat_1(X2)
% 2.34/1.01      | k2_relat_1(X1) != k2_relat_1(X2)
% 2.34/1.01      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(k5_relat_1(X2,X0)) ),
% 2.34/1.01      inference(cnf_transformation,[],[f29]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_491,plain,
% 2.34/1.01      ( k2_relat_1(X0) != k2_relat_1(X1)
% 2.34/1.01      | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
% 2.34/1.01      | v1_relat_1(X2) != iProver_top
% 2.34/1.01      | v1_relat_1(X0) != iProver_top
% 2.34/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1811,plain,
% 2.34/1.01      ( k2_relat_1(X0) != X1
% 2.34/1.01      | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
% 2.34/1.01      | v1_relat_1(X0) != iProver_top
% 2.34/1.01      | v1_relat_1(X2) != iProver_top
% 2.34/1.01      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_5,c_491]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_11,plain,
% 2.34/1.01      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.34/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_485,plain,
% 2.34/1.01      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2188,plain,
% 2.34/1.01      ( k2_relat_1(X0) != X1
% 2.34/1.01      | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
% 2.34/1.01      | v1_relat_1(X0) != iProver_top
% 2.34/1.01      | v1_relat_1(X2) != iProver_top ),
% 2.34/1.01      inference(forward_subsumption_resolution,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_1811,c_485]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2193,plain,
% 2.34/1.01      ( k1_relat_1(sK0) != X0
% 2.34/1.01      | k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
% 2.34/1.01      | v1_relat_1(X1) != iProver_top
% 2.34/1.01      | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_182,c_2188]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_18,plain,
% 2.34/1.01      ( v1_relat_1(sK0) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_19,plain,
% 2.34/1.01      ( v1_funct_1(sK0) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_9,plain,
% 2.34/1.01      ( ~ v1_funct_1(X0)
% 2.34/1.01      | ~ v1_relat_1(X0)
% 2.34/1.01      | v1_relat_1(k2_funct_1(X0)) ),
% 2.34/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_33,plain,
% 2.34/1.01      ( v1_funct_1(X0) != iProver_top
% 2.34/1.01      | v1_relat_1(X0) != iProver_top
% 2.34/1.01      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_35,plain,
% 2.34/1.01      ( v1_funct_1(sK0) != iProver_top
% 2.34/1.01      | v1_relat_1(k2_funct_1(sK0)) = iProver_top
% 2.34/1.01      | v1_relat_1(sK0) != iProver_top ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_33]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2843,plain,
% 2.34/1.01      ( v1_relat_1(X1) != iProver_top
% 2.34/1.01      | k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
% 2.34/1.01      | k1_relat_1(sK0) != X0 ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_2193,c_18,c_19,c_35]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2844,plain,
% 2.34/1.01      ( k1_relat_1(sK0) != X0
% 2.34/1.01      | k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
% 2.34/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.34/1.01      inference(renaming,[status(thm)],[c_2843]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2852,plain,
% 2.34/1.01      ( k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
% 2.34/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.34/1.01      inference(equality_resolution,[status(thm)],[c_2844]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3708,plain,
% 2.34/1.01      ( k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_483,c_2852]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_7,plain,
% 2.34/1.01      ( ~ v1_relat_1(X0)
% 2.34/1.01      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
% 2.34/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_489,plain,
% 2.34/1.01      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 2.34/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_995,plain,
% 2.34/1.01      ( k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) = sK0 ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_483,c_489]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_3710,plain,
% 2.34/1.01      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0) ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_3708,c_995]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_269,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_638,plain,
% 2.34/1.01      ( X0 != X1 | k2_relat_1(sK0) != X1 | k2_relat_1(sK0) = X0 ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_269]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_677,plain,
% 2.34/1.01      ( X0 != k2_relat_1(X1)
% 2.34/1.01      | k2_relat_1(sK0) = X0
% 2.34/1.01      | k2_relat_1(sK0) != k2_relat_1(X1) ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_638]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_798,plain,
% 2.34/1.01      ( k2_relat_1(X0) != k2_relat_1(X1)
% 2.34/1.01      | k2_relat_1(sK0) != k2_relat_1(X1)
% 2.34/1.01      | k2_relat_1(sK0) = k2_relat_1(X0) ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_677]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1732,plain,
% 2.34/1.01      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(X0)
% 2.34/1.01      | k2_relat_1(sK0) != k2_relat_1(X0)
% 2.34/1.01      | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_798]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1734,plain,
% 2.34/1.01      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)
% 2.34/1.01      | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
% 2.34/1.01      | k2_relat_1(sK0) != k2_relat_1(sK0) ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_1732]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_4,plain,
% 2.34/1.01      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 2.34/1.01      | ~ v1_relat_1(X1)
% 2.34/1.01      | ~ v1_relat_1(X0)
% 2.34/1.01      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f30]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_490,plain,
% 2.34/1.01      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 2.34/1.01      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 2.34/1.01      | v1_relat_1(X0) != iProver_top
% 2.34/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1477,plain,
% 2.34/1.01      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k1_relat_1(k2_funct_1(sK0))
% 2.34/1.01      | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) != iProver_top
% 2.34/1.01      | v1_relat_1(X0) != iProver_top
% 2.34/1.01      | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
% 2.34/1.01      inference(superposition,[status(thm)],[c_182,c_490]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_13,plain,
% 2.34/1.01      ( ~ v2_funct_1(X0)
% 2.34/1.01      | ~ v1_funct_1(X0)
% 2.34/1.01      | ~ v1_relat_1(X0)
% 2.34/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_171,plain,
% 2.34/1.01      ( ~ v1_funct_1(X0)
% 2.34/1.01      | ~ v1_relat_1(X0)
% 2.34/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.34/1.01      | sK0 != X0 ),
% 2.34/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_15]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_172,plain,
% 2.34/1.01      ( ~ v1_funct_1(sK0)
% 2.34/1.01      | ~ v1_relat_1(sK0)
% 2.34/1.01      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.34/1.01      inference(unflattening,[status(thm)],[c_171]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_22,plain,
% 2.34/1.01      ( ~ v2_funct_1(sK0)
% 2.34/1.01      | ~ v1_funct_1(sK0)
% 2.34/1.01      | ~ v1_relat_1(sK0)
% 2.34/1.01      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_174,plain,
% 2.34/1.01      ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.34/1.01      inference(global_propositional_subsumption,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_172,c_17,c_16,c_15,c_22]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1500,plain,
% 2.34/1.01      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k2_relat_1(sK0)
% 2.34/1.01      | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) != iProver_top
% 2.34/1.01      | v1_relat_1(X0) != iProver_top
% 2.34/1.01      | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
% 2.34/1.01      inference(light_normalisation,[status(thm)],[c_1477,c_174]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1521,plain,
% 2.34/1.01      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0)
% 2.34/1.01      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top
% 2.34/1.01      | v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 2.34/1.01      | v1_relat_1(sK0) != iProver_top ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_1500]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_1,plain,
% 2.34/1.01      ( r1_tarski(X0,X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_751,plain,
% 2.34/1.01      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_754,plain,
% 2.34/1.01      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) = iProver_top ),
% 2.34/1.01      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_591,plain,
% 2.34/1.01      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != X0
% 2.34/1.01      | k2_relat_1(sK0) != X0
% 2.34/1.01      | k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_269]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_634,plain,
% 2.34/1.01      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(X0)
% 2.34/1.01      | k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
% 2.34/1.01      | k2_relat_1(sK0) != k2_relat_1(X0) ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_591]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_636,plain,
% 2.34/1.01      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)
% 2.34/1.01      | k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
% 2.34/1.01      | k2_relat_1(sK0) != k2_relat_1(sK0) ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_634]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_272,plain,
% 2.34/1.01      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 2.34/1.01      theory(equality) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_280,plain,
% 2.34/1.01      ( k2_relat_1(sK0) = k2_relat_1(sK0) | sK0 != sK0 ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_272]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_0,plain,
% 2.34/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.34/1.01      inference(cnf_transformation,[],[f28]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_55,plain,
% 2.34/1.01      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_2,plain,
% 2.34/1.01      ( r1_tarski(X0,X0) ),
% 2.34/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_51,plain,
% 2.34/1.01      ( r1_tarski(sK0,sK0) ),
% 2.34/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(c_14,negated_conjecture,
% 2.34/1.01      ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
% 2.34/1.01      | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
% 2.34/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.34/1.01  
% 2.34/1.01  cnf(contradiction,plain,
% 2.34/1.01      ( $false ),
% 2.34/1.01      inference(minisat,
% 2.34/1.01                [status(thm)],
% 2.34/1.01                [c_3710,c_1734,c_1521,c_754,c_636,c_280,c_55,c_51,c_35,
% 2.34/1.01                 c_14,c_19,c_18]) ).
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.34/1.01  
% 2.34/1.01  ------                               Statistics
% 2.34/1.01  
% 2.34/1.01  ------ General
% 2.34/1.01  
% 2.34/1.01  abstr_ref_over_cycles:                  0
% 2.34/1.01  abstr_ref_under_cycles:                 0
% 2.34/1.01  gc_basic_clause_elim:                   0
% 2.34/1.01  forced_gc_time:                         0
% 2.34/1.01  parsing_time:                           0.012
% 2.34/1.01  unif_index_cands_time:                  0.
% 2.34/1.01  unif_index_add_time:                    0.
% 2.34/1.01  orderings_time:                         0.
% 2.34/1.01  out_proof_time:                         0.007
% 2.34/1.01  total_time:                             0.17
% 2.34/1.01  num_of_symbols:                         41
% 2.34/1.01  num_of_terms:                           2822
% 2.34/1.01  
% 2.34/1.01  ------ Preprocessing
% 2.34/1.01  
% 2.34/1.01  num_of_splits:                          0
% 2.34/1.01  num_of_split_atoms:                     0
% 2.34/1.01  num_of_reused_defs:                     0
% 2.34/1.01  num_eq_ax_congr_red:                    0
% 2.34/1.01  num_of_sem_filtered_clauses:            1
% 2.34/1.01  num_of_subtypes:                        0
% 2.34/1.01  monotx_restored_types:                  0
% 2.34/1.01  sat_num_of_epr_types:                   0
% 2.34/1.01  sat_num_of_non_cyclic_types:            0
% 2.34/1.01  sat_guarded_non_collapsed_types:        0
% 2.34/1.01  num_pure_diseq_elim:                    0
% 2.34/1.01  simp_replaced_by:                       0
% 2.34/1.01  res_preprocessed:                       86
% 2.34/1.01  prep_upred:                             0
% 2.34/1.01  prep_unflattend:                        2
% 2.34/1.01  smt_new_axioms:                         0
% 2.34/1.01  pred_elim_cands:                        3
% 2.34/1.01  pred_elim:                              1
% 2.34/1.01  pred_elim_cl:                           1
% 2.34/1.01  pred_elim_cycles:                       3
% 2.34/1.01  merged_defs:                            0
% 2.34/1.01  merged_defs_ncl:                        0
% 2.34/1.01  bin_hyper_res:                          0
% 2.34/1.01  prep_cycles:                            4
% 2.34/1.01  pred_elim_time:                         0.
% 2.34/1.01  splitting_time:                         0.
% 2.34/1.01  sem_filter_time:                        0.
% 2.34/1.01  monotx_time:                            0.001
% 2.34/1.01  subtype_inf_time:                       0.
% 2.34/1.01  
% 2.34/1.01  ------ Problem properties
% 2.34/1.01  
% 2.34/1.01  clauses:                                16
% 2.34/1.01  conjectures:                            3
% 2.34/1.01  epr:                                    4
% 2.34/1.01  horn:                                   16
% 2.34/1.01  ground:                                 5
% 2.34/1.01  unary:                                  9
% 2.34/1.01  binary:                                 2
% 2.34/1.01  lits:                                   31
% 2.34/1.01  lits_eq:                                11
% 2.34/1.01  fd_pure:                                0
% 2.34/1.01  fd_pseudo:                              0
% 2.34/1.01  fd_cond:                                0
% 2.34/1.01  fd_pseudo_cond:                         1
% 2.34/1.01  ac_symbols:                             0
% 2.34/1.01  
% 2.34/1.01  ------ Propositional Solver
% 2.34/1.01  
% 2.34/1.01  prop_solver_calls:                      27
% 2.34/1.01  prop_fast_solver_calls:                 515
% 2.34/1.01  smt_solver_calls:                       0
% 2.34/1.01  smt_fast_solver_calls:                  0
% 2.34/1.01  prop_num_of_clauses:                    1295
% 2.34/1.01  prop_preprocess_simplified:             4051
% 2.34/1.01  prop_fo_subsumed:                       18
% 2.34/1.01  prop_solver_time:                       0.
% 2.34/1.01  smt_solver_time:                        0.
% 2.34/1.01  smt_fast_solver_time:                   0.
% 2.34/1.01  prop_fast_solver_time:                  0.
% 2.34/1.01  prop_unsat_core_time:                   0.
% 2.34/1.01  
% 2.34/1.01  ------ QBF
% 2.34/1.01  
% 2.34/1.01  qbf_q_res:                              0
% 2.34/1.01  qbf_num_tautologies:                    0
% 2.34/1.01  qbf_prep_cycles:                        0
% 2.34/1.01  
% 2.34/1.01  ------ BMC1
% 2.34/1.01  
% 2.34/1.01  bmc1_current_bound:                     -1
% 2.34/1.01  bmc1_last_solved_bound:                 -1
% 2.34/1.01  bmc1_unsat_core_size:                   -1
% 2.34/1.01  bmc1_unsat_core_parents_size:           -1
% 2.34/1.01  bmc1_merge_next_fun:                    0
% 2.34/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.34/1.01  
% 2.34/1.01  ------ Instantiation
% 2.34/1.01  
% 2.34/1.01  inst_num_of_clauses:                    476
% 2.34/1.01  inst_num_in_passive:                    40
% 2.34/1.01  inst_num_in_active:                     196
% 2.34/1.01  inst_num_in_unprocessed:                241
% 2.34/1.01  inst_num_of_loops:                      200
% 2.34/1.01  inst_num_of_learning_restarts:          0
% 2.34/1.01  inst_num_moves_active_passive:          2
% 2.34/1.01  inst_lit_activity:                      0
% 2.34/1.01  inst_lit_activity_moves:                0
% 2.34/1.01  inst_num_tautologies:                   0
% 2.34/1.01  inst_num_prop_implied:                  0
% 2.34/1.01  inst_num_existing_simplified:           0
% 2.34/1.01  inst_num_eq_res_simplified:             0
% 2.34/1.01  inst_num_child_elim:                    0
% 2.34/1.01  inst_num_of_dismatching_blockings:      422
% 2.34/1.01  inst_num_of_non_proper_insts:           656
% 2.34/1.01  inst_num_of_duplicates:                 0
% 2.34/1.01  inst_inst_num_from_inst_to_res:         0
% 2.34/1.01  inst_dismatching_checking_time:         0.
% 2.34/1.01  
% 2.34/1.01  ------ Resolution
% 2.34/1.01  
% 2.34/1.01  res_num_of_clauses:                     0
% 2.34/1.01  res_num_in_passive:                     0
% 2.34/1.01  res_num_in_active:                      0
% 2.34/1.01  res_num_of_loops:                       90
% 2.34/1.01  res_forward_subset_subsumed:            69
% 2.34/1.01  res_backward_subset_subsumed:           2
% 2.34/1.01  res_forward_subsumed:                   0
% 2.34/1.01  res_backward_subsumed:                  0
% 2.34/1.01  res_forward_subsumption_resolution:     0
% 2.34/1.01  res_backward_subsumption_resolution:    0
% 2.34/1.01  res_clause_to_clause_subsumption:       116
% 2.34/1.01  res_orphan_elimination:                 0
% 2.34/1.01  res_tautology_del:                      56
% 2.34/1.01  res_num_eq_res_simplified:              0
% 2.34/1.01  res_num_sel_changes:                    0
% 2.34/1.01  res_moves_from_active_to_pass:          0
% 2.34/1.01  
% 2.34/1.01  ------ Superposition
% 2.34/1.01  
% 2.34/1.01  sup_time_total:                         0.
% 2.34/1.01  sup_time_generating:                    0.
% 2.34/1.01  sup_time_sim_full:                      0.
% 2.34/1.01  sup_time_sim_immed:                     0.
% 2.34/1.01  
% 2.34/1.01  sup_num_of_clauses:                     56
% 2.34/1.01  sup_num_in_active:                      39
% 2.34/1.01  sup_num_in_passive:                     17
% 2.34/1.01  sup_num_of_loops:                       39
% 2.34/1.01  sup_fw_superposition:                   39
% 2.34/1.01  sup_bw_superposition:                   10
% 2.34/1.01  sup_immediate_simplified:               12
% 2.34/1.01  sup_given_eliminated:                   0
% 2.34/1.01  comparisons_done:                       0
% 2.34/1.01  comparisons_avoided:                    0
% 2.34/1.01  
% 2.34/1.01  ------ Simplifications
% 2.34/1.01  
% 2.34/1.01  
% 2.34/1.01  sim_fw_subset_subsumed:                 2
% 2.34/1.01  sim_bw_subset_subsumed:                 0
% 2.34/1.01  sim_fw_subsumed:                        2
% 2.34/1.01  sim_bw_subsumed:                        0
% 2.34/1.01  sim_fw_subsumption_res:                 4
% 2.34/1.01  sim_bw_subsumption_res:                 0
% 2.34/1.01  sim_tautology_del:                      0
% 2.34/1.01  sim_eq_tautology_del:                   5
% 2.34/1.01  sim_eq_res_simp:                        1
% 2.34/1.01  sim_fw_demodulated:                     0
% 2.34/1.01  sim_bw_demodulated:                     1
% 2.34/1.01  sim_light_normalised:                   11
% 2.34/1.01  sim_joinable_taut:                      0
% 2.34/1.01  sim_joinable_simp:                      0
% 2.34/1.01  sim_ac_normalised:                      0
% 2.34/1.01  sim_smt_subsumption:                    0
% 2.34/1.01  
%------------------------------------------------------------------------------
