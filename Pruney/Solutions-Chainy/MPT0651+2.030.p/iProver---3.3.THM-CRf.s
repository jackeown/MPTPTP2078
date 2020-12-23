%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:31 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 308 expanded)
%              Number of clauses        :   60 (  96 expanded)
%              Number of leaves         :   12 (  63 expanded)
%              Depth                    :   17
%              Number of atoms          :  284 (1225 expanded)
%              Number of equality atoms :  161 ( 509 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
        | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f38,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

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

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f27,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_435,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_438,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_434,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k2_relat_1(X1) != k2_relat_1(X2)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(k5_relat_1(X2,X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_442,plain,
    ( k2_relat_1(X0) != k2_relat_1(X1)
    | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1216,plain,
    ( k2_relat_1(X0) != X1
    | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_442])).

cnf(c_9,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_436,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1477,plain,
    ( k2_relat_1(X0) != X1
    | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1216,c_436])).

cnf(c_1483,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(X0)),X1)) = k2_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1477])).

cnf(c_3910,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) = k2_relat_1(k5_relat_1(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_434,c_1483])).

cnf(c_3933,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(X0))) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(X0)))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_438,c_3910])).

cnf(c_4226,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0))) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_435,c_3933])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_163,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_164,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_163])).

cnf(c_23,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_166,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_164,c_15,c_14,c_13,c_23])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_441,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_812,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(X0))),k2_funct_1(X0)) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_438,c_441])).

cnf(c_978,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK0))),k2_funct_1(sK0)) = k2_funct_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_435,c_812])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_155,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_156,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_155])).

cnf(c_20,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_158,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_156,c_15,c_14,c_13,c_20])).

cnf(c_981,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) = k2_funct_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_978,c_158])).

cnf(c_16,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1004,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) = k2_funct_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_981,c_16])).

cnf(c_4229,plain,
    ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4226,c_166,c_1004])).

cnf(c_3,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_relat_1(X1) != k1_relat_1(X2)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_443,plain,
    ( k1_relat_1(X0) != k1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1442,plain,
    ( k1_relat_1(X0) != X1
    | k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X2,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_443])).

cnf(c_1597,plain,
    ( k1_relat_1(X0) != X1
    | k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X2,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1442,c_436])).

cnf(c_1602,plain,
    ( k2_relat_1(sK0) != X0
    | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_158,c_1597])).

cnf(c_17,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_31,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_33,plain,
    ( v1_funct_1(sK0) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_1695,plain,
    ( v1_relat_1(X1) != iProver_top
    | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))
    | k2_relat_1(sK0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1602,c_16,c_17,c_33])).

cnf(c_1696,plain,
    ( k2_relat_1(sK0) != X0
    | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1695])).

cnf(c_1704,plain,
    ( k1_relat_1(k5_relat_1(X0,k6_relat_1(k2_relat_1(sK0)))) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1696])).

cnf(c_2109,plain,
    ( k1_relat_1(k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(superposition,[status(thm)],[c_434,c_1704])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_440,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_669,plain,
    ( k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) = sK0 ),
    inference(superposition,[status(thm)],[c_434,c_440])).

cnf(c_2111,plain,
    ( k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_2109,c_669])).

cnf(c_12,negated_conjecture,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2126,plain,
    ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) != k1_relat_1(sK0)
    | k1_relat_1(sK0) != k1_relat_1(sK0) ),
    inference(demodulation,[status(thm)],[c_2111,c_12])).

cnf(c_246,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_263,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_249,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_256,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4229,c_2126,c_263,c_256,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:17:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.83/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.02  
% 2.83/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.83/1.02  
% 2.83/1.02  ------  iProver source info
% 2.83/1.02  
% 2.83/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.83/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.83/1.02  git: non_committed_changes: false
% 2.83/1.02  git: last_make_outside_of_git: false
% 2.83/1.02  
% 2.83/1.02  ------ 
% 2.83/1.02  
% 2.83/1.02  ------ Input Options
% 2.83/1.02  
% 2.83/1.02  --out_options                           all
% 2.83/1.02  --tptp_safe_out                         true
% 2.83/1.02  --problem_path                          ""
% 2.83/1.02  --include_path                          ""
% 2.83/1.02  --clausifier                            res/vclausify_rel
% 2.83/1.02  --clausifier_options                    --mode clausify
% 2.83/1.02  --stdin                                 false
% 2.83/1.02  --stats_out                             all
% 2.83/1.02  
% 2.83/1.02  ------ General Options
% 2.83/1.02  
% 2.83/1.02  --fof                                   false
% 2.83/1.02  --time_out_real                         305.
% 2.83/1.02  --time_out_virtual                      -1.
% 2.83/1.02  --symbol_type_check                     false
% 2.83/1.02  --clausify_out                          false
% 2.83/1.02  --sig_cnt_out                           false
% 2.83/1.02  --trig_cnt_out                          false
% 2.83/1.02  --trig_cnt_out_tolerance                1.
% 2.83/1.02  --trig_cnt_out_sk_spl                   false
% 2.83/1.02  --abstr_cl_out                          false
% 2.83/1.02  
% 2.83/1.02  ------ Global Options
% 2.83/1.02  
% 2.83/1.02  --schedule                              default
% 2.83/1.02  --add_important_lit                     false
% 2.83/1.02  --prop_solver_per_cl                    1000
% 2.83/1.02  --min_unsat_core                        false
% 2.83/1.02  --soft_assumptions                      false
% 2.83/1.02  --soft_lemma_size                       3
% 2.83/1.02  --prop_impl_unit_size                   0
% 2.83/1.02  --prop_impl_unit                        []
% 2.83/1.02  --share_sel_clauses                     true
% 2.83/1.02  --reset_solvers                         false
% 2.83/1.02  --bc_imp_inh                            [conj_cone]
% 2.83/1.02  --conj_cone_tolerance                   3.
% 2.83/1.02  --extra_neg_conj                        none
% 2.83/1.02  --large_theory_mode                     true
% 2.83/1.02  --prolific_symb_bound                   200
% 2.83/1.02  --lt_threshold                          2000
% 2.83/1.02  --clause_weak_htbl                      true
% 2.83/1.02  --gc_record_bc_elim                     false
% 2.83/1.02  
% 2.83/1.02  ------ Preprocessing Options
% 2.83/1.02  
% 2.83/1.02  --preprocessing_flag                    true
% 2.83/1.02  --time_out_prep_mult                    0.1
% 2.83/1.02  --splitting_mode                        input
% 2.83/1.02  --splitting_grd                         true
% 2.83/1.02  --splitting_cvd                         false
% 2.83/1.02  --splitting_cvd_svl                     false
% 2.83/1.02  --splitting_nvd                         32
% 2.83/1.02  --sub_typing                            true
% 2.83/1.02  --prep_gs_sim                           true
% 2.83/1.02  --prep_unflatten                        true
% 2.83/1.02  --prep_res_sim                          true
% 2.83/1.02  --prep_upred                            true
% 2.83/1.02  --prep_sem_filter                       exhaustive
% 2.83/1.02  --prep_sem_filter_out                   false
% 2.83/1.02  --pred_elim                             true
% 2.83/1.02  --res_sim_input                         true
% 2.83/1.02  --eq_ax_congr_red                       true
% 2.83/1.02  --pure_diseq_elim                       true
% 2.83/1.02  --brand_transform                       false
% 2.83/1.02  --non_eq_to_eq                          false
% 2.83/1.02  --prep_def_merge                        true
% 2.83/1.02  --prep_def_merge_prop_impl              false
% 2.83/1.02  --prep_def_merge_mbd                    true
% 2.83/1.02  --prep_def_merge_tr_red                 false
% 2.83/1.02  --prep_def_merge_tr_cl                  false
% 2.83/1.02  --smt_preprocessing                     true
% 2.83/1.02  --smt_ac_axioms                         fast
% 2.83/1.02  --preprocessed_out                      false
% 2.83/1.02  --preprocessed_stats                    false
% 2.83/1.02  
% 2.83/1.02  ------ Abstraction refinement Options
% 2.83/1.02  
% 2.83/1.02  --abstr_ref                             []
% 2.83/1.02  --abstr_ref_prep                        false
% 2.83/1.02  --abstr_ref_until_sat                   false
% 2.83/1.02  --abstr_ref_sig_restrict                funpre
% 2.83/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.83/1.02  --abstr_ref_under                       []
% 2.83/1.02  
% 2.83/1.02  ------ SAT Options
% 2.83/1.02  
% 2.83/1.02  --sat_mode                              false
% 2.83/1.02  --sat_fm_restart_options                ""
% 2.83/1.02  --sat_gr_def                            false
% 2.83/1.02  --sat_epr_types                         true
% 2.83/1.02  --sat_non_cyclic_types                  false
% 2.83/1.02  --sat_finite_models                     false
% 2.83/1.02  --sat_fm_lemmas                         false
% 2.83/1.02  --sat_fm_prep                           false
% 2.83/1.02  --sat_fm_uc_incr                        true
% 2.83/1.02  --sat_out_model                         small
% 2.83/1.02  --sat_out_clauses                       false
% 2.83/1.02  
% 2.83/1.02  ------ QBF Options
% 2.83/1.02  
% 2.83/1.02  --qbf_mode                              false
% 2.83/1.02  --qbf_elim_univ                         false
% 2.83/1.02  --qbf_dom_inst                          none
% 2.83/1.02  --qbf_dom_pre_inst                      false
% 2.83/1.02  --qbf_sk_in                             false
% 2.83/1.02  --qbf_pred_elim                         true
% 2.83/1.02  --qbf_split                             512
% 2.83/1.02  
% 2.83/1.02  ------ BMC1 Options
% 2.83/1.02  
% 2.83/1.02  --bmc1_incremental                      false
% 2.83/1.02  --bmc1_axioms                           reachable_all
% 2.83/1.02  --bmc1_min_bound                        0
% 2.83/1.02  --bmc1_max_bound                        -1
% 2.83/1.02  --bmc1_max_bound_default                -1
% 2.83/1.02  --bmc1_symbol_reachability              true
% 2.83/1.02  --bmc1_property_lemmas                  false
% 2.83/1.02  --bmc1_k_induction                      false
% 2.83/1.02  --bmc1_non_equiv_states                 false
% 2.83/1.02  --bmc1_deadlock                         false
% 2.83/1.02  --bmc1_ucm                              false
% 2.83/1.02  --bmc1_add_unsat_core                   none
% 2.83/1.02  --bmc1_unsat_core_children              false
% 2.83/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.83/1.02  --bmc1_out_stat                         full
% 2.83/1.02  --bmc1_ground_init                      false
% 2.83/1.02  --bmc1_pre_inst_next_state              false
% 2.83/1.02  --bmc1_pre_inst_state                   false
% 2.83/1.02  --bmc1_pre_inst_reach_state             false
% 2.83/1.02  --bmc1_out_unsat_core                   false
% 2.83/1.02  --bmc1_aig_witness_out                  false
% 2.83/1.02  --bmc1_verbose                          false
% 2.83/1.02  --bmc1_dump_clauses_tptp                false
% 2.83/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.83/1.02  --bmc1_dump_file                        -
% 2.83/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.83/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.83/1.02  --bmc1_ucm_extend_mode                  1
% 2.83/1.02  --bmc1_ucm_init_mode                    2
% 2.83/1.02  --bmc1_ucm_cone_mode                    none
% 2.83/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.83/1.02  --bmc1_ucm_relax_model                  4
% 2.83/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.83/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.83/1.02  --bmc1_ucm_layered_model                none
% 2.83/1.02  --bmc1_ucm_max_lemma_size               10
% 2.83/1.02  
% 2.83/1.02  ------ AIG Options
% 2.83/1.02  
% 2.83/1.02  --aig_mode                              false
% 2.83/1.02  
% 2.83/1.02  ------ Instantiation Options
% 2.83/1.02  
% 2.83/1.02  --instantiation_flag                    true
% 2.83/1.02  --inst_sos_flag                         false
% 2.83/1.02  --inst_sos_phase                        true
% 2.83/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.83/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.83/1.02  --inst_lit_sel_side                     num_symb
% 2.83/1.02  --inst_solver_per_active                1400
% 2.83/1.02  --inst_solver_calls_frac                1.
% 2.83/1.02  --inst_passive_queue_type               priority_queues
% 2.83/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.83/1.02  --inst_passive_queues_freq              [25;2]
% 2.83/1.02  --inst_dismatching                      true
% 2.83/1.02  --inst_eager_unprocessed_to_passive     true
% 2.83/1.02  --inst_prop_sim_given                   true
% 2.83/1.02  --inst_prop_sim_new                     false
% 2.83/1.02  --inst_subs_new                         false
% 2.83/1.02  --inst_eq_res_simp                      false
% 2.83/1.02  --inst_subs_given                       false
% 2.83/1.02  --inst_orphan_elimination               true
% 2.83/1.02  --inst_learning_loop_flag               true
% 2.83/1.02  --inst_learning_start                   3000
% 2.83/1.02  --inst_learning_factor                  2
% 2.83/1.02  --inst_start_prop_sim_after_learn       3
% 2.83/1.02  --inst_sel_renew                        solver
% 2.83/1.02  --inst_lit_activity_flag                true
% 2.83/1.02  --inst_restr_to_given                   false
% 2.83/1.02  --inst_activity_threshold               500
% 2.83/1.02  --inst_out_proof                        true
% 2.83/1.02  
% 2.83/1.02  ------ Resolution Options
% 2.83/1.02  
% 2.83/1.02  --resolution_flag                       true
% 2.83/1.02  --res_lit_sel                           adaptive
% 2.83/1.02  --res_lit_sel_side                      none
% 2.83/1.02  --res_ordering                          kbo
% 2.83/1.02  --res_to_prop_solver                    active
% 2.83/1.02  --res_prop_simpl_new                    false
% 2.83/1.02  --res_prop_simpl_given                  true
% 2.83/1.02  --res_passive_queue_type                priority_queues
% 2.83/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.83/1.02  --res_passive_queues_freq               [15;5]
% 2.83/1.02  --res_forward_subs                      full
% 2.83/1.02  --res_backward_subs                     full
% 2.83/1.02  --res_forward_subs_resolution           true
% 2.83/1.02  --res_backward_subs_resolution          true
% 2.83/1.02  --res_orphan_elimination                true
% 2.83/1.02  --res_time_limit                        2.
% 2.83/1.02  --res_out_proof                         true
% 2.83/1.02  
% 2.83/1.02  ------ Superposition Options
% 2.83/1.02  
% 2.83/1.02  --superposition_flag                    true
% 2.83/1.02  --sup_passive_queue_type                priority_queues
% 2.83/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.83/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.83/1.02  --demod_completeness_check              fast
% 2.83/1.02  --demod_use_ground                      true
% 2.83/1.02  --sup_to_prop_solver                    passive
% 2.83/1.02  --sup_prop_simpl_new                    true
% 2.83/1.02  --sup_prop_simpl_given                  true
% 2.83/1.02  --sup_fun_splitting                     false
% 2.83/1.02  --sup_smt_interval                      50000
% 2.83/1.02  
% 2.83/1.02  ------ Superposition Simplification Setup
% 2.83/1.02  
% 2.83/1.02  --sup_indices_passive                   []
% 2.83/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.83/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/1.02  --sup_full_bw                           [BwDemod]
% 2.83/1.02  --sup_immed_triv                        [TrivRules]
% 2.83/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.83/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/1.02  --sup_immed_bw_main                     []
% 2.83/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.83/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/1.02  
% 2.83/1.02  ------ Combination Options
% 2.83/1.02  
% 2.83/1.02  --comb_res_mult                         3
% 2.83/1.02  --comb_sup_mult                         2
% 2.83/1.02  --comb_inst_mult                        10
% 2.83/1.02  
% 2.83/1.02  ------ Debug Options
% 2.83/1.02  
% 2.83/1.02  --dbg_backtrace                         false
% 2.83/1.02  --dbg_dump_prop_clauses                 false
% 2.83/1.02  --dbg_dump_prop_clauses_file            -
% 2.83/1.02  --dbg_out_stat                          false
% 2.83/1.02  ------ Parsing...
% 2.83/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.83/1.02  
% 2.83/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.83/1.02  
% 2.83/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.83/1.02  
% 2.83/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.83/1.02  ------ Proving...
% 2.83/1.02  ------ Problem Properties 
% 2.83/1.02  
% 2.83/1.02  
% 2.83/1.02  clauses                                 15
% 2.83/1.02  conjectures                             3
% 2.83/1.02  EPR                                     2
% 2.83/1.02  Horn                                    15
% 2.83/1.02  unary                                   8
% 2.83/1.02  binary                                  3
% 2.83/1.02  lits                                    30
% 2.83/1.02  lits eq                                 12
% 2.83/1.02  fd_pure                                 0
% 2.83/1.02  fd_pseudo                               0
% 2.83/1.02  fd_cond                                 0
% 2.83/1.02  fd_pseudo_cond                          0
% 2.83/1.02  AC symbols                              0
% 2.83/1.02  
% 2.83/1.02  ------ Schedule dynamic 5 is on 
% 2.83/1.02  
% 2.83/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.83/1.02  
% 2.83/1.02  
% 2.83/1.02  ------ 
% 2.83/1.02  Current options:
% 2.83/1.02  ------ 
% 2.83/1.02  
% 2.83/1.02  ------ Input Options
% 2.83/1.02  
% 2.83/1.02  --out_options                           all
% 2.83/1.02  --tptp_safe_out                         true
% 2.83/1.02  --problem_path                          ""
% 2.83/1.02  --include_path                          ""
% 2.83/1.02  --clausifier                            res/vclausify_rel
% 2.83/1.02  --clausifier_options                    --mode clausify
% 2.83/1.02  --stdin                                 false
% 2.83/1.02  --stats_out                             all
% 2.83/1.02  
% 2.83/1.02  ------ General Options
% 2.83/1.02  
% 2.83/1.02  --fof                                   false
% 2.83/1.02  --time_out_real                         305.
% 2.83/1.02  --time_out_virtual                      -1.
% 2.83/1.02  --symbol_type_check                     false
% 2.83/1.02  --clausify_out                          false
% 2.83/1.02  --sig_cnt_out                           false
% 2.83/1.02  --trig_cnt_out                          false
% 2.83/1.02  --trig_cnt_out_tolerance                1.
% 2.83/1.02  --trig_cnt_out_sk_spl                   false
% 2.83/1.02  --abstr_cl_out                          false
% 2.83/1.02  
% 2.83/1.02  ------ Global Options
% 2.83/1.02  
% 2.83/1.02  --schedule                              default
% 2.83/1.02  --add_important_lit                     false
% 2.83/1.02  --prop_solver_per_cl                    1000
% 2.83/1.02  --min_unsat_core                        false
% 2.83/1.02  --soft_assumptions                      false
% 2.83/1.02  --soft_lemma_size                       3
% 2.83/1.02  --prop_impl_unit_size                   0
% 2.83/1.02  --prop_impl_unit                        []
% 2.83/1.02  --share_sel_clauses                     true
% 2.83/1.02  --reset_solvers                         false
% 2.83/1.02  --bc_imp_inh                            [conj_cone]
% 2.83/1.02  --conj_cone_tolerance                   3.
% 2.83/1.02  --extra_neg_conj                        none
% 2.83/1.02  --large_theory_mode                     true
% 2.83/1.02  --prolific_symb_bound                   200
% 2.83/1.02  --lt_threshold                          2000
% 2.83/1.02  --clause_weak_htbl                      true
% 2.83/1.02  --gc_record_bc_elim                     false
% 2.83/1.02  
% 2.83/1.02  ------ Preprocessing Options
% 2.83/1.02  
% 2.83/1.02  --preprocessing_flag                    true
% 2.83/1.02  --time_out_prep_mult                    0.1
% 2.83/1.02  --splitting_mode                        input
% 2.83/1.02  --splitting_grd                         true
% 2.83/1.02  --splitting_cvd                         false
% 2.83/1.02  --splitting_cvd_svl                     false
% 2.83/1.02  --splitting_nvd                         32
% 2.83/1.02  --sub_typing                            true
% 2.83/1.02  --prep_gs_sim                           true
% 2.83/1.02  --prep_unflatten                        true
% 2.83/1.02  --prep_res_sim                          true
% 2.83/1.02  --prep_upred                            true
% 2.83/1.02  --prep_sem_filter                       exhaustive
% 2.83/1.02  --prep_sem_filter_out                   false
% 2.83/1.02  --pred_elim                             true
% 2.83/1.02  --res_sim_input                         true
% 2.83/1.02  --eq_ax_congr_red                       true
% 2.83/1.02  --pure_diseq_elim                       true
% 2.83/1.02  --brand_transform                       false
% 2.83/1.02  --non_eq_to_eq                          false
% 2.83/1.02  --prep_def_merge                        true
% 2.83/1.02  --prep_def_merge_prop_impl              false
% 2.83/1.02  --prep_def_merge_mbd                    true
% 2.83/1.02  --prep_def_merge_tr_red                 false
% 2.83/1.02  --prep_def_merge_tr_cl                  false
% 2.83/1.02  --smt_preprocessing                     true
% 2.83/1.02  --smt_ac_axioms                         fast
% 2.83/1.02  --preprocessed_out                      false
% 2.83/1.02  --preprocessed_stats                    false
% 2.83/1.02  
% 2.83/1.02  ------ Abstraction refinement Options
% 2.83/1.02  
% 2.83/1.02  --abstr_ref                             []
% 2.83/1.02  --abstr_ref_prep                        false
% 2.83/1.02  --abstr_ref_until_sat                   false
% 2.83/1.02  --abstr_ref_sig_restrict                funpre
% 2.83/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.83/1.02  --abstr_ref_under                       []
% 2.83/1.02  
% 2.83/1.02  ------ SAT Options
% 2.83/1.02  
% 2.83/1.02  --sat_mode                              false
% 2.83/1.02  --sat_fm_restart_options                ""
% 2.83/1.02  --sat_gr_def                            false
% 2.83/1.02  --sat_epr_types                         true
% 2.83/1.02  --sat_non_cyclic_types                  false
% 2.83/1.02  --sat_finite_models                     false
% 2.83/1.02  --sat_fm_lemmas                         false
% 2.83/1.02  --sat_fm_prep                           false
% 2.83/1.02  --sat_fm_uc_incr                        true
% 2.83/1.02  --sat_out_model                         small
% 2.83/1.02  --sat_out_clauses                       false
% 2.83/1.02  
% 2.83/1.02  ------ QBF Options
% 2.83/1.02  
% 2.83/1.02  --qbf_mode                              false
% 2.83/1.02  --qbf_elim_univ                         false
% 2.83/1.02  --qbf_dom_inst                          none
% 2.83/1.02  --qbf_dom_pre_inst                      false
% 2.83/1.02  --qbf_sk_in                             false
% 2.83/1.02  --qbf_pred_elim                         true
% 2.83/1.02  --qbf_split                             512
% 2.83/1.02  
% 2.83/1.02  ------ BMC1 Options
% 2.83/1.02  
% 2.83/1.02  --bmc1_incremental                      false
% 2.83/1.02  --bmc1_axioms                           reachable_all
% 2.83/1.02  --bmc1_min_bound                        0
% 2.83/1.02  --bmc1_max_bound                        -1
% 2.83/1.02  --bmc1_max_bound_default                -1
% 2.83/1.02  --bmc1_symbol_reachability              true
% 2.83/1.02  --bmc1_property_lemmas                  false
% 2.83/1.02  --bmc1_k_induction                      false
% 2.83/1.02  --bmc1_non_equiv_states                 false
% 2.83/1.02  --bmc1_deadlock                         false
% 2.83/1.02  --bmc1_ucm                              false
% 2.83/1.02  --bmc1_add_unsat_core                   none
% 2.83/1.02  --bmc1_unsat_core_children              false
% 2.83/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.83/1.02  --bmc1_out_stat                         full
% 2.83/1.02  --bmc1_ground_init                      false
% 2.83/1.02  --bmc1_pre_inst_next_state              false
% 2.83/1.02  --bmc1_pre_inst_state                   false
% 2.83/1.02  --bmc1_pre_inst_reach_state             false
% 2.83/1.02  --bmc1_out_unsat_core                   false
% 2.83/1.02  --bmc1_aig_witness_out                  false
% 2.83/1.02  --bmc1_verbose                          false
% 2.83/1.02  --bmc1_dump_clauses_tptp                false
% 2.83/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.83/1.02  --bmc1_dump_file                        -
% 2.83/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.83/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.83/1.02  --bmc1_ucm_extend_mode                  1
% 2.83/1.02  --bmc1_ucm_init_mode                    2
% 2.83/1.02  --bmc1_ucm_cone_mode                    none
% 2.83/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.83/1.02  --bmc1_ucm_relax_model                  4
% 2.83/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.83/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.83/1.02  --bmc1_ucm_layered_model                none
% 2.83/1.02  --bmc1_ucm_max_lemma_size               10
% 2.83/1.02  
% 2.83/1.02  ------ AIG Options
% 2.83/1.02  
% 2.83/1.02  --aig_mode                              false
% 2.83/1.02  
% 2.83/1.02  ------ Instantiation Options
% 2.83/1.02  
% 2.83/1.02  --instantiation_flag                    true
% 2.83/1.02  --inst_sos_flag                         false
% 2.83/1.02  --inst_sos_phase                        true
% 2.83/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.83/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.83/1.02  --inst_lit_sel_side                     none
% 2.83/1.02  --inst_solver_per_active                1400
% 2.83/1.02  --inst_solver_calls_frac                1.
% 2.83/1.02  --inst_passive_queue_type               priority_queues
% 2.83/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.83/1.02  --inst_passive_queues_freq              [25;2]
% 2.83/1.02  --inst_dismatching                      true
% 2.83/1.02  --inst_eager_unprocessed_to_passive     true
% 2.83/1.02  --inst_prop_sim_given                   true
% 2.83/1.02  --inst_prop_sim_new                     false
% 2.83/1.02  --inst_subs_new                         false
% 2.83/1.02  --inst_eq_res_simp                      false
% 2.83/1.02  --inst_subs_given                       false
% 2.83/1.02  --inst_orphan_elimination               true
% 2.83/1.02  --inst_learning_loop_flag               true
% 2.83/1.02  --inst_learning_start                   3000
% 2.83/1.02  --inst_learning_factor                  2
% 2.83/1.02  --inst_start_prop_sim_after_learn       3
% 2.83/1.02  --inst_sel_renew                        solver
% 2.83/1.02  --inst_lit_activity_flag                true
% 2.83/1.02  --inst_restr_to_given                   false
% 2.83/1.02  --inst_activity_threshold               500
% 2.83/1.02  --inst_out_proof                        true
% 2.83/1.02  
% 2.83/1.02  ------ Resolution Options
% 2.83/1.02  
% 2.83/1.02  --resolution_flag                       false
% 2.83/1.02  --res_lit_sel                           adaptive
% 2.83/1.02  --res_lit_sel_side                      none
% 2.83/1.02  --res_ordering                          kbo
% 2.83/1.02  --res_to_prop_solver                    active
% 2.83/1.02  --res_prop_simpl_new                    false
% 2.83/1.02  --res_prop_simpl_given                  true
% 2.83/1.02  --res_passive_queue_type                priority_queues
% 2.83/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.83/1.02  --res_passive_queues_freq               [15;5]
% 2.83/1.02  --res_forward_subs                      full
% 2.83/1.02  --res_backward_subs                     full
% 2.83/1.02  --res_forward_subs_resolution           true
% 2.83/1.02  --res_backward_subs_resolution          true
% 2.83/1.02  --res_orphan_elimination                true
% 2.83/1.02  --res_time_limit                        2.
% 2.83/1.02  --res_out_proof                         true
% 2.83/1.02  
% 2.83/1.02  ------ Superposition Options
% 2.83/1.02  
% 2.83/1.02  --superposition_flag                    true
% 2.83/1.02  --sup_passive_queue_type                priority_queues
% 2.83/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.83/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.83/1.02  --demod_completeness_check              fast
% 2.83/1.02  --demod_use_ground                      true
% 2.83/1.02  --sup_to_prop_solver                    passive
% 2.83/1.02  --sup_prop_simpl_new                    true
% 2.83/1.02  --sup_prop_simpl_given                  true
% 2.83/1.02  --sup_fun_splitting                     false
% 2.83/1.02  --sup_smt_interval                      50000
% 2.83/1.02  
% 2.83/1.02  ------ Superposition Simplification Setup
% 2.83/1.02  
% 2.83/1.02  --sup_indices_passive                   []
% 2.83/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.83/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.83/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/1.02  --sup_full_bw                           [BwDemod]
% 2.83/1.02  --sup_immed_triv                        [TrivRules]
% 2.83/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.83/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/1.02  --sup_immed_bw_main                     []
% 2.83/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.83/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.83/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.83/1.02  
% 2.83/1.02  ------ Combination Options
% 2.83/1.02  
% 2.83/1.02  --comb_res_mult                         3
% 2.83/1.02  --comb_sup_mult                         2
% 2.83/1.02  --comb_inst_mult                        10
% 2.83/1.02  
% 2.83/1.02  ------ Debug Options
% 2.83/1.02  
% 2.83/1.02  --dbg_backtrace                         false
% 2.83/1.02  --dbg_dump_prop_clauses                 false
% 2.83/1.02  --dbg_dump_prop_clauses_file            -
% 2.83/1.02  --dbg_out_stat                          false
% 2.83/1.02  
% 2.83/1.02  
% 2.83/1.02  
% 2.83/1.02  
% 2.83/1.02  ------ Proving...
% 2.83/1.02  
% 2.83/1.02  
% 2.83/1.02  % SZS status Theorem for theBenchmark.p
% 2.83/1.02  
% 2.83/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.83/1.02  
% 2.83/1.02  fof(f9,conjecture,(
% 2.83/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 2.83/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/1.02  
% 2.83/1.02  fof(f10,negated_conjecture,(
% 2.83/1.02    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 2.83/1.02    inference(negated_conjecture,[],[f9])).
% 2.83/1.02  
% 2.83/1.02  fof(f21,plain,(
% 2.83/1.02    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.83/1.02    inference(ennf_transformation,[],[f10])).
% 2.83/1.02  
% 2.83/1.02  fof(f22,plain,(
% 2.83/1.02    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.83/1.02    inference(flattening,[],[f21])).
% 2.83/1.02  
% 2.83/1.02  fof(f23,plain,(
% 2.83/1.02    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.83/1.02    introduced(choice_axiom,[])).
% 2.83/1.02  
% 2.83/1.02  fof(f24,plain,(
% 2.83/1.02    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.83/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 2.83/1.02  
% 2.83/1.02  fof(f38,plain,(
% 2.83/1.02    v1_funct_1(sK0)),
% 2.83/1.02    inference(cnf_transformation,[],[f24])).
% 2.83/1.02  
% 2.83/1.02  fof(f6,axiom,(
% 2.83/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.83/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/1.02  
% 2.83/1.02  fof(f17,plain,(
% 2.83/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.83/1.02    inference(ennf_transformation,[],[f6])).
% 2.83/1.02  
% 2.83/1.02  fof(f18,plain,(
% 2.83/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.83/1.02    inference(flattening,[],[f17])).
% 2.83/1.02  
% 2.83/1.02  fof(f31,plain,(
% 2.83/1.02    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.83/1.02    inference(cnf_transformation,[],[f18])).
% 2.83/1.02  
% 2.83/1.02  fof(f37,plain,(
% 2.83/1.02    v1_relat_1(sK0)),
% 2.83/1.02    inference(cnf_transformation,[],[f24])).
% 2.83/1.02  
% 2.83/1.02  fof(f3,axiom,(
% 2.83/1.02    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.83/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/1.02  
% 2.83/1.02  fof(f28,plain,(
% 2.83/1.02    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.83/1.02    inference(cnf_transformation,[],[f3])).
% 2.83/1.02  
% 2.83/1.02  fof(f2,axiom,(
% 2.83/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 2.83/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/1.02  
% 2.83/1.02  fof(f13,plain,(
% 2.83/1.02    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.83/1.02    inference(ennf_transformation,[],[f2])).
% 2.83/1.02  
% 2.83/1.02  fof(f14,plain,(
% 2.83/1.02    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.83/1.02    inference(flattening,[],[f13])).
% 2.83/1.02  
% 2.83/1.02  fof(f26,plain,(
% 2.83/1.02    ( ! [X2,X0,X1] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.83/1.02    inference(cnf_transformation,[],[f14])).
% 2.83/1.02  
% 2.83/1.02  fof(f7,axiom,(
% 2.83/1.02    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.83/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/1.02  
% 2.83/1.02  fof(f33,plain,(
% 2.83/1.02    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.83/1.02    inference(cnf_transformation,[],[f7])).
% 2.83/1.02  
% 2.83/1.02  fof(f8,axiom,(
% 2.83/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.83/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/1.02  
% 2.83/1.02  fof(f19,plain,(
% 2.83/1.02    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.83/1.02    inference(ennf_transformation,[],[f8])).
% 2.83/1.02  
% 2.83/1.02  fof(f20,plain,(
% 2.83/1.02    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.83/1.02    inference(flattening,[],[f19])).
% 2.83/1.02  
% 2.83/1.02  fof(f36,plain,(
% 2.83/1.02    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.83/1.02    inference(cnf_transformation,[],[f20])).
% 2.83/1.02  
% 2.83/1.02  fof(f39,plain,(
% 2.83/1.02    v2_funct_1(sK0)),
% 2.83/1.02    inference(cnf_transformation,[],[f24])).
% 2.83/1.02  
% 2.83/1.02  fof(f4,axiom,(
% 2.83/1.02    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.83/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/1.02  
% 2.83/1.02  fof(f15,plain,(
% 2.83/1.02    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.83/1.02    inference(ennf_transformation,[],[f4])).
% 2.83/1.02  
% 2.83/1.02  fof(f29,plain,(
% 2.83/1.02    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.83/1.02    inference(cnf_transformation,[],[f15])).
% 2.83/1.02  
% 2.83/1.02  fof(f35,plain,(
% 2.83/1.02    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.83/1.02    inference(cnf_transformation,[],[f20])).
% 2.83/1.02  
% 2.83/1.02  fof(f27,plain,(
% 2.83/1.02    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.83/1.02    inference(cnf_transformation,[],[f3])).
% 2.83/1.02  
% 2.83/1.02  fof(f1,axiom,(
% 2.83/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 2.83/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/1.02  
% 2.83/1.02  fof(f11,plain,(
% 2.83/1.02    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.83/1.02    inference(ennf_transformation,[],[f1])).
% 2.83/1.02  
% 2.83/1.02  fof(f12,plain,(
% 2.83/1.02    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.83/1.02    inference(flattening,[],[f11])).
% 2.83/1.02  
% 2.83/1.02  fof(f25,plain,(
% 2.83/1.02    ( ! [X2,X0,X1] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.83/1.02    inference(cnf_transformation,[],[f12])).
% 2.83/1.02  
% 2.83/1.02  fof(f5,axiom,(
% 2.83/1.02    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.83/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.83/1.02  
% 2.83/1.02  fof(f16,plain,(
% 2.83/1.02    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.83/1.02    inference(ennf_transformation,[],[f5])).
% 2.83/1.02  
% 2.83/1.02  fof(f30,plain,(
% 2.83/1.02    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.83/1.02    inference(cnf_transformation,[],[f16])).
% 2.83/1.02  
% 2.83/1.02  fof(f40,plain,(
% 2.83/1.02    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 2.83/1.02    inference(cnf_transformation,[],[f24])).
% 2.83/1.02  
% 2.83/1.02  cnf(c_14,negated_conjecture,
% 2.83/1.02      ( v1_funct_1(sK0) ),
% 2.83/1.02      inference(cnf_transformation,[],[f38]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_435,plain,
% 2.83/1.02      ( v1_funct_1(sK0) = iProver_top ),
% 2.83/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_7,plain,
% 2.83/1.02      ( ~ v1_funct_1(X0)
% 2.83/1.02      | ~ v1_relat_1(X0)
% 2.83/1.02      | v1_relat_1(k2_funct_1(X0)) ),
% 2.83/1.02      inference(cnf_transformation,[],[f31]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_438,plain,
% 2.83/1.02      ( v1_funct_1(X0) != iProver_top
% 2.83/1.02      | v1_relat_1(X0) != iProver_top
% 2.83/1.02      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 2.83/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_15,negated_conjecture,
% 2.83/1.02      ( v1_relat_1(sK0) ),
% 2.83/1.02      inference(cnf_transformation,[],[f37]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_434,plain,
% 2.83/1.02      ( v1_relat_1(sK0) = iProver_top ),
% 2.83/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_2,plain,
% 2.83/1.02      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 2.83/1.02      inference(cnf_transformation,[],[f28]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_1,plain,
% 2.83/1.02      ( ~ v1_relat_1(X0)
% 2.83/1.02      | ~ v1_relat_1(X1)
% 2.83/1.02      | ~ v1_relat_1(X2)
% 2.83/1.02      | k2_relat_1(X1) != k2_relat_1(X2)
% 2.83/1.02      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(k5_relat_1(X2,X0)) ),
% 2.83/1.02      inference(cnf_transformation,[],[f26]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_442,plain,
% 2.83/1.02      ( k2_relat_1(X0) != k2_relat_1(X1)
% 2.83/1.02      | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
% 2.83/1.02      | v1_relat_1(X2) != iProver_top
% 2.83/1.02      | v1_relat_1(X0) != iProver_top
% 2.83/1.02      | v1_relat_1(X1) != iProver_top ),
% 2.83/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_1216,plain,
% 2.83/1.02      ( k2_relat_1(X0) != X1
% 2.83/1.02      | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
% 2.83/1.02      | v1_relat_1(X0) != iProver_top
% 2.83/1.02      | v1_relat_1(X2) != iProver_top
% 2.83/1.02      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 2.83/1.02      inference(superposition,[status(thm)],[c_2,c_442]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_9,plain,
% 2.83/1.02      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.83/1.02      inference(cnf_transformation,[],[f33]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_436,plain,
% 2.83/1.02      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.83/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_1477,plain,
% 2.83/1.02      ( k2_relat_1(X0) != X1
% 2.83/1.02      | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
% 2.83/1.02      | v1_relat_1(X0) != iProver_top
% 2.83/1.02      | v1_relat_1(X2) != iProver_top ),
% 2.83/1.02      inference(forward_subsumption_resolution,
% 2.83/1.02                [status(thm)],
% 2.83/1.02                [c_1216,c_436]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_1483,plain,
% 2.83/1.02      ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(X0)),X1)) = k2_relat_1(k5_relat_1(X0,X1))
% 2.83/1.02      | v1_relat_1(X0) != iProver_top
% 2.83/1.02      | v1_relat_1(X1) != iProver_top ),
% 2.83/1.02      inference(equality_resolution,[status(thm)],[c_1477]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_3910,plain,
% 2.83/1.02      ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) = k2_relat_1(k5_relat_1(sK0,X0))
% 2.83/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.83/1.02      inference(superposition,[status(thm)],[c_434,c_1483]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_3933,plain,
% 2.83/1.02      ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(X0))) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(X0)))
% 2.83/1.02      | v1_funct_1(X0) != iProver_top
% 2.83/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.83/1.02      inference(superposition,[status(thm)],[c_438,c_3910]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_4226,plain,
% 2.83/1.02      ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0))) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
% 2.83/1.02      | v1_relat_1(sK0) != iProver_top ),
% 2.83/1.02      inference(superposition,[status(thm)],[c_435,c_3933]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_10,plain,
% 2.83/1.02      ( ~ v2_funct_1(X0)
% 2.83/1.02      | ~ v1_funct_1(X0)
% 2.83/1.02      | ~ v1_relat_1(X0)
% 2.83/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.83/1.02      inference(cnf_transformation,[],[f36]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_13,negated_conjecture,
% 2.83/1.02      ( v2_funct_1(sK0) ),
% 2.83/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_163,plain,
% 2.83/1.02      ( ~ v1_funct_1(X0)
% 2.83/1.02      | ~ v1_relat_1(X0)
% 2.83/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.83/1.02      | sK0 != X0 ),
% 2.83/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_13]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_164,plain,
% 2.83/1.02      ( ~ v1_funct_1(sK0)
% 2.83/1.02      | ~ v1_relat_1(sK0)
% 2.83/1.02      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 2.83/1.02      inference(unflattening,[status(thm)],[c_163]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_23,plain,
% 2.83/1.02      ( ~ v2_funct_1(sK0)
% 2.83/1.02      | ~ v1_funct_1(sK0)
% 2.83/1.02      | ~ v1_relat_1(sK0)
% 2.83/1.02      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 2.83/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_166,plain,
% 2.83/1.02      ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 2.83/1.02      inference(global_propositional_subsumption,
% 2.83/1.02                [status(thm)],
% 2.83/1.02                [c_164,c_15,c_14,c_13,c_23]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_4,plain,
% 2.83/1.02      ( ~ v1_relat_1(X0)
% 2.83/1.02      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
% 2.83/1.02      inference(cnf_transformation,[],[f29]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_441,plain,
% 2.83/1.02      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 2.83/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.83/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_812,plain,
% 2.83/1.02      ( k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(X0))),k2_funct_1(X0)) = k2_funct_1(X0)
% 2.83/1.02      | v1_funct_1(X0) != iProver_top
% 2.83/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.83/1.02      inference(superposition,[status(thm)],[c_438,c_441]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_978,plain,
% 2.83/1.02      ( k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK0))),k2_funct_1(sK0)) = k2_funct_1(sK0)
% 2.83/1.02      | v1_relat_1(sK0) != iProver_top ),
% 2.83/1.02      inference(superposition,[status(thm)],[c_435,c_812]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_11,plain,
% 2.83/1.02      ( ~ v2_funct_1(X0)
% 2.83/1.02      | ~ v1_funct_1(X0)
% 2.83/1.02      | ~ v1_relat_1(X0)
% 2.83/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.83/1.02      inference(cnf_transformation,[],[f35]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_155,plain,
% 2.83/1.02      ( ~ v1_funct_1(X0)
% 2.83/1.02      | ~ v1_relat_1(X0)
% 2.83/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.83/1.02      | sK0 != X0 ),
% 2.83/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_13]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_156,plain,
% 2.83/1.02      ( ~ v1_funct_1(sK0)
% 2.83/1.02      | ~ v1_relat_1(sK0)
% 2.83/1.02      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.83/1.02      inference(unflattening,[status(thm)],[c_155]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_20,plain,
% 2.83/1.02      ( ~ v2_funct_1(sK0)
% 2.83/1.02      | ~ v1_funct_1(sK0)
% 2.83/1.02      | ~ v1_relat_1(sK0)
% 2.83/1.02      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.83/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_158,plain,
% 2.83/1.02      ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.83/1.02      inference(global_propositional_subsumption,
% 2.83/1.02                [status(thm)],
% 2.83/1.02                [c_156,c_15,c_14,c_13,c_20]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_981,plain,
% 2.83/1.02      ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) = k2_funct_1(sK0)
% 2.83/1.02      | v1_relat_1(sK0) != iProver_top ),
% 2.83/1.02      inference(light_normalisation,[status(thm)],[c_978,c_158]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_16,plain,
% 2.83/1.02      ( v1_relat_1(sK0) = iProver_top ),
% 2.83/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_1004,plain,
% 2.83/1.02      ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) = k2_funct_1(sK0) ),
% 2.83/1.02      inference(global_propositional_subsumption,
% 2.83/1.02                [status(thm)],
% 2.83/1.02                [c_981,c_16]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_4229,plain,
% 2.83/1.02      ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(sK0)
% 2.83/1.02      | v1_relat_1(sK0) != iProver_top ),
% 2.83/1.02      inference(light_normalisation,[status(thm)],[c_4226,c_166,c_1004]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_3,plain,
% 2.83/1.02      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.83/1.02      inference(cnf_transformation,[],[f27]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_0,plain,
% 2.83/1.02      ( ~ v1_relat_1(X0)
% 2.83/1.02      | ~ v1_relat_1(X1)
% 2.83/1.02      | ~ v1_relat_1(X2)
% 2.83/1.02      | k1_relat_1(X1) != k1_relat_1(X2)
% 2.83/1.02      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,X2)) ),
% 2.83/1.02      inference(cnf_transformation,[],[f25]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_443,plain,
% 2.83/1.02      ( k1_relat_1(X0) != k1_relat_1(X1)
% 2.83/1.02      | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
% 2.83/1.02      | v1_relat_1(X2) != iProver_top
% 2.83/1.02      | v1_relat_1(X0) != iProver_top
% 2.83/1.02      | v1_relat_1(X1) != iProver_top ),
% 2.83/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_1442,plain,
% 2.83/1.02      ( k1_relat_1(X0) != X1
% 2.83/1.02      | k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X2,X0))
% 2.83/1.02      | v1_relat_1(X0) != iProver_top
% 2.83/1.02      | v1_relat_1(X2) != iProver_top
% 2.83/1.02      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 2.83/1.02      inference(superposition,[status(thm)],[c_3,c_443]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_1597,plain,
% 2.83/1.02      ( k1_relat_1(X0) != X1
% 2.83/1.02      | k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X2,X0))
% 2.83/1.02      | v1_relat_1(X0) != iProver_top
% 2.83/1.02      | v1_relat_1(X2) != iProver_top ),
% 2.83/1.02      inference(forward_subsumption_resolution,
% 2.83/1.02                [status(thm)],
% 2.83/1.02                [c_1442,c_436]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_1602,plain,
% 2.83/1.02      ( k2_relat_1(sK0) != X0
% 2.83/1.02      | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))
% 2.83/1.02      | v1_relat_1(X1) != iProver_top
% 2.83/1.02      | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
% 2.83/1.02      inference(superposition,[status(thm)],[c_158,c_1597]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_17,plain,
% 2.83/1.02      ( v1_funct_1(sK0) = iProver_top ),
% 2.83/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_31,plain,
% 2.83/1.02      ( v1_funct_1(X0) != iProver_top
% 2.83/1.02      | v1_relat_1(X0) != iProver_top
% 2.83/1.02      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 2.83/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_33,plain,
% 2.83/1.02      ( v1_funct_1(sK0) != iProver_top
% 2.83/1.02      | v1_relat_1(k2_funct_1(sK0)) = iProver_top
% 2.83/1.02      | v1_relat_1(sK0) != iProver_top ),
% 2.83/1.02      inference(instantiation,[status(thm)],[c_31]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_1695,plain,
% 2.83/1.02      ( v1_relat_1(X1) != iProver_top
% 2.83/1.02      | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))
% 2.83/1.02      | k2_relat_1(sK0) != X0 ),
% 2.83/1.02      inference(global_propositional_subsumption,
% 2.83/1.02                [status(thm)],
% 2.83/1.02                [c_1602,c_16,c_17,c_33]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_1696,plain,
% 2.83/1.02      ( k2_relat_1(sK0) != X0
% 2.83/1.02      | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))
% 2.83/1.02      | v1_relat_1(X1) != iProver_top ),
% 2.83/1.02      inference(renaming,[status(thm)],[c_1695]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_1704,plain,
% 2.83/1.02      ( k1_relat_1(k5_relat_1(X0,k6_relat_1(k2_relat_1(sK0)))) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
% 2.83/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.83/1.02      inference(equality_resolution,[status(thm)],[c_1696]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_2109,plain,
% 2.83/1.02      ( k1_relat_1(k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
% 2.83/1.02      inference(superposition,[status(thm)],[c_434,c_1704]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_5,plain,
% 2.83/1.02      ( ~ v1_relat_1(X0)
% 2.83/1.02      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 2.83/1.02      inference(cnf_transformation,[],[f30]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_440,plain,
% 2.83/1.02      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 2.83/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.83/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_669,plain,
% 2.83/1.02      ( k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) = sK0 ),
% 2.83/1.02      inference(superposition,[status(thm)],[c_434,c_440]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_2111,plain,
% 2.83/1.02      ( k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(sK0) ),
% 2.83/1.02      inference(light_normalisation,[status(thm)],[c_2109,c_669]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_12,negated_conjecture,
% 2.83/1.02      ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
% 2.83/1.02      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
% 2.83/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_2126,plain,
% 2.83/1.02      ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) != k1_relat_1(sK0)
% 2.83/1.02      | k1_relat_1(sK0) != k1_relat_1(sK0) ),
% 2.83/1.02      inference(demodulation,[status(thm)],[c_2111,c_12]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_246,plain,( X0 = X0 ),theory(equality) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_263,plain,
% 2.83/1.02      ( sK0 = sK0 ),
% 2.83/1.02      inference(instantiation,[status(thm)],[c_246]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_249,plain,
% 2.83/1.02      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 2.83/1.02      theory(equality) ).
% 2.83/1.02  
% 2.83/1.02  cnf(c_256,plain,
% 2.83/1.02      ( k1_relat_1(sK0) = k1_relat_1(sK0) | sK0 != sK0 ),
% 2.83/1.02      inference(instantiation,[status(thm)],[c_249]) ).
% 2.83/1.02  
% 2.83/1.02  cnf(contradiction,plain,
% 2.83/1.02      ( $false ),
% 2.83/1.02      inference(minisat,[status(thm)],[c_4229,c_2126,c_263,c_256,c_16]) ).
% 2.83/1.02  
% 2.83/1.02  
% 2.83/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.83/1.02  
% 2.83/1.02  ------                               Statistics
% 2.83/1.02  
% 2.83/1.02  ------ General
% 2.83/1.02  
% 2.83/1.02  abstr_ref_over_cycles:                  0
% 2.83/1.02  abstr_ref_under_cycles:                 0
% 2.83/1.02  gc_basic_clause_elim:                   0
% 2.83/1.02  forced_gc_time:                         0
% 2.83/1.02  parsing_time:                           0.021
% 2.83/1.02  unif_index_cands_time:                  0.
% 2.83/1.02  unif_index_add_time:                    0.
% 2.83/1.02  orderings_time:                         0.
% 2.83/1.02  out_proof_time:                         0.012
% 2.83/1.02  total_time:                             0.198
% 2.83/1.02  num_of_symbols:                         40
% 2.83/1.02  num_of_terms:                           3601
% 2.83/1.02  
% 2.83/1.02  ------ Preprocessing
% 2.83/1.02  
% 2.83/1.02  num_of_splits:                          0
% 2.83/1.02  num_of_split_atoms:                     0
% 2.83/1.02  num_of_reused_defs:                     0
% 2.83/1.02  num_eq_ax_congr_red:                    0
% 2.83/1.02  num_of_sem_filtered_clauses:            1
% 2.83/1.02  num_of_subtypes:                        0
% 2.83/1.02  monotx_restored_types:                  0
% 2.83/1.02  sat_num_of_epr_types:                   0
% 2.83/1.02  sat_num_of_non_cyclic_types:            0
% 2.83/1.02  sat_guarded_non_collapsed_types:        0
% 2.83/1.02  num_pure_diseq_elim:                    0
% 2.83/1.02  simp_replaced_by:                       0
% 2.83/1.02  res_preprocessed:                       80
% 2.83/1.02  prep_upred:                             0
% 2.83/1.02  prep_unflattend:                        2
% 2.83/1.02  smt_new_axioms:                         0
% 2.83/1.02  pred_elim_cands:                        2
% 2.83/1.02  pred_elim:                              1
% 2.83/1.02  pred_elim_cl:                           1
% 2.83/1.02  pred_elim_cycles:                       3
% 2.83/1.02  merged_defs:                            0
% 2.83/1.02  merged_defs_ncl:                        0
% 2.83/1.02  bin_hyper_res:                          0
% 2.83/1.02  prep_cycles:                            4
% 2.83/1.02  pred_elim_time:                         0.
% 2.83/1.02  splitting_time:                         0.
% 2.83/1.02  sem_filter_time:                        0.
% 2.83/1.02  monotx_time:                            0.
% 2.83/1.02  subtype_inf_time:                       0.
% 2.83/1.02  
% 2.83/1.02  ------ Problem properties
% 2.83/1.02  
% 2.83/1.02  clauses:                                15
% 2.83/1.02  conjectures:                            3
% 2.83/1.02  epr:                                    2
% 2.83/1.02  horn:                                   15
% 2.83/1.02  ground:                                 5
% 2.83/1.02  unary:                                  8
% 2.83/1.02  binary:                                 3
% 2.83/1.02  lits:                                   30
% 2.83/1.02  lits_eq:                                12
% 2.83/1.02  fd_pure:                                0
% 2.83/1.02  fd_pseudo:                              0
% 2.83/1.02  fd_cond:                                0
% 2.83/1.02  fd_pseudo_cond:                         0
% 2.83/1.02  ac_symbols:                             0
% 2.83/1.02  
% 2.83/1.02  ------ Propositional Solver
% 2.83/1.02  
% 2.83/1.02  prop_solver_calls:                      29
% 2.83/1.02  prop_fast_solver_calls:                 569
% 2.83/1.02  smt_solver_calls:                       0
% 2.83/1.02  smt_fast_solver_calls:                  0
% 2.83/1.02  prop_num_of_clauses:                    1429
% 2.83/1.02  prop_preprocess_simplified:             4157
% 2.83/1.02  prop_fo_subsumed:                       21
% 2.83/1.02  prop_solver_time:                       0.
% 2.83/1.02  smt_solver_time:                        0.
% 2.83/1.02  smt_fast_solver_time:                   0.
% 2.83/1.02  prop_fast_solver_time:                  0.
% 2.83/1.02  prop_unsat_core_time:                   0.
% 2.83/1.02  
% 2.83/1.02  ------ QBF
% 2.83/1.02  
% 2.83/1.02  qbf_q_res:                              0
% 2.83/1.02  qbf_num_tautologies:                    0
% 2.83/1.02  qbf_prep_cycles:                        0
% 2.83/1.02  
% 2.83/1.02  ------ BMC1
% 2.83/1.02  
% 2.83/1.02  bmc1_current_bound:                     -1
% 2.83/1.02  bmc1_last_solved_bound:                 -1
% 2.83/1.02  bmc1_unsat_core_size:                   -1
% 2.83/1.02  bmc1_unsat_core_parents_size:           -1
% 2.83/1.02  bmc1_merge_next_fun:                    0
% 2.83/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.83/1.02  
% 2.83/1.02  ------ Instantiation
% 2.83/1.02  
% 2.83/1.02  inst_num_of_clauses:                    719
% 2.83/1.02  inst_num_in_passive:                    148
% 2.83/1.02  inst_num_in_active:                     326
% 2.83/1.02  inst_num_in_unprocessed:                245
% 2.83/1.02  inst_num_of_loops:                      330
% 2.83/1.02  inst_num_of_learning_restarts:          0
% 2.83/1.02  inst_num_moves_active_passive:          0
% 2.83/1.02  inst_lit_activity:                      0
% 2.83/1.02  inst_lit_activity_moves:                0
% 2.83/1.02  inst_num_tautologies:                   0
% 2.83/1.02  inst_num_prop_implied:                  0
% 2.83/1.02  inst_num_existing_simplified:           0
% 2.83/1.02  inst_num_eq_res_simplified:             0
% 2.83/1.02  inst_num_child_elim:                    0
% 2.83/1.02  inst_num_of_dismatching_blockings:      414
% 2.83/1.02  inst_num_of_non_proper_insts:           811
% 2.83/1.02  inst_num_of_duplicates:                 0
% 2.83/1.02  inst_inst_num_from_inst_to_res:         0
% 2.83/1.02  inst_dismatching_checking_time:         0.
% 2.83/1.02  
% 2.83/1.02  ------ Resolution
% 2.83/1.02  
% 2.83/1.02  res_num_of_clauses:                     0
% 2.83/1.02  res_num_in_passive:                     0
% 2.83/1.02  res_num_in_active:                      0
% 2.83/1.02  res_num_of_loops:                       84
% 2.83/1.02  res_forward_subset_subsumed:            119
% 2.83/1.02  res_backward_subset_subsumed:           2
% 2.83/1.02  res_forward_subsumed:                   0
% 2.83/1.02  res_backward_subsumed:                  0
% 2.83/1.02  res_forward_subsumption_resolution:     0
% 2.83/1.02  res_backward_subsumption_resolution:    0
% 2.83/1.02  res_clause_to_clause_subsumption:       286
% 2.83/1.02  res_orphan_elimination:                 0
% 2.83/1.02  res_tautology_del:                      98
% 2.83/1.02  res_num_eq_res_simplified:              0
% 2.83/1.02  res_num_sel_changes:                    0
% 2.83/1.02  res_moves_from_active_to_pass:          0
% 2.83/1.02  
% 2.83/1.02  ------ Superposition
% 2.83/1.02  
% 2.83/1.02  sup_time_total:                         0.
% 2.83/1.02  sup_time_generating:                    0.
% 2.83/1.02  sup_time_sim_full:                      0.
% 2.83/1.02  sup_time_sim_immed:                     0.
% 2.83/1.02  
% 2.83/1.02  sup_num_of_clauses:                     102
% 2.83/1.02  sup_num_in_active:                      65
% 2.83/1.02  sup_num_in_passive:                     37
% 2.83/1.02  sup_num_of_loops:                       65
% 2.83/1.02  sup_fw_superposition:                   65
% 2.83/1.02  sup_bw_superposition:                   40
% 2.83/1.02  sup_immediate_simplified:               17
% 2.83/1.02  sup_given_eliminated:                   0
% 2.83/1.02  comparisons_done:                       0
% 2.83/1.02  comparisons_avoided:                    0
% 2.83/1.02  
% 2.83/1.02  ------ Simplifications
% 2.83/1.02  
% 2.83/1.02  
% 2.83/1.02  sim_fw_subset_subsumed:                 4
% 2.83/1.02  sim_bw_subset_subsumed:                 0
% 2.83/1.02  sim_fw_subsumed:                        5
% 2.83/1.02  sim_bw_subsumed:                        0
% 2.83/1.02  sim_fw_subsumption_res:                 4
% 2.83/1.02  sim_bw_subsumption_res:                 0
% 2.83/1.02  sim_tautology_del:                      0
% 2.83/1.02  sim_eq_tautology_del:                   8
% 2.83/1.02  sim_eq_res_simp:                        3
% 2.83/1.02  sim_fw_demodulated:                     2
% 2.83/1.02  sim_bw_demodulated:                     1
% 2.83/1.02  sim_light_normalised:                   13
% 2.83/1.02  sim_joinable_taut:                      0
% 2.83/1.02  sim_joinable_simp:                      0
% 2.83/1.02  sim_ac_normalised:                      0
% 2.83/1.02  sim_smt_subsumption:                    0
% 2.83/1.02  
%------------------------------------------------------------------------------
