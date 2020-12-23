%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:38 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 313 expanded)
%              Number of clauses        :   65 ( 101 expanded)
%              Number of leaves         :   13 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  297 (1237 expanded)
%              Number of equality atoms :  175 ( 523 expanded)
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
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) != k2_relat_1(X0) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) != k2_relat_1(X0) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,
    ( ? [X0] :
        ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) != k2_relat_1(X0) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
        | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f36,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

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

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

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

fof(f34,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

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

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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

fof(f30,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_403,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_404,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_405,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_relat_1(X1) != k1_relat_1(X2)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_410,plain,
    ( k1_relat_1(X0) != k1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1265,plain,
    ( k1_relat_1(X0) != X1
    | k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X2,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_410])).

cnf(c_0,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_411,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1461,plain,
    ( k1_relat_1(X0) != X1
    | k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X2,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1265,c_411])).

cnf(c_1467,plain,
    ( k1_relat_1(k5_relat_1(X0,k6_relat_1(k1_relat_1(X1)))) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1461])).

cnf(c_6036,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X0),k6_relat_1(k1_relat_1(X1)))) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X1))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_405,c_1467])).

cnf(c_7442,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0)))) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_404,c_6036])).

cnf(c_15,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7466,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0)))) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7442,c_15])).

cnf(c_7467,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0)))) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7466])).

cnf(c_7474,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(superposition,[status(thm)],[c_403,c_7467])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_12,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_144,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_145,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_144])).

cnf(c_19,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_147,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_145,c_14,c_13,c_12,c_19])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_407,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_649,plain,
    ( k5_relat_1(k2_funct_1(X0),k6_relat_1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_405,c_407])).

cnf(c_861,plain,
    ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) = k2_funct_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_404,c_649])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_152,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_12])).

cnf(c_153,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_152])).

cnf(c_22,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_155,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_153,c_14,c_13,c_12,c_22])).

cnf(c_864,plain,
    ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k2_funct_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_861,c_155])).

cnf(c_908,plain,
    ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k2_funct_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_864,c_15])).

cnf(c_7476,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_7474,c_147,c_908])).

cnf(c_3,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k2_relat_1(X1) != k2_relat_1(X2)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(k5_relat_1(X2,X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_409,plain,
    ( k2_relat_1(X0) != k2_relat_1(X1)
    | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1127,plain,
    ( k2_relat_1(X0) != X1
    | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_409])).

cnf(c_1300,plain,
    ( k2_relat_1(X0) != X1
    | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1127,c_411])).

cnf(c_1305,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
    | k1_relat_1(sK0) != X0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_155,c_1300])).

cnf(c_16,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_24,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_26,plain,
    ( v1_funct_1(sK0) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1567,plain,
    ( v1_relat_1(X1) != iProver_top
    | k1_relat_1(sK0) != X0
    | k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1305,c_15,c_16,c_26])).

cnf(c_1568,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
    | k1_relat_1(sK0) != X0
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1567])).

cnf(c_1576,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1568])).

cnf(c_1741,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(superposition,[status(thm)],[c_403,c_1576])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_408,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_712,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_403,c_408])).

cnf(c_1743,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_1741,c_712])).

cnf(c_230,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_495,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != X0
    | k2_relat_1(sK0) != X0
    | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_502,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(X0)
    | k2_relat_1(sK0) != k2_relat_1(X0)
    | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_504,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)
    | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_502])).

cnf(c_229,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_246,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_235,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_242,plain,
    ( k2_relat_1(sK0) = k2_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(c_11,negated_conjecture,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7476,c_1743,c_504,c_246,c_242,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n007.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 10:30:21 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 3.26/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/0.97  
% 3.26/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.26/0.97  
% 3.26/0.97  ------  iProver source info
% 3.26/0.97  
% 3.26/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.26/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.26/0.97  git: non_committed_changes: false
% 3.26/0.97  git: last_make_outside_of_git: false
% 3.26/0.97  
% 3.26/0.97  ------ 
% 3.26/0.97  
% 3.26/0.97  ------ Input Options
% 3.26/0.97  
% 3.26/0.97  --out_options                           all
% 3.26/0.97  --tptp_safe_out                         true
% 3.26/0.97  --problem_path                          ""
% 3.26/0.97  --include_path                          ""
% 3.26/0.97  --clausifier                            res/vclausify_rel
% 3.26/0.97  --clausifier_options                    --mode clausify
% 3.26/0.97  --stdin                                 false
% 3.26/0.97  --stats_out                             all
% 3.26/0.97  
% 3.26/0.97  ------ General Options
% 3.26/0.97  
% 3.26/0.97  --fof                                   false
% 3.26/0.97  --time_out_real                         305.
% 3.26/0.97  --time_out_virtual                      -1.
% 3.26/0.97  --symbol_type_check                     false
% 3.26/0.97  --clausify_out                          false
% 3.26/0.97  --sig_cnt_out                           false
% 3.26/0.97  --trig_cnt_out                          false
% 3.26/0.97  --trig_cnt_out_tolerance                1.
% 3.26/0.97  --trig_cnt_out_sk_spl                   false
% 3.26/0.97  --abstr_cl_out                          false
% 3.26/0.97  
% 3.26/0.97  ------ Global Options
% 3.26/0.97  
% 3.26/0.97  --schedule                              default
% 3.26/0.97  --add_important_lit                     false
% 3.26/0.97  --prop_solver_per_cl                    1000
% 3.26/0.97  --min_unsat_core                        false
% 3.26/0.97  --soft_assumptions                      false
% 3.26/0.97  --soft_lemma_size                       3
% 3.26/0.97  --prop_impl_unit_size                   0
% 3.26/0.97  --prop_impl_unit                        []
% 3.26/0.97  --share_sel_clauses                     true
% 3.26/0.97  --reset_solvers                         false
% 3.26/0.97  --bc_imp_inh                            [conj_cone]
% 3.26/0.97  --conj_cone_tolerance                   3.
% 3.26/0.97  --extra_neg_conj                        none
% 3.26/0.97  --large_theory_mode                     true
% 3.26/0.97  --prolific_symb_bound                   200
% 3.26/0.97  --lt_threshold                          2000
% 3.26/0.97  --clause_weak_htbl                      true
% 3.26/0.97  --gc_record_bc_elim                     false
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing Options
% 3.26/0.97  
% 3.26/0.97  --preprocessing_flag                    true
% 3.26/0.97  --time_out_prep_mult                    0.1
% 3.26/0.97  --splitting_mode                        input
% 3.26/0.97  --splitting_grd                         true
% 3.26/0.97  --splitting_cvd                         false
% 3.26/0.97  --splitting_cvd_svl                     false
% 3.26/0.97  --splitting_nvd                         32
% 3.26/0.97  --sub_typing                            true
% 3.26/0.97  --prep_gs_sim                           true
% 3.26/0.97  --prep_unflatten                        true
% 3.26/0.97  --prep_res_sim                          true
% 3.26/0.97  --prep_upred                            true
% 3.26/0.97  --prep_sem_filter                       exhaustive
% 3.26/0.97  --prep_sem_filter_out                   false
% 3.26/0.97  --pred_elim                             true
% 3.26/0.97  --res_sim_input                         true
% 3.26/0.97  --eq_ax_congr_red                       true
% 3.26/0.97  --pure_diseq_elim                       true
% 3.26/0.97  --brand_transform                       false
% 3.26/0.97  --non_eq_to_eq                          false
% 3.26/0.97  --prep_def_merge                        true
% 3.26/0.97  --prep_def_merge_prop_impl              false
% 3.26/0.97  --prep_def_merge_mbd                    true
% 3.26/0.97  --prep_def_merge_tr_red                 false
% 3.26/0.97  --prep_def_merge_tr_cl                  false
% 3.26/0.97  --smt_preprocessing                     true
% 3.26/0.97  --smt_ac_axioms                         fast
% 3.26/0.97  --preprocessed_out                      false
% 3.26/0.97  --preprocessed_stats                    false
% 3.26/0.97  
% 3.26/0.97  ------ Abstraction refinement Options
% 3.26/0.97  
% 3.26/0.97  --abstr_ref                             []
% 3.26/0.97  --abstr_ref_prep                        false
% 3.26/0.97  --abstr_ref_until_sat                   false
% 3.26/0.97  --abstr_ref_sig_restrict                funpre
% 3.26/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.97  --abstr_ref_under                       []
% 3.26/0.97  
% 3.26/0.97  ------ SAT Options
% 3.26/0.97  
% 3.26/0.97  --sat_mode                              false
% 3.26/0.97  --sat_fm_restart_options                ""
% 3.26/0.97  --sat_gr_def                            false
% 3.26/0.97  --sat_epr_types                         true
% 3.26/0.97  --sat_non_cyclic_types                  false
% 3.26/0.97  --sat_finite_models                     false
% 3.26/0.97  --sat_fm_lemmas                         false
% 3.26/0.97  --sat_fm_prep                           false
% 3.26/0.97  --sat_fm_uc_incr                        true
% 3.26/0.97  --sat_out_model                         small
% 3.26/0.97  --sat_out_clauses                       false
% 3.26/0.97  
% 3.26/0.97  ------ QBF Options
% 3.26/0.97  
% 3.26/0.97  --qbf_mode                              false
% 3.26/0.97  --qbf_elim_univ                         false
% 3.26/0.97  --qbf_dom_inst                          none
% 3.26/0.97  --qbf_dom_pre_inst                      false
% 3.26/0.97  --qbf_sk_in                             false
% 3.26/0.97  --qbf_pred_elim                         true
% 3.26/0.97  --qbf_split                             512
% 3.26/0.97  
% 3.26/0.97  ------ BMC1 Options
% 3.26/0.97  
% 3.26/0.97  --bmc1_incremental                      false
% 3.26/0.97  --bmc1_axioms                           reachable_all
% 3.26/0.97  --bmc1_min_bound                        0
% 3.26/0.97  --bmc1_max_bound                        -1
% 3.26/0.97  --bmc1_max_bound_default                -1
% 3.26/0.97  --bmc1_symbol_reachability              true
% 3.26/0.97  --bmc1_property_lemmas                  false
% 3.26/0.97  --bmc1_k_induction                      false
% 3.26/0.97  --bmc1_non_equiv_states                 false
% 3.26/0.97  --bmc1_deadlock                         false
% 3.26/0.97  --bmc1_ucm                              false
% 3.26/0.97  --bmc1_add_unsat_core                   none
% 3.26/0.97  --bmc1_unsat_core_children              false
% 3.26/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.97  --bmc1_out_stat                         full
% 3.26/0.97  --bmc1_ground_init                      false
% 3.26/0.97  --bmc1_pre_inst_next_state              false
% 3.26/0.97  --bmc1_pre_inst_state                   false
% 3.26/0.97  --bmc1_pre_inst_reach_state             false
% 3.26/0.97  --bmc1_out_unsat_core                   false
% 3.26/0.97  --bmc1_aig_witness_out                  false
% 3.26/0.97  --bmc1_verbose                          false
% 3.26/0.97  --bmc1_dump_clauses_tptp                false
% 3.26/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.97  --bmc1_dump_file                        -
% 3.26/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.97  --bmc1_ucm_extend_mode                  1
% 3.26/0.97  --bmc1_ucm_init_mode                    2
% 3.26/0.97  --bmc1_ucm_cone_mode                    none
% 3.26/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.97  --bmc1_ucm_relax_model                  4
% 3.26/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.97  --bmc1_ucm_layered_model                none
% 3.26/0.97  --bmc1_ucm_max_lemma_size               10
% 3.26/0.97  
% 3.26/0.97  ------ AIG Options
% 3.26/0.97  
% 3.26/0.97  --aig_mode                              false
% 3.26/0.97  
% 3.26/0.97  ------ Instantiation Options
% 3.26/0.97  
% 3.26/0.97  --instantiation_flag                    true
% 3.26/0.97  --inst_sos_flag                         false
% 3.26/0.97  --inst_sos_phase                        true
% 3.26/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.97  --inst_lit_sel_side                     num_symb
% 3.26/0.97  --inst_solver_per_active                1400
% 3.26/0.97  --inst_solver_calls_frac                1.
% 3.26/0.97  --inst_passive_queue_type               priority_queues
% 3.26/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.97  --inst_passive_queues_freq              [25;2]
% 3.26/0.97  --inst_dismatching                      true
% 3.26/0.97  --inst_eager_unprocessed_to_passive     true
% 3.26/0.97  --inst_prop_sim_given                   true
% 3.26/0.97  --inst_prop_sim_new                     false
% 3.26/0.97  --inst_subs_new                         false
% 3.26/0.97  --inst_eq_res_simp                      false
% 3.26/0.97  --inst_subs_given                       false
% 3.26/0.97  --inst_orphan_elimination               true
% 3.26/0.97  --inst_learning_loop_flag               true
% 3.26/0.97  --inst_learning_start                   3000
% 3.26/0.97  --inst_learning_factor                  2
% 3.26/0.97  --inst_start_prop_sim_after_learn       3
% 3.26/0.97  --inst_sel_renew                        solver
% 3.26/0.97  --inst_lit_activity_flag                true
% 3.26/0.97  --inst_restr_to_given                   false
% 3.26/0.97  --inst_activity_threshold               500
% 3.26/0.97  --inst_out_proof                        true
% 3.26/0.97  
% 3.26/0.97  ------ Resolution Options
% 3.26/0.97  
% 3.26/0.97  --resolution_flag                       true
% 3.26/0.97  --res_lit_sel                           adaptive
% 3.26/0.97  --res_lit_sel_side                      none
% 3.26/0.97  --res_ordering                          kbo
% 3.26/0.97  --res_to_prop_solver                    active
% 3.26/0.97  --res_prop_simpl_new                    false
% 3.26/0.97  --res_prop_simpl_given                  true
% 3.26/0.97  --res_passive_queue_type                priority_queues
% 3.26/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.97  --res_passive_queues_freq               [15;5]
% 3.26/0.97  --res_forward_subs                      full
% 3.26/0.97  --res_backward_subs                     full
% 3.26/0.97  --res_forward_subs_resolution           true
% 3.26/0.97  --res_backward_subs_resolution          true
% 3.26/0.97  --res_orphan_elimination                true
% 3.26/0.97  --res_time_limit                        2.
% 3.26/0.97  --res_out_proof                         true
% 3.26/0.97  
% 3.26/0.97  ------ Superposition Options
% 3.26/0.97  
% 3.26/0.97  --superposition_flag                    true
% 3.26/0.97  --sup_passive_queue_type                priority_queues
% 3.26/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.97  --demod_completeness_check              fast
% 3.26/0.97  --demod_use_ground                      true
% 3.26/0.97  --sup_to_prop_solver                    passive
% 3.26/0.97  --sup_prop_simpl_new                    true
% 3.26/0.97  --sup_prop_simpl_given                  true
% 3.26/0.97  --sup_fun_splitting                     false
% 3.26/0.97  --sup_smt_interval                      50000
% 3.26/0.97  
% 3.26/0.97  ------ Superposition Simplification Setup
% 3.26/0.97  
% 3.26/0.97  --sup_indices_passive                   []
% 3.26/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.97  --sup_full_bw                           [BwDemod]
% 3.26/0.97  --sup_immed_triv                        [TrivRules]
% 3.26/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.97  --sup_immed_bw_main                     []
% 3.26/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.97  
% 3.26/0.97  ------ Combination Options
% 3.26/0.97  
% 3.26/0.97  --comb_res_mult                         3
% 3.26/0.97  --comb_sup_mult                         2
% 3.26/0.97  --comb_inst_mult                        10
% 3.26/0.97  
% 3.26/0.97  ------ Debug Options
% 3.26/0.97  
% 3.26/0.97  --dbg_backtrace                         false
% 3.26/0.97  --dbg_dump_prop_clauses                 false
% 3.26/0.97  --dbg_dump_prop_clauses_file            -
% 3.26/0.97  --dbg_out_stat                          false
% 3.26/0.97  ------ Parsing...
% 3.26/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.26/0.97  ------ Proving...
% 3.26/0.97  ------ Problem Properties 
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  clauses                                 14
% 3.26/0.97  conjectures                             3
% 3.26/0.97  EPR                                     2
% 3.26/0.97  Horn                                    14
% 3.26/0.97  unary                                   7
% 3.26/0.97  binary                                  3
% 3.26/0.97  lits                                    29
% 3.26/0.97  lits eq                                 12
% 3.26/0.97  fd_pure                                 0
% 3.26/0.97  fd_pseudo                               0
% 3.26/0.97  fd_cond                                 0
% 3.26/0.97  fd_pseudo_cond                          0
% 3.26/0.97  AC symbols                              0
% 3.26/0.97  
% 3.26/0.97  ------ Schedule dynamic 5 is on 
% 3.26/0.97  
% 3.26/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.26/0.97  
% 3.26/0.97  
% 3.26/0.97  ------ 
% 3.26/0.97  Current options:
% 3.26/0.97  ------ 
% 3.26/0.97  
% 3.26/0.97  ------ Input Options
% 3.26/0.97  
% 3.26/0.97  --out_options                           all
% 3.26/0.97  --tptp_safe_out                         true
% 3.26/0.97  --problem_path                          ""
% 3.26/0.97  --include_path                          ""
% 3.26/0.97  --clausifier                            res/vclausify_rel
% 3.26/0.97  --clausifier_options                    --mode clausify
% 3.26/0.97  --stdin                                 false
% 3.26/0.97  --stats_out                             all
% 3.26/0.97  
% 3.26/0.97  ------ General Options
% 3.26/0.97  
% 3.26/0.97  --fof                                   false
% 3.26/0.97  --time_out_real                         305.
% 3.26/0.97  --time_out_virtual                      -1.
% 3.26/0.97  --symbol_type_check                     false
% 3.26/0.97  --clausify_out                          false
% 3.26/0.97  --sig_cnt_out                           false
% 3.26/0.97  --trig_cnt_out                          false
% 3.26/0.97  --trig_cnt_out_tolerance                1.
% 3.26/0.97  --trig_cnt_out_sk_spl                   false
% 3.26/0.97  --abstr_cl_out                          false
% 3.26/0.97  
% 3.26/0.97  ------ Global Options
% 3.26/0.97  
% 3.26/0.97  --schedule                              default
% 3.26/0.97  --add_important_lit                     false
% 3.26/0.97  --prop_solver_per_cl                    1000
% 3.26/0.97  --min_unsat_core                        false
% 3.26/0.97  --soft_assumptions                      false
% 3.26/0.97  --soft_lemma_size                       3
% 3.26/0.97  --prop_impl_unit_size                   0
% 3.26/0.97  --prop_impl_unit                        []
% 3.26/0.97  --share_sel_clauses                     true
% 3.26/0.97  --reset_solvers                         false
% 3.26/0.97  --bc_imp_inh                            [conj_cone]
% 3.26/0.97  --conj_cone_tolerance                   3.
% 3.26/0.97  --extra_neg_conj                        none
% 3.26/0.97  --large_theory_mode                     true
% 3.26/0.97  --prolific_symb_bound                   200
% 3.26/0.97  --lt_threshold                          2000
% 3.26/0.97  --clause_weak_htbl                      true
% 3.26/0.97  --gc_record_bc_elim                     false
% 3.26/0.97  
% 3.26/0.97  ------ Preprocessing Options
% 3.26/0.97  
% 3.26/0.97  --preprocessing_flag                    true
% 3.26/0.97  --time_out_prep_mult                    0.1
% 3.26/0.97  --splitting_mode                        input
% 3.26/0.97  --splitting_grd                         true
% 3.26/0.97  --splitting_cvd                         false
% 3.26/0.97  --splitting_cvd_svl                     false
% 3.26/0.97  --splitting_nvd                         32
% 3.26/0.97  --sub_typing                            true
% 3.26/0.97  --prep_gs_sim                           true
% 3.26/0.97  --prep_unflatten                        true
% 3.26/0.97  --prep_res_sim                          true
% 3.26/0.97  --prep_upred                            true
% 3.26/0.97  --prep_sem_filter                       exhaustive
% 3.26/0.97  --prep_sem_filter_out                   false
% 3.26/0.97  --pred_elim                             true
% 3.26/0.97  --res_sim_input                         true
% 3.26/0.97  --eq_ax_congr_red                       true
% 3.26/0.97  --pure_diseq_elim                       true
% 3.26/0.97  --brand_transform                       false
% 3.26/0.97  --non_eq_to_eq                          false
% 3.26/0.97  --prep_def_merge                        true
% 3.26/0.97  --prep_def_merge_prop_impl              false
% 3.26/0.97  --prep_def_merge_mbd                    true
% 3.26/0.97  --prep_def_merge_tr_red                 false
% 3.26/0.97  --prep_def_merge_tr_cl                  false
% 3.26/0.97  --smt_preprocessing                     true
% 3.26/0.97  --smt_ac_axioms                         fast
% 3.26/0.97  --preprocessed_out                      false
% 3.26/0.97  --preprocessed_stats                    false
% 3.26/0.97  
% 3.26/0.97  ------ Abstraction refinement Options
% 3.26/0.97  
% 3.26/0.97  --abstr_ref                             []
% 3.26/0.97  --abstr_ref_prep                        false
% 3.26/0.97  --abstr_ref_until_sat                   false
% 3.26/0.97  --abstr_ref_sig_restrict                funpre
% 3.26/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.97  --abstr_ref_under                       []
% 3.26/0.97  
% 3.26/0.97  ------ SAT Options
% 3.26/0.97  
% 3.26/0.97  --sat_mode                              false
% 3.26/0.97  --sat_fm_restart_options                ""
% 3.26/0.97  --sat_gr_def                            false
% 3.26/0.97  --sat_epr_types                         true
% 3.26/0.97  --sat_non_cyclic_types                  false
% 3.26/0.97  --sat_finite_models                     false
% 3.26/0.97  --sat_fm_lemmas                         false
% 3.26/0.97  --sat_fm_prep                           false
% 3.26/0.97  --sat_fm_uc_incr                        true
% 3.26/0.97  --sat_out_model                         small
% 3.26/0.97  --sat_out_clauses                       false
% 3.26/0.97  
% 3.26/0.97  ------ QBF Options
% 3.26/0.97  
% 3.26/0.97  --qbf_mode                              false
% 3.26/0.97  --qbf_elim_univ                         false
% 3.26/0.97  --qbf_dom_inst                          none
% 3.26/0.97  --qbf_dom_pre_inst                      false
% 3.26/0.97  --qbf_sk_in                             false
% 3.26/0.97  --qbf_pred_elim                         true
% 3.26/0.97  --qbf_split                             512
% 3.26/0.97  
% 3.26/0.97  ------ BMC1 Options
% 3.26/0.97  
% 3.26/0.97  --bmc1_incremental                      false
% 3.26/0.97  --bmc1_axioms                           reachable_all
% 3.26/0.97  --bmc1_min_bound                        0
% 3.26/0.97  --bmc1_max_bound                        -1
% 3.26/0.97  --bmc1_max_bound_default                -1
% 3.26/0.97  --bmc1_symbol_reachability              true
% 3.26/0.97  --bmc1_property_lemmas                  false
% 3.26/0.97  --bmc1_k_induction                      false
% 3.26/0.97  --bmc1_non_equiv_states                 false
% 3.26/0.97  --bmc1_deadlock                         false
% 3.26/0.97  --bmc1_ucm                              false
% 3.26/0.97  --bmc1_add_unsat_core                   none
% 3.26/0.97  --bmc1_unsat_core_children              false
% 3.26/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.97  --bmc1_out_stat                         full
% 3.26/0.97  --bmc1_ground_init                      false
% 3.26/0.97  --bmc1_pre_inst_next_state              false
% 3.26/0.97  --bmc1_pre_inst_state                   false
% 3.26/0.97  --bmc1_pre_inst_reach_state             false
% 3.26/0.97  --bmc1_out_unsat_core                   false
% 3.26/0.97  --bmc1_aig_witness_out                  false
% 3.26/0.97  --bmc1_verbose                          false
% 3.26/0.97  --bmc1_dump_clauses_tptp                false
% 3.26/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.97  --bmc1_dump_file                        -
% 3.26/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.97  --bmc1_ucm_extend_mode                  1
% 3.26/0.97  --bmc1_ucm_init_mode                    2
% 3.26/0.97  --bmc1_ucm_cone_mode                    none
% 3.26/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.97  --bmc1_ucm_relax_model                  4
% 3.26/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.97  --bmc1_ucm_layered_model                none
% 3.26/0.97  --bmc1_ucm_max_lemma_size               10
% 3.26/0.97  
% 3.26/0.97  ------ AIG Options
% 3.26/0.97  
% 3.26/0.97  --aig_mode                              false
% 3.26/0.97  
% 3.26/0.97  ------ Instantiation Options
% 3.26/0.97  
% 3.26/0.97  --instantiation_flag                    true
% 3.26/0.97  --inst_sos_flag                         false
% 3.26/0.97  --inst_sos_phase                        true
% 3.26/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.97  --inst_lit_sel_side                     none
% 3.26/0.97  --inst_solver_per_active                1400
% 3.26/0.97  --inst_solver_calls_frac                1.
% 3.26/0.97  --inst_passive_queue_type               priority_queues
% 3.26/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.97  --inst_passive_queues_freq              [25;2]
% 3.26/0.97  --inst_dismatching                      true
% 3.26/0.97  --inst_eager_unprocessed_to_passive     true
% 3.26/0.97  --inst_prop_sim_given                   true
% 3.26/0.97  --inst_prop_sim_new                     false
% 3.26/0.97  --inst_subs_new                         false
% 3.26/0.97  --inst_eq_res_simp                      false
% 3.26/0.97  --inst_subs_given                       false
% 3.26/0.97  --inst_orphan_elimination               true
% 3.26/0.97  --inst_learning_loop_flag               true
% 3.26/0.97  --inst_learning_start                   3000
% 3.26/0.97  --inst_learning_factor                  2
% 3.26/0.97  --inst_start_prop_sim_after_learn       3
% 3.26/0.97  --inst_sel_renew                        solver
% 3.26/0.97  --inst_lit_activity_flag                true
% 3.26/0.97  --inst_restr_to_given                   false
% 3.26/0.97  --inst_activity_threshold               500
% 3.26/0.97  --inst_out_proof                        true
% 3.26/0.97  
% 3.26/0.97  ------ Resolution Options
% 3.26/0.97  
% 3.26/0.97  --resolution_flag                       false
% 3.26/0.97  --res_lit_sel                           adaptive
% 3.26/0.97  --res_lit_sel_side                      none
% 3.26/0.97  --res_ordering                          kbo
% 3.26/0.98  --res_to_prop_solver                    active
% 3.26/0.98  --res_prop_simpl_new                    false
% 3.26/0.98  --res_prop_simpl_given                  true
% 3.26/0.98  --res_passive_queue_type                priority_queues
% 3.26/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.98  --res_passive_queues_freq               [15;5]
% 3.26/0.98  --res_forward_subs                      full
% 3.26/0.98  --res_backward_subs                     full
% 3.26/0.98  --res_forward_subs_resolution           true
% 3.26/0.98  --res_backward_subs_resolution          true
% 3.26/0.98  --res_orphan_elimination                true
% 3.26/0.98  --res_time_limit                        2.
% 3.26/0.98  --res_out_proof                         true
% 3.26/0.98  
% 3.26/0.98  ------ Superposition Options
% 3.26/0.98  
% 3.26/0.98  --superposition_flag                    true
% 3.26/0.98  --sup_passive_queue_type                priority_queues
% 3.26/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.98  --demod_completeness_check              fast
% 3.26/0.98  --demod_use_ground                      true
% 3.26/0.98  --sup_to_prop_solver                    passive
% 3.26/0.98  --sup_prop_simpl_new                    true
% 3.26/0.98  --sup_prop_simpl_given                  true
% 3.26/0.98  --sup_fun_splitting                     false
% 3.26/0.98  --sup_smt_interval                      50000
% 3.26/0.98  
% 3.26/0.98  ------ Superposition Simplification Setup
% 3.26/0.98  
% 3.26/0.98  --sup_indices_passive                   []
% 3.26/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.98  --sup_full_bw                           [BwDemod]
% 3.26/0.98  --sup_immed_triv                        [TrivRules]
% 3.26/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.98  --sup_immed_bw_main                     []
% 3.26/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.98  
% 3.26/0.98  ------ Combination Options
% 3.26/0.98  
% 3.26/0.98  --comb_res_mult                         3
% 3.26/0.98  --comb_sup_mult                         2
% 3.26/0.98  --comb_inst_mult                        10
% 3.26/0.98  
% 3.26/0.98  ------ Debug Options
% 3.26/0.98  
% 3.26/0.98  --dbg_backtrace                         false
% 3.26/0.98  --dbg_dump_prop_clauses                 false
% 3.26/0.98  --dbg_dump_prop_clauses_file            -
% 3.26/0.98  --dbg_out_stat                          false
% 3.26/0.98  
% 3.26/0.98  
% 3.26/0.98  
% 3.26/0.98  
% 3.26/0.98  ------ Proving...
% 3.26/0.98  
% 3.26/0.98  
% 3.26/0.98  % SZS status Theorem for theBenchmark.p
% 3.26/0.98  
% 3.26/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.26/0.98  
% 3.26/0.98  fof(f9,conjecture,(
% 3.26/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f10,negated_conjecture,(
% 3.26/0.98    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 3.26/0.98    inference(negated_conjecture,[],[f9])).
% 3.26/0.98  
% 3.26/0.98  fof(f21,plain,(
% 3.26/0.98    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) != k2_relat_1(X0)) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.26/0.98    inference(ennf_transformation,[],[f10])).
% 3.26/0.98  
% 3.26/0.98  fof(f22,plain,(
% 3.26/0.98    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) != k2_relat_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.26/0.98    inference(flattening,[],[f21])).
% 3.26/0.98  
% 3.26/0.98  fof(f23,plain,(
% 3.26/0.98    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) != k2_relat_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 3.26/0.98    introduced(choice_axiom,[])).
% 3.26/0.98  
% 3.26/0.98  fof(f24,plain,(
% 3.26/0.98    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 3.26/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 3.26/0.98  
% 3.26/0.98  fof(f36,plain,(
% 3.26/0.98    v1_relat_1(sK0)),
% 3.26/0.98    inference(cnf_transformation,[],[f24])).
% 3.26/0.98  
% 3.26/0.98  fof(f37,plain,(
% 3.26/0.98    v1_funct_1(sK0)),
% 3.26/0.98    inference(cnf_transformation,[],[f24])).
% 3.26/0.98  
% 3.26/0.98  fof(f7,axiom,(
% 3.26/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f17,plain,(
% 3.26/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.26/0.98    inference(ennf_transformation,[],[f7])).
% 3.26/0.98  
% 3.26/0.98  fof(f18,plain,(
% 3.26/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.26/0.98    inference(flattening,[],[f17])).
% 3.26/0.98  
% 3.26/0.98  fof(f32,plain,(
% 3.26/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f18])).
% 3.26/0.98  
% 3.26/0.98  fof(f4,axiom,(
% 3.26/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f28,plain,(
% 3.26/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.26/0.98    inference(cnf_transformation,[],[f4])).
% 3.26/0.98  
% 3.26/0.98  fof(f2,axiom,(
% 3.26/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f11,plain,(
% 3.26/0.98    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.26/0.98    inference(ennf_transformation,[],[f2])).
% 3.26/0.98  
% 3.26/0.98  fof(f12,plain,(
% 3.26/0.98    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.26/0.98    inference(flattening,[],[f11])).
% 3.26/0.98  
% 3.26/0.98  fof(f26,plain,(
% 3.26/0.98    ( ! [X2,X0,X1] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f12])).
% 3.26/0.98  
% 3.26/0.98  fof(f1,axiom,(
% 3.26/0.98    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f25,plain,(
% 3.26/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.26/0.98    inference(cnf_transformation,[],[f1])).
% 3.26/0.98  
% 3.26/0.98  fof(f8,axiom,(
% 3.26/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f19,plain,(
% 3.26/0.98    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.26/0.98    inference(ennf_transformation,[],[f8])).
% 3.26/0.98  
% 3.26/0.98  fof(f20,plain,(
% 3.26/0.98    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.26/0.98    inference(flattening,[],[f19])).
% 3.26/0.98  
% 3.26/0.98  fof(f34,plain,(
% 3.26/0.98    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f20])).
% 3.26/0.98  
% 3.26/0.98  fof(f38,plain,(
% 3.26/0.98    v2_funct_1(sK0)),
% 3.26/0.98    inference(cnf_transformation,[],[f24])).
% 3.26/0.98  
% 3.26/0.98  fof(f6,axiom,(
% 3.26/0.98    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f16,plain,(
% 3.26/0.98    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.26/0.98    inference(ennf_transformation,[],[f6])).
% 3.26/0.98  
% 3.26/0.98  fof(f31,plain,(
% 3.26/0.98    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f16])).
% 3.26/0.98  
% 3.26/0.98  fof(f35,plain,(
% 3.26/0.98    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f20])).
% 3.26/0.98  
% 3.26/0.98  fof(f29,plain,(
% 3.26/0.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.26/0.98    inference(cnf_transformation,[],[f4])).
% 3.26/0.98  
% 3.26/0.98  fof(f3,axiom,(
% 3.26/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f13,plain,(
% 3.26/0.98    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.26/0.98    inference(ennf_transformation,[],[f3])).
% 3.26/0.98  
% 3.26/0.98  fof(f14,plain,(
% 3.26/0.98    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.26/0.98    inference(flattening,[],[f13])).
% 3.26/0.98  
% 3.26/0.98  fof(f27,plain,(
% 3.26/0.98    ( ! [X2,X0,X1] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f14])).
% 3.26/0.98  
% 3.26/0.98  fof(f5,axiom,(
% 3.26/0.98    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 3.26/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.98  
% 3.26/0.98  fof(f15,plain,(
% 3.26/0.98    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 3.26/0.98    inference(ennf_transformation,[],[f5])).
% 3.26/0.98  
% 3.26/0.98  fof(f30,plain,(
% 3.26/0.98    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 3.26/0.98    inference(cnf_transformation,[],[f15])).
% 3.26/0.98  
% 3.26/0.98  fof(f39,plain,(
% 3.26/0.98    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)),
% 3.26/0.98    inference(cnf_transformation,[],[f24])).
% 3.26/0.98  
% 3.26/0.98  cnf(c_14,negated_conjecture,
% 3.26/0.98      ( v1_relat_1(sK0) ),
% 3.26/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_403,plain,
% 3.26/0.98      ( v1_relat_1(sK0) = iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_13,negated_conjecture,
% 3.26/0.98      ( v1_funct_1(sK0) ),
% 3.26/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_404,plain,
% 3.26/0.98      ( v1_funct_1(sK0) = iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_8,plain,
% 3.26/0.98      ( ~ v1_funct_1(X0)
% 3.26/0.98      | ~ v1_relat_1(X0)
% 3.26/0.98      | v1_relat_1(k2_funct_1(X0)) ),
% 3.26/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_405,plain,
% 3.26/0.98      ( v1_funct_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_4,plain,
% 3.26/0.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.26/0.98      inference(cnf_transformation,[],[f28]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1,plain,
% 3.26/0.98      ( ~ v1_relat_1(X0)
% 3.26/0.98      | ~ v1_relat_1(X1)
% 3.26/0.98      | ~ v1_relat_1(X2)
% 3.26/0.98      | k1_relat_1(X1) != k1_relat_1(X2)
% 3.26/0.98      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,X2)) ),
% 3.26/0.98      inference(cnf_transformation,[],[f26]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_410,plain,
% 3.26/0.98      ( k1_relat_1(X0) != k1_relat_1(X1)
% 3.26/0.98      | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
% 3.26/0.98      | v1_relat_1(X2) != iProver_top
% 3.26/0.98      | v1_relat_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1265,plain,
% 3.26/0.98      ( k1_relat_1(X0) != X1
% 3.26/0.98      | k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X2,X0))
% 3.26/0.98      | v1_relat_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(X2) != iProver_top
% 3.26/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.26/0.98      inference(superposition,[status(thm)],[c_4,c_410]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_0,plain,
% 3.26/0.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.26/0.98      inference(cnf_transformation,[],[f25]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_411,plain,
% 3.26/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1461,plain,
% 3.26/0.98      ( k1_relat_1(X0) != X1
% 3.26/0.98      | k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X2,X0))
% 3.26/0.98      | v1_relat_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(X2) != iProver_top ),
% 3.26/0.98      inference(forward_subsumption_resolution,
% 3.26/0.98                [status(thm)],
% 3.26/0.98                [c_1265,c_411]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1467,plain,
% 3.26/0.98      ( k1_relat_1(k5_relat_1(X0,k6_relat_1(k1_relat_1(X1)))) = k1_relat_1(k5_relat_1(X0,X1))
% 3.26/0.98      | v1_relat_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.26/0.98      inference(equality_resolution,[status(thm)],[c_1461]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_6036,plain,
% 3.26/0.98      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),k6_relat_1(k1_relat_1(X1)))) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X1))
% 3.26/0.98      | v1_funct_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.26/0.98      inference(superposition,[status(thm)],[c_405,c_1467]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_7442,plain,
% 3.26/0.98      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0)))) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
% 3.26/0.98      | v1_relat_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(sK0) != iProver_top ),
% 3.26/0.98      inference(superposition,[status(thm)],[c_404,c_6036]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_15,plain,
% 3.26/0.98      ( v1_relat_1(sK0) = iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_7466,plain,
% 3.26/0.98      ( v1_relat_1(X0) != iProver_top
% 3.26/0.98      | k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0)))) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) ),
% 3.26/0.98      inference(global_propositional_subsumption,
% 3.26/0.98                [status(thm)],
% 3.26/0.98                [c_7442,c_15]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_7467,plain,
% 3.26/0.98      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0)))) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
% 3.26/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.26/0.98      inference(renaming,[status(thm)],[c_7466]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_7474,plain,
% 3.26/0.98      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
% 3.26/0.98      inference(superposition,[status(thm)],[c_403,c_7467]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_10,plain,
% 3.26/0.98      ( ~ v2_funct_1(X0)
% 3.26/0.98      | ~ v1_funct_1(X0)
% 3.26/0.98      | ~ v1_relat_1(X0)
% 3.26/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.26/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_12,negated_conjecture,
% 3.26/0.98      ( v2_funct_1(sK0) ),
% 3.26/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_144,plain,
% 3.26/0.98      ( ~ v1_funct_1(X0)
% 3.26/0.98      | ~ v1_relat_1(X0)
% 3.26/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.26/0.98      | sK0 != X0 ),
% 3.26/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_12]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_145,plain,
% 3.26/0.98      ( ~ v1_funct_1(sK0)
% 3.26/0.98      | ~ v1_relat_1(sK0)
% 3.26/0.98      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 3.26/0.98      inference(unflattening,[status(thm)],[c_144]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_19,plain,
% 3.26/0.98      ( ~ v2_funct_1(sK0)
% 3.26/0.98      | ~ v1_funct_1(sK0)
% 3.26/0.98      | ~ v1_relat_1(sK0)
% 3.26/0.98      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 3.26/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_147,plain,
% 3.26/0.98      ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 3.26/0.98      inference(global_propositional_subsumption,
% 3.26/0.98                [status(thm)],
% 3.26/0.98                [c_145,c_14,c_13,c_12,c_19]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_6,plain,
% 3.26/0.98      ( ~ v1_relat_1(X0)
% 3.26/0.98      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 3.26/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_407,plain,
% 3.26/0.98      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 3.26/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_649,plain,
% 3.26/0.98      ( k5_relat_1(k2_funct_1(X0),k6_relat_1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
% 3.26/0.98      | v1_funct_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.26/0.98      inference(superposition,[status(thm)],[c_405,c_407]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_861,plain,
% 3.26/0.98      ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) = k2_funct_1(sK0)
% 3.26/0.98      | v1_relat_1(sK0) != iProver_top ),
% 3.26/0.98      inference(superposition,[status(thm)],[c_404,c_649]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_9,plain,
% 3.26/0.98      ( ~ v2_funct_1(X0)
% 3.26/0.98      | ~ v1_funct_1(X0)
% 3.26/0.98      | ~ v1_relat_1(X0)
% 3.26/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.26/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_152,plain,
% 3.26/0.98      ( ~ v1_funct_1(X0)
% 3.26/0.98      | ~ v1_relat_1(X0)
% 3.26/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.26/0.98      | sK0 != X0 ),
% 3.26/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_12]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_153,plain,
% 3.26/0.98      ( ~ v1_funct_1(sK0)
% 3.26/0.98      | ~ v1_relat_1(sK0)
% 3.26/0.98      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 3.26/0.98      inference(unflattening,[status(thm)],[c_152]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_22,plain,
% 3.26/0.98      ( ~ v2_funct_1(sK0)
% 3.26/0.98      | ~ v1_funct_1(sK0)
% 3.26/0.98      | ~ v1_relat_1(sK0)
% 3.26/0.98      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 3.26/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_155,plain,
% 3.26/0.98      ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 3.26/0.98      inference(global_propositional_subsumption,
% 3.26/0.98                [status(thm)],
% 3.26/0.98                [c_153,c_14,c_13,c_12,c_22]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_864,plain,
% 3.26/0.98      ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k2_funct_1(sK0)
% 3.26/0.98      | v1_relat_1(sK0) != iProver_top ),
% 3.26/0.98      inference(light_normalisation,[status(thm)],[c_861,c_155]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_908,plain,
% 3.26/0.98      ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k2_funct_1(sK0) ),
% 3.26/0.98      inference(global_propositional_subsumption,
% 3.26/0.98                [status(thm)],
% 3.26/0.98                [c_864,c_15]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_7476,plain,
% 3.26/0.98      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0) ),
% 3.26/0.98      inference(light_normalisation,[status(thm)],[c_7474,c_147,c_908]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_3,plain,
% 3.26/0.98      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.26/0.98      inference(cnf_transformation,[],[f29]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_2,plain,
% 3.26/0.98      ( ~ v1_relat_1(X0)
% 3.26/0.98      | ~ v1_relat_1(X1)
% 3.26/0.98      | ~ v1_relat_1(X2)
% 3.26/0.98      | k2_relat_1(X1) != k2_relat_1(X2)
% 3.26/0.98      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(k5_relat_1(X2,X0)) ),
% 3.26/0.98      inference(cnf_transformation,[],[f27]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_409,plain,
% 3.26/0.98      ( k2_relat_1(X0) != k2_relat_1(X1)
% 3.26/0.98      | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
% 3.26/0.98      | v1_relat_1(X2) != iProver_top
% 3.26/0.98      | v1_relat_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1127,plain,
% 3.26/0.98      ( k2_relat_1(X0) != X1
% 3.26/0.98      | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
% 3.26/0.98      | v1_relat_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(X2) != iProver_top
% 3.26/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.26/0.98      inference(superposition,[status(thm)],[c_3,c_409]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1300,plain,
% 3.26/0.98      ( k2_relat_1(X0) != X1
% 3.26/0.98      | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
% 3.26/0.98      | v1_relat_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(X2) != iProver_top ),
% 3.26/0.98      inference(forward_subsumption_resolution,
% 3.26/0.98                [status(thm)],
% 3.26/0.98                [c_1127,c_411]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1305,plain,
% 3.26/0.98      ( k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
% 3.26/0.98      | k1_relat_1(sK0) != X0
% 3.26/0.98      | v1_relat_1(X1) != iProver_top
% 3.26/0.98      | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
% 3.26/0.98      inference(superposition,[status(thm)],[c_155,c_1300]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_16,plain,
% 3.26/0.98      ( v1_funct_1(sK0) = iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_24,plain,
% 3.26/0.98      ( v1_funct_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(X0) != iProver_top
% 3.26/0.98      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_26,plain,
% 3.26/0.98      ( v1_funct_1(sK0) != iProver_top
% 3.26/0.98      | v1_relat_1(k2_funct_1(sK0)) = iProver_top
% 3.26/0.98      | v1_relat_1(sK0) != iProver_top ),
% 3.26/0.98      inference(instantiation,[status(thm)],[c_24]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1567,plain,
% 3.26/0.98      ( v1_relat_1(X1) != iProver_top
% 3.26/0.98      | k1_relat_1(sK0) != X0
% 3.26/0.98      | k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1)) ),
% 3.26/0.98      inference(global_propositional_subsumption,
% 3.26/0.98                [status(thm)],
% 3.26/0.98                [c_1305,c_15,c_16,c_26]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1568,plain,
% 3.26/0.98      ( k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
% 3.26/0.98      | k1_relat_1(sK0) != X0
% 3.26/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.26/0.98      inference(renaming,[status(thm)],[c_1567]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1576,plain,
% 3.26/0.98      ( k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
% 3.26/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.26/0.98      inference(equality_resolution,[status(thm)],[c_1568]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1741,plain,
% 3.26/0.98      ( k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
% 3.26/0.98      inference(superposition,[status(thm)],[c_403,c_1576]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_5,plain,
% 3.26/0.98      ( ~ v1_relat_1(X0)
% 3.26/0.98      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
% 3.26/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_408,plain,
% 3.26/0.98      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 3.26/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.26/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_712,plain,
% 3.26/0.98      ( k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) = sK0 ),
% 3.26/0.98      inference(superposition,[status(thm)],[c_403,c_408]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_1743,plain,
% 3.26/0.98      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0) ),
% 3.26/0.98      inference(light_normalisation,[status(thm)],[c_1741,c_712]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_230,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_495,plain,
% 3.26/0.98      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != X0
% 3.26/0.98      | k2_relat_1(sK0) != X0
% 3.26/0.98      | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
% 3.26/0.98      inference(instantiation,[status(thm)],[c_230]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_502,plain,
% 3.26/0.98      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(X0)
% 3.26/0.98      | k2_relat_1(sK0) != k2_relat_1(X0)
% 3.26/0.98      | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
% 3.26/0.98      inference(instantiation,[status(thm)],[c_495]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_504,plain,
% 3.26/0.98      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)
% 3.26/0.98      | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
% 3.26/0.98      | k2_relat_1(sK0) != k2_relat_1(sK0) ),
% 3.26/0.98      inference(instantiation,[status(thm)],[c_502]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_229,plain,( X0 = X0 ),theory(equality) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_246,plain,
% 3.26/0.98      ( sK0 = sK0 ),
% 3.26/0.98      inference(instantiation,[status(thm)],[c_229]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_235,plain,
% 3.26/0.98      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 3.26/0.98      theory(equality) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_242,plain,
% 3.26/0.98      ( k2_relat_1(sK0) = k2_relat_1(sK0) | sK0 != sK0 ),
% 3.26/0.98      inference(instantiation,[status(thm)],[c_235]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(c_11,negated_conjecture,
% 3.26/0.98      ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
% 3.26/0.98      | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0) ),
% 3.26/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.26/0.98  
% 3.26/0.98  cnf(contradiction,plain,
% 3.26/0.98      ( $false ),
% 3.26/0.98      inference(minisat,
% 3.26/0.98                [status(thm)],
% 3.26/0.98                [c_7476,c_1743,c_504,c_246,c_242,c_11]) ).
% 3.26/0.98  
% 3.26/0.98  
% 3.26/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.26/0.98  
% 3.26/0.98  ------                               Statistics
% 3.26/0.98  
% 3.26/0.98  ------ General
% 3.26/0.98  
% 3.26/0.98  abstr_ref_over_cycles:                  0
% 3.26/0.98  abstr_ref_under_cycles:                 0
% 3.26/0.98  gc_basic_clause_elim:                   0
% 3.26/0.98  forced_gc_time:                         0
% 3.26/0.98  parsing_time:                           0.012
% 3.26/0.98  unif_index_cands_time:                  0.
% 3.26/0.98  unif_index_add_time:                    0.
% 3.26/0.98  orderings_time:                         0.
% 3.26/0.98  out_proof_time:                         0.015
% 3.26/0.98  total_time:                             0.35
% 3.26/0.98  num_of_symbols:                         40
% 3.26/0.98  num_of_terms:                           5155
% 3.26/0.98  
% 3.26/0.98  ------ Preprocessing
% 3.26/0.98  
% 3.26/0.98  num_of_splits:                          0
% 3.26/0.98  num_of_split_atoms:                     0
% 3.26/0.98  num_of_reused_defs:                     0
% 3.26/0.98  num_eq_ax_congr_red:                    0
% 3.26/0.98  num_of_sem_filtered_clauses:            1
% 3.26/0.98  num_of_subtypes:                        0
% 3.26/0.98  monotx_restored_types:                  0
% 3.26/0.98  sat_num_of_epr_types:                   0
% 3.26/0.98  sat_num_of_non_cyclic_types:            0
% 3.26/0.98  sat_guarded_non_collapsed_types:        0
% 3.26/0.98  num_pure_diseq_elim:                    0
% 3.26/0.98  simp_replaced_by:                       0
% 3.26/0.98  res_preprocessed:                       76
% 3.26/0.98  prep_upred:                             0
% 3.26/0.98  prep_unflattend:                        2
% 3.26/0.98  smt_new_axioms:                         0
% 3.26/0.98  pred_elim_cands:                        2
% 3.26/0.98  pred_elim:                              1
% 3.26/0.98  pred_elim_cl:                           1
% 3.26/0.98  pred_elim_cycles:                       3
% 3.26/0.98  merged_defs:                            0
% 3.26/0.98  merged_defs_ncl:                        0
% 3.26/0.98  bin_hyper_res:                          0
% 3.26/0.98  prep_cycles:                            4
% 3.26/0.98  pred_elim_time:                         0.
% 3.26/0.98  splitting_time:                         0.
% 3.26/0.98  sem_filter_time:                        0.
% 3.26/0.98  monotx_time:                            0.009
% 3.26/0.98  subtype_inf_time:                       0.
% 3.26/0.98  
% 3.26/0.98  ------ Problem properties
% 3.26/0.98  
% 3.26/0.98  clauses:                                14
% 3.26/0.98  conjectures:                            3
% 3.26/0.98  epr:                                    2
% 3.26/0.98  horn:                                   14
% 3.26/0.98  ground:                                 5
% 3.26/0.98  unary:                                  7
% 3.26/0.98  binary:                                 3
% 3.26/0.98  lits:                                   29
% 3.26/0.98  lits_eq:                                12
% 3.26/0.98  fd_pure:                                0
% 3.26/0.98  fd_pseudo:                              0
% 3.26/0.98  fd_cond:                                0
% 3.26/0.98  fd_pseudo_cond:                         0
% 3.26/0.98  ac_symbols:                             0
% 3.26/0.98  
% 3.26/0.98  ------ Propositional Solver
% 3.26/0.98  
% 3.26/0.98  prop_solver_calls:                      31
% 3.26/0.98  prop_fast_solver_calls:                 720
% 3.26/0.98  smt_solver_calls:                       0
% 3.26/0.98  smt_fast_solver_calls:                  0
% 3.26/0.98  prop_num_of_clauses:                    2202
% 3.26/0.98  prop_preprocess_simplified:             5630
% 3.26/0.98  prop_fo_subsumed:                       25
% 3.26/0.98  prop_solver_time:                       0.
% 3.26/0.98  smt_solver_time:                        0.
% 3.26/0.98  smt_fast_solver_time:                   0.
% 3.26/0.98  prop_fast_solver_time:                  0.
% 3.26/0.98  prop_unsat_core_time:                   0.
% 3.26/0.98  
% 3.26/0.98  ------ QBF
% 3.26/0.98  
% 3.26/0.98  qbf_q_res:                              0
% 3.26/0.98  qbf_num_tautologies:                    0
% 3.26/0.98  qbf_prep_cycles:                        0
% 3.26/0.98  
% 3.26/0.98  ------ BMC1
% 3.26/0.98  
% 3.26/0.98  bmc1_current_bound:                     -1
% 3.26/0.98  bmc1_last_solved_bound:                 -1
% 3.26/0.98  bmc1_unsat_core_size:                   -1
% 3.26/0.98  bmc1_unsat_core_parents_size:           -1
% 3.26/0.98  bmc1_merge_next_fun:                    0
% 3.26/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.26/0.98  
% 3.26/0.98  ------ Instantiation
% 3.26/0.98  
% 3.26/0.98  inst_num_of_clauses:                    1192
% 3.26/0.98  inst_num_in_passive:                    471
% 3.26/0.98  inst_num_in_active:                     495
% 3.26/0.98  inst_num_in_unprocessed:                226
% 3.26/0.98  inst_num_of_loops:                      510
% 3.26/0.98  inst_num_of_learning_restarts:          0
% 3.26/0.98  inst_num_moves_active_passive:          10
% 3.26/0.98  inst_lit_activity:                      0
% 3.26/0.98  inst_lit_activity_moves:                0
% 3.26/0.98  inst_num_tautologies:                   0
% 3.26/0.98  inst_num_prop_implied:                  0
% 3.26/0.98  inst_num_existing_simplified:           0
% 3.26/0.98  inst_num_eq_res_simplified:             0
% 3.26/0.98  inst_num_child_elim:                    0
% 3.26/0.98  inst_num_of_dismatching_blockings:      834
% 3.26/0.98  inst_num_of_non_proper_insts:           1596
% 3.26/0.98  inst_num_of_duplicates:                 0
% 3.26/0.98  inst_inst_num_from_inst_to_res:         0
% 3.26/0.98  inst_dismatching_checking_time:         0.
% 3.26/0.98  
% 3.26/0.98  ------ Resolution
% 3.26/0.98  
% 3.26/0.98  res_num_of_clauses:                     0
% 3.26/0.98  res_num_in_passive:                     0
% 3.26/0.98  res_num_in_active:                      0
% 3.26/0.98  res_num_of_loops:                       80
% 3.26/0.98  res_forward_subset_subsumed:            303
% 3.26/0.98  res_backward_subset_subsumed:           4
% 3.26/0.98  res_forward_subsumed:                   0
% 3.26/0.98  res_backward_subsumed:                  0
% 3.26/0.98  res_forward_subsumption_resolution:     0
% 3.26/0.98  res_backward_subsumption_resolution:    0
% 3.26/0.98  res_clause_to_clause_subsumption:       651
% 3.26/0.98  res_orphan_elimination:                 0
% 3.26/0.98  res_tautology_del:                      217
% 3.26/0.98  res_num_eq_res_simplified:              0
% 3.26/0.98  res_num_sel_changes:                    0
% 3.26/0.98  res_moves_from_active_to_pass:          0
% 3.26/0.98  
% 3.26/0.98  ------ Superposition
% 3.26/0.98  
% 3.26/0.98  sup_time_total:                         0.
% 3.26/0.98  sup_time_generating:                    0.
% 3.26/0.98  sup_time_sim_full:                      0.
% 3.26/0.98  sup_time_sim_immed:                     0.
% 3.26/0.98  
% 3.26/0.98  sup_num_of_clauses:                     159
% 3.26/0.98  sup_num_in_active:                      101
% 3.26/0.98  sup_num_in_passive:                     58
% 3.26/0.98  sup_num_of_loops:                       101
% 3.26/0.98  sup_fw_superposition:                   132
% 3.26/0.98  sup_bw_superposition:                   54
% 3.26/0.98  sup_immediate_simplified:               38
% 3.26/0.98  sup_given_eliminated:                   0
% 3.26/0.98  comparisons_done:                       0
% 3.26/0.98  comparisons_avoided:                    0
% 3.26/0.98  
% 3.26/0.98  ------ Simplifications
% 3.26/0.98  
% 3.26/0.98  
% 3.26/0.98  sim_fw_subset_subsumed:                 12
% 3.26/0.98  sim_bw_subset_subsumed:                 0
% 3.26/0.98  sim_fw_subsumed:                        11
% 3.26/0.98  sim_bw_subsumed:                        0
% 3.26/0.98  sim_fw_subsumption_res:                 4
% 3.26/0.98  sim_bw_subsumption_res:                 0
% 3.26/0.98  sim_tautology_del:                      0
% 3.26/0.98  sim_eq_tautology_del:                   19
% 3.26/0.98  sim_eq_res_simp:                        3
% 3.26/0.98  sim_fw_demodulated:                     8
% 3.26/0.98  sim_bw_demodulated:                     1
% 3.26/0.98  sim_light_normalised:                   20
% 3.26/0.98  sim_joinable_taut:                      0
% 3.26/0.98  sim_joinable_simp:                      0
% 3.26/0.98  sim_ac_normalised:                      0
% 3.26/0.98  sim_smt_subsumption:                    0
% 3.26/0.98  
%------------------------------------------------------------------------------
