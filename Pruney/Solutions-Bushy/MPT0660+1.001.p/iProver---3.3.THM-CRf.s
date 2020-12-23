%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0660+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:50 EST 2020

% Result     : Theorem 1.01s
% Output     : CNFRefutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :   66 (  89 expanded)
%              Number of clauses        :   35 (  41 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :   13
%              Number of atoms          :  199 ( 239 expanded)
%              Number of equality atoms :  100 ( 106 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,conjecture,(
    ! [X0] : k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f18,plain,(
    ? [X0] : k2_funct_1(k6_relat_1(X0)) != k6_relat_1(X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,
    ( ? [X0] : k2_funct_1(k6_relat_1(X0)) != k6_relat_1(X0)
   => k2_funct_1(k6_relat_1(sK0)) != k6_relat_1(sK0) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    k2_funct_1(k6_relat_1(sK0)) != k6_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f34,plain,(
    k2_funct_1(k6_relat_1(sK0)) != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_4,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_131,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
    | k6_relat_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_132,plain,
    ( ~ v1_relat_1(k6_relat_1(X0))
    | ~ v1_funct_1(k6_relat_1(X0))
    | k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0))) = k6_relat_1(k1_relat_1(k6_relat_1(X0))) ),
    inference(unflattening,[status(thm)],[c_131])).

cnf(c_5,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_136,plain,
    ( k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0))) = k6_relat_1(k1_relat_1(k6_relat_1(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_132,c_5,c_2])).

cnf(c_12,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_358,plain,
    ( k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_136,c_12])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X0,X1) != X0
    | k2_relat_1(X0) != k1_relat_1(X1)
    | k6_relat_1(k1_relat_1(X1)) = X1 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_334,plain,
    ( k5_relat_1(X0,X1) != X0
    | k2_relat_1(X0) != k1_relat_1(X1)
    | k6_relat_1(k1_relat_1(X1)) = X1
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_724,plain,
    ( k1_relat_1(k2_funct_1(k6_relat_1(X0))) != k2_relat_1(k6_relat_1(X0))
    | k6_relat_1(k1_relat_1(k2_funct_1(k6_relat_1(X0)))) = k2_funct_1(k6_relat_1(X0))
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k2_funct_1(k6_relat_1(X0))) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_funct_1(k2_funct_1(k6_relat_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_358,c_334])).

cnf(c_11,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_153,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | k6_relat_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_154,plain,
    ( ~ v1_relat_1(k6_relat_1(X0))
    | ~ v1_funct_1(k6_relat_1(X0))
    | k1_relat_1(k2_funct_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_153])).

cnf(c_158,plain,
    ( k1_relat_1(k2_funct_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_154,c_5,c_2])).

cnf(c_352,plain,
    ( k1_relat_1(k2_funct_1(k6_relat_1(X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_158,c_11])).

cnf(c_725,plain,
    ( X0 != X0
    | k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0)
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k2_funct_1(k6_relat_1(X0))) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_funct_1(k2_funct_1(k6_relat_1(X0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_724,c_11,c_352])).

cnf(c_726,plain,
    ( k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0)
    | v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k2_funct_1(k6_relat_1(X0))) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_funct_1(k2_funct_1(k6_relat_1(X0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_725])).

cnf(c_728,plain,
    ( k2_funct_1(k6_relat_1(sK0)) = k6_relat_1(sK0)
    | v1_relat_1(k6_relat_1(sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(k6_relat_1(sK0))) != iProver_top
    | v1_funct_1(k6_relat_1(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(k6_relat_1(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_408,plain,
    ( ~ v1_relat_1(k6_relat_1(X0))
    | v1_relat_1(k2_funct_1(k6_relat_1(X0)))
    | ~ v1_funct_1(k6_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_409,plain,
    ( v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k2_funct_1(k6_relat_1(X0))) = iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_411,plain,
    ( v1_relat_1(k6_relat_1(sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(k6_relat_1(sK0))) = iProver_top
    | v1_funct_1(k6_relat_1(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_403,plain,
    ( ~ v1_relat_1(k6_relat_1(X0))
    | ~ v1_funct_1(k6_relat_1(X0))
    | v1_funct_1(k2_funct_1(k6_relat_1(X0))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_404,plain,
    ( v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_funct_1(k2_funct_1(k6_relat_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_406,plain,
    ( v1_relat_1(k6_relat_1(sK0)) != iProver_top
    | v1_funct_1(k6_relat_1(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(k6_relat_1(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_38,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_40,plain,
    ( v1_funct_1(k6_relat_1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_31,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_33,plain,
    ( v1_relat_1(k6_relat_1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_13,negated_conjecture,
    ( k2_funct_1(k6_relat_1(sK0)) != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_728,c_411,c_406,c_40,c_33,c_13])).


%------------------------------------------------------------------------------
