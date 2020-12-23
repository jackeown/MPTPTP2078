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
% DateTime   : Thu Dec  3 11:50:37 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 521 expanded)
%              Number of clauses        :   58 ( 149 expanded)
%              Number of leaves         :   12 ( 107 expanded)
%              Depth                    :   15
%              Number of atoms          :  242 (2038 expanded)
%              Number of equality atoms :  118 ( 788 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,
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

fof(f26,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f38,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_406,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_413,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(k2_relat_1(X0),X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_410,plain,
    ( k8_relat_1(k2_relat_1(X0),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_671,plain,
    ( k8_relat_1(k2_relat_1(k4_relat_1(X0)),k4_relat_1(X0)) = k4_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_410])).

cnf(c_2541,plain,
    ( k8_relat_1(k2_relat_1(k4_relat_1(sK0)),k4_relat_1(sK0)) = k4_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_406,c_671])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_13,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_167,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_168,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_167])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_23,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_170,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_168,c_15,c_14,c_13,c_23])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_175,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_176,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_175])).

cnf(c_26,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_178,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_176,c_15,c_14,c_13,c_26])).

cnf(c_424,plain,
    ( k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_170,c_178])).

cnf(c_2543,plain,
    ( k8_relat_1(k1_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_2541,c_424])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_411,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1260,plain,
    ( k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k4_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_411])).

cnf(c_3225,plain,
    ( k5_relat_1(k4_relat_1(sK0),k6_relat_1(X0)) = k8_relat_1(X0,k4_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_406,c_1260])).

cnf(c_1,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_412,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_407,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_621,plain,
    ( k10_relat_1(k4_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k4_relat_1(X0),X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_407])).

cnf(c_2390,plain,
    ( k10_relat_1(k4_relat_1(sK0),k1_relat_1(X0)) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_406,c_621])).

cnf(c_2739,plain,
    ( k10_relat_1(k4_relat_1(sK0),k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_412,c_2390])).

cnf(c_8,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2744,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(sK0),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK0),X0) ),
    inference(light_normalisation,[status(thm)],[c_2739,c_8])).

cnf(c_3240,plain,
    ( k1_relat_1(k8_relat_1(X0,k4_relat_1(sK0))) = k10_relat_1(k4_relat_1(sK0),X0) ),
    inference(demodulation,[status(thm)],[c_3225,c_2744])).

cnf(c_3414,plain,
    ( k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_2543,c_3240])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_159,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_160,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_159])).

cnf(c_20,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_162,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_160,c_15,c_14,c_13,c_20])).

cnf(c_427,plain,
    ( k1_relat_1(k4_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_162,c_178])).

cnf(c_2740,plain,
    ( k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(superposition,[status(thm)],[c_406,c_2390])).

cnf(c_3415,plain,
    ( k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_3414,c_427,c_2740])).

cnf(c_3546,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k2_relat_1(sK0) ),
    inference(demodulation,[status(thm)],[c_3415,c_2740])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_408,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1139,plain,
    ( k9_relat_1(sK0,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_406,c_408])).

cnf(c_1472,plain,
    ( k9_relat_1(sK0,k2_relat_1(k4_relat_1(X0))) = k2_relat_1(k5_relat_1(k4_relat_1(X0),sK0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_1139])).

cnf(c_1548,plain,
    ( k9_relat_1(sK0,k2_relat_1(k4_relat_1(sK0))) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(superposition,[status(thm)],[c_406,c_1472])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_409,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_786,plain,
    ( k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_406,c_409])).

cnf(c_1550,plain,
    ( k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k2_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_1548,c_424,c_786])).

cnf(c_12,negated_conjecture,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_446,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) != k2_relat_1(sK0)
    | k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) != k2_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_12,c_178])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3546,c_1550,c_446])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:19:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.64/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/0.95  
% 2.64/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.64/0.95  
% 2.64/0.95  ------  iProver source info
% 2.64/0.95  
% 2.64/0.95  git: date: 2020-06-30 10:37:57 +0100
% 2.64/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.64/0.95  git: non_committed_changes: false
% 2.64/0.95  git: last_make_outside_of_git: false
% 2.64/0.95  
% 2.64/0.95  ------ 
% 2.64/0.95  
% 2.64/0.95  ------ Input Options
% 2.64/0.95  
% 2.64/0.95  --out_options                           all
% 2.64/0.95  --tptp_safe_out                         true
% 2.64/0.95  --problem_path                          ""
% 2.64/0.95  --include_path                          ""
% 2.64/0.95  --clausifier                            res/vclausify_rel
% 2.64/0.95  --clausifier_options                    --mode clausify
% 2.64/0.95  --stdin                                 false
% 2.64/0.95  --stats_out                             all
% 2.64/0.95  
% 2.64/0.95  ------ General Options
% 2.64/0.95  
% 2.64/0.95  --fof                                   false
% 2.64/0.95  --time_out_real                         305.
% 2.64/0.95  --time_out_virtual                      -1.
% 2.64/0.95  --symbol_type_check                     false
% 2.64/0.95  --clausify_out                          false
% 2.64/0.95  --sig_cnt_out                           false
% 2.64/0.95  --trig_cnt_out                          false
% 2.64/0.95  --trig_cnt_out_tolerance                1.
% 2.64/0.95  --trig_cnt_out_sk_spl                   false
% 2.64/0.95  --abstr_cl_out                          false
% 2.64/0.95  
% 2.64/0.95  ------ Global Options
% 2.64/0.95  
% 2.64/0.95  --schedule                              default
% 2.64/0.95  --add_important_lit                     false
% 2.64/0.95  --prop_solver_per_cl                    1000
% 2.64/0.95  --min_unsat_core                        false
% 2.64/0.95  --soft_assumptions                      false
% 2.64/0.95  --soft_lemma_size                       3
% 2.64/0.95  --prop_impl_unit_size                   0
% 2.64/0.95  --prop_impl_unit                        []
% 2.64/0.95  --share_sel_clauses                     true
% 2.64/0.95  --reset_solvers                         false
% 2.64/0.95  --bc_imp_inh                            [conj_cone]
% 2.64/0.95  --conj_cone_tolerance                   3.
% 2.64/0.95  --extra_neg_conj                        none
% 2.64/0.95  --large_theory_mode                     true
% 2.64/0.95  --prolific_symb_bound                   200
% 2.64/0.95  --lt_threshold                          2000
% 2.64/0.95  --clause_weak_htbl                      true
% 2.64/0.95  --gc_record_bc_elim                     false
% 2.64/0.95  
% 2.64/0.95  ------ Preprocessing Options
% 2.64/0.95  
% 2.64/0.95  --preprocessing_flag                    true
% 2.64/0.95  --time_out_prep_mult                    0.1
% 2.64/0.95  --splitting_mode                        input
% 2.64/0.95  --splitting_grd                         true
% 2.64/0.95  --splitting_cvd                         false
% 2.64/0.95  --splitting_cvd_svl                     false
% 2.64/0.95  --splitting_nvd                         32
% 2.64/0.95  --sub_typing                            true
% 2.64/0.95  --prep_gs_sim                           true
% 2.64/0.95  --prep_unflatten                        true
% 2.64/0.95  --prep_res_sim                          true
% 2.64/0.95  --prep_upred                            true
% 2.64/0.95  --prep_sem_filter                       exhaustive
% 2.64/0.95  --prep_sem_filter_out                   false
% 2.64/0.95  --pred_elim                             true
% 2.64/0.95  --res_sim_input                         true
% 2.64/0.95  --eq_ax_congr_red                       true
% 2.64/0.95  --pure_diseq_elim                       true
% 2.64/0.95  --brand_transform                       false
% 2.64/0.95  --non_eq_to_eq                          false
% 2.64/0.95  --prep_def_merge                        true
% 2.64/0.95  --prep_def_merge_prop_impl              false
% 2.64/0.95  --prep_def_merge_mbd                    true
% 2.64/0.95  --prep_def_merge_tr_red                 false
% 2.64/0.95  --prep_def_merge_tr_cl                  false
% 2.64/0.95  --smt_preprocessing                     true
% 2.64/0.95  --smt_ac_axioms                         fast
% 2.64/0.95  --preprocessed_out                      false
% 2.64/0.95  --preprocessed_stats                    false
% 2.64/0.95  
% 2.64/0.95  ------ Abstraction refinement Options
% 2.64/0.95  
% 2.64/0.95  --abstr_ref                             []
% 2.64/0.95  --abstr_ref_prep                        false
% 2.64/0.95  --abstr_ref_until_sat                   false
% 2.64/0.95  --abstr_ref_sig_restrict                funpre
% 2.64/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/0.95  --abstr_ref_under                       []
% 2.64/0.95  
% 2.64/0.95  ------ SAT Options
% 2.64/0.95  
% 2.64/0.95  --sat_mode                              false
% 2.64/0.95  --sat_fm_restart_options                ""
% 2.64/0.95  --sat_gr_def                            false
% 2.64/0.95  --sat_epr_types                         true
% 2.64/0.95  --sat_non_cyclic_types                  false
% 2.64/0.95  --sat_finite_models                     false
% 2.64/0.95  --sat_fm_lemmas                         false
% 2.64/0.95  --sat_fm_prep                           false
% 2.64/0.95  --sat_fm_uc_incr                        true
% 2.64/0.95  --sat_out_model                         small
% 2.64/0.95  --sat_out_clauses                       false
% 2.64/0.95  
% 2.64/0.95  ------ QBF Options
% 2.64/0.95  
% 2.64/0.95  --qbf_mode                              false
% 2.64/0.95  --qbf_elim_univ                         false
% 2.64/0.95  --qbf_dom_inst                          none
% 2.64/0.95  --qbf_dom_pre_inst                      false
% 2.64/0.95  --qbf_sk_in                             false
% 2.64/0.95  --qbf_pred_elim                         true
% 2.64/0.95  --qbf_split                             512
% 2.64/0.95  
% 2.64/0.95  ------ BMC1 Options
% 2.64/0.95  
% 2.64/0.95  --bmc1_incremental                      false
% 2.64/0.95  --bmc1_axioms                           reachable_all
% 2.64/0.95  --bmc1_min_bound                        0
% 2.64/0.95  --bmc1_max_bound                        -1
% 2.64/0.95  --bmc1_max_bound_default                -1
% 2.64/0.95  --bmc1_symbol_reachability              true
% 2.64/0.95  --bmc1_property_lemmas                  false
% 2.64/0.95  --bmc1_k_induction                      false
% 2.64/0.95  --bmc1_non_equiv_states                 false
% 2.64/0.95  --bmc1_deadlock                         false
% 2.64/0.95  --bmc1_ucm                              false
% 2.64/0.95  --bmc1_add_unsat_core                   none
% 2.64/0.95  --bmc1_unsat_core_children              false
% 2.64/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/0.95  --bmc1_out_stat                         full
% 2.64/0.95  --bmc1_ground_init                      false
% 2.64/0.95  --bmc1_pre_inst_next_state              false
% 2.64/0.95  --bmc1_pre_inst_state                   false
% 2.64/0.95  --bmc1_pre_inst_reach_state             false
% 2.64/0.95  --bmc1_out_unsat_core                   false
% 2.64/0.95  --bmc1_aig_witness_out                  false
% 2.64/0.95  --bmc1_verbose                          false
% 2.64/0.95  --bmc1_dump_clauses_tptp                false
% 2.64/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.64/0.95  --bmc1_dump_file                        -
% 2.64/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.64/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.64/0.95  --bmc1_ucm_extend_mode                  1
% 2.64/0.95  --bmc1_ucm_init_mode                    2
% 2.64/0.95  --bmc1_ucm_cone_mode                    none
% 2.64/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.64/0.95  --bmc1_ucm_relax_model                  4
% 2.64/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.64/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/0.95  --bmc1_ucm_layered_model                none
% 2.64/0.95  --bmc1_ucm_max_lemma_size               10
% 2.64/0.95  
% 2.64/0.95  ------ AIG Options
% 2.64/0.95  
% 2.64/0.95  --aig_mode                              false
% 2.64/0.95  
% 2.64/0.95  ------ Instantiation Options
% 2.64/0.95  
% 2.64/0.95  --instantiation_flag                    true
% 2.64/0.95  --inst_sos_flag                         false
% 2.64/0.95  --inst_sos_phase                        true
% 2.64/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/0.95  --inst_lit_sel_side                     num_symb
% 2.64/0.95  --inst_solver_per_active                1400
% 2.64/0.95  --inst_solver_calls_frac                1.
% 2.64/0.95  --inst_passive_queue_type               priority_queues
% 2.64/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/0.95  --inst_passive_queues_freq              [25;2]
% 2.64/0.95  --inst_dismatching                      true
% 2.64/0.95  --inst_eager_unprocessed_to_passive     true
% 2.64/0.95  --inst_prop_sim_given                   true
% 2.64/0.95  --inst_prop_sim_new                     false
% 2.64/0.95  --inst_subs_new                         false
% 2.64/0.95  --inst_eq_res_simp                      false
% 2.64/0.95  --inst_subs_given                       false
% 2.64/0.95  --inst_orphan_elimination               true
% 2.64/0.95  --inst_learning_loop_flag               true
% 2.64/0.95  --inst_learning_start                   3000
% 2.64/0.95  --inst_learning_factor                  2
% 2.64/0.95  --inst_start_prop_sim_after_learn       3
% 2.64/0.95  --inst_sel_renew                        solver
% 2.64/0.95  --inst_lit_activity_flag                true
% 2.64/0.95  --inst_restr_to_given                   false
% 2.64/0.95  --inst_activity_threshold               500
% 2.64/0.95  --inst_out_proof                        true
% 2.64/0.95  
% 2.64/0.95  ------ Resolution Options
% 2.64/0.95  
% 2.64/0.95  --resolution_flag                       true
% 2.64/0.95  --res_lit_sel                           adaptive
% 2.64/0.95  --res_lit_sel_side                      none
% 2.64/0.95  --res_ordering                          kbo
% 2.64/0.95  --res_to_prop_solver                    active
% 2.64/0.95  --res_prop_simpl_new                    false
% 2.64/0.95  --res_prop_simpl_given                  true
% 2.64/0.95  --res_passive_queue_type                priority_queues
% 2.64/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/0.95  --res_passive_queues_freq               [15;5]
% 2.64/0.95  --res_forward_subs                      full
% 2.64/0.95  --res_backward_subs                     full
% 2.64/0.95  --res_forward_subs_resolution           true
% 2.64/0.95  --res_backward_subs_resolution          true
% 2.64/0.95  --res_orphan_elimination                true
% 2.64/0.95  --res_time_limit                        2.
% 2.64/0.95  --res_out_proof                         true
% 2.64/0.95  
% 2.64/0.95  ------ Superposition Options
% 2.64/0.95  
% 2.64/0.95  --superposition_flag                    true
% 2.64/0.95  --sup_passive_queue_type                priority_queues
% 2.64/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.64/0.95  --demod_completeness_check              fast
% 2.64/0.95  --demod_use_ground                      true
% 2.64/0.95  --sup_to_prop_solver                    passive
% 2.64/0.95  --sup_prop_simpl_new                    true
% 2.64/0.95  --sup_prop_simpl_given                  true
% 2.64/0.95  --sup_fun_splitting                     false
% 2.64/0.95  --sup_smt_interval                      50000
% 2.64/0.95  
% 2.64/0.95  ------ Superposition Simplification Setup
% 2.64/0.95  
% 2.64/0.95  --sup_indices_passive                   []
% 2.64/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.95  --sup_full_bw                           [BwDemod]
% 2.64/0.95  --sup_immed_triv                        [TrivRules]
% 2.64/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.95  --sup_immed_bw_main                     []
% 2.64/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/0.95  
% 2.64/0.95  ------ Combination Options
% 2.64/0.95  
% 2.64/0.95  --comb_res_mult                         3
% 2.64/0.95  --comb_sup_mult                         2
% 2.64/0.95  --comb_inst_mult                        10
% 2.64/0.95  
% 2.64/0.95  ------ Debug Options
% 2.64/0.95  
% 2.64/0.95  --dbg_backtrace                         false
% 2.64/0.95  --dbg_dump_prop_clauses                 false
% 2.64/0.95  --dbg_dump_prop_clauses_file            -
% 2.64/0.95  --dbg_out_stat                          false
% 2.64/0.95  ------ Parsing...
% 2.64/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.64/0.95  
% 2.64/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.64/0.95  
% 2.64/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.64/0.95  
% 2.64/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.64/0.95  ------ Proving...
% 2.64/0.95  ------ Problem Properties 
% 2.64/0.95  
% 2.64/0.95  
% 2.64/0.95  clauses                                 14
% 2.64/0.95  conjectures                             2
% 2.64/0.95  EPR                                     1
% 2.64/0.95  Horn                                    14
% 2.64/0.95  unary                                   7
% 2.64/0.95  binary                                  5
% 2.64/0.95  lits                                    23
% 2.64/0.95  lits eq                                 12
% 2.64/0.95  fd_pure                                 0
% 2.64/0.95  fd_pseudo                               0
% 2.64/0.95  fd_cond                                 0
% 2.64/0.95  fd_pseudo_cond                          0
% 2.64/0.95  AC symbols                              0
% 2.64/0.95  
% 2.64/0.95  ------ Schedule dynamic 5 is on 
% 2.64/0.95  
% 2.64/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.64/0.95  
% 2.64/0.95  
% 2.64/0.95  ------ 
% 2.64/0.95  Current options:
% 2.64/0.95  ------ 
% 2.64/0.95  
% 2.64/0.95  ------ Input Options
% 2.64/0.95  
% 2.64/0.95  --out_options                           all
% 2.64/0.95  --tptp_safe_out                         true
% 2.64/0.95  --problem_path                          ""
% 2.64/0.95  --include_path                          ""
% 2.64/0.95  --clausifier                            res/vclausify_rel
% 2.64/0.95  --clausifier_options                    --mode clausify
% 2.64/0.95  --stdin                                 false
% 2.64/0.95  --stats_out                             all
% 2.64/0.95  
% 2.64/0.95  ------ General Options
% 2.64/0.95  
% 2.64/0.95  --fof                                   false
% 2.64/0.95  --time_out_real                         305.
% 2.64/0.95  --time_out_virtual                      -1.
% 2.64/0.95  --symbol_type_check                     false
% 2.64/0.95  --clausify_out                          false
% 2.64/0.95  --sig_cnt_out                           false
% 2.64/0.95  --trig_cnt_out                          false
% 2.64/0.95  --trig_cnt_out_tolerance                1.
% 2.64/0.95  --trig_cnt_out_sk_spl                   false
% 2.64/0.95  --abstr_cl_out                          false
% 2.64/0.95  
% 2.64/0.95  ------ Global Options
% 2.64/0.95  
% 2.64/0.95  --schedule                              default
% 2.64/0.95  --add_important_lit                     false
% 2.64/0.95  --prop_solver_per_cl                    1000
% 2.64/0.95  --min_unsat_core                        false
% 2.64/0.95  --soft_assumptions                      false
% 2.64/0.95  --soft_lemma_size                       3
% 2.64/0.95  --prop_impl_unit_size                   0
% 2.64/0.95  --prop_impl_unit                        []
% 2.64/0.95  --share_sel_clauses                     true
% 2.64/0.95  --reset_solvers                         false
% 2.64/0.95  --bc_imp_inh                            [conj_cone]
% 2.64/0.95  --conj_cone_tolerance                   3.
% 2.64/0.95  --extra_neg_conj                        none
% 2.64/0.95  --large_theory_mode                     true
% 2.64/0.95  --prolific_symb_bound                   200
% 2.64/0.95  --lt_threshold                          2000
% 2.64/0.95  --clause_weak_htbl                      true
% 2.64/0.95  --gc_record_bc_elim                     false
% 2.64/0.95  
% 2.64/0.95  ------ Preprocessing Options
% 2.64/0.95  
% 2.64/0.95  --preprocessing_flag                    true
% 2.64/0.95  --time_out_prep_mult                    0.1
% 2.64/0.95  --splitting_mode                        input
% 2.64/0.95  --splitting_grd                         true
% 2.64/0.95  --splitting_cvd                         false
% 2.64/0.95  --splitting_cvd_svl                     false
% 2.64/0.95  --splitting_nvd                         32
% 2.64/0.95  --sub_typing                            true
% 2.64/0.95  --prep_gs_sim                           true
% 2.64/0.95  --prep_unflatten                        true
% 2.64/0.95  --prep_res_sim                          true
% 2.64/0.95  --prep_upred                            true
% 2.64/0.95  --prep_sem_filter                       exhaustive
% 2.64/0.95  --prep_sem_filter_out                   false
% 2.64/0.95  --pred_elim                             true
% 2.64/0.95  --res_sim_input                         true
% 2.64/0.95  --eq_ax_congr_red                       true
% 2.64/0.95  --pure_diseq_elim                       true
% 2.64/0.95  --brand_transform                       false
% 2.64/0.95  --non_eq_to_eq                          false
% 2.64/0.95  --prep_def_merge                        true
% 2.64/0.95  --prep_def_merge_prop_impl              false
% 2.64/0.95  --prep_def_merge_mbd                    true
% 2.64/0.95  --prep_def_merge_tr_red                 false
% 2.64/0.95  --prep_def_merge_tr_cl                  false
% 2.64/0.95  --smt_preprocessing                     true
% 2.64/0.95  --smt_ac_axioms                         fast
% 2.64/0.95  --preprocessed_out                      false
% 2.64/0.95  --preprocessed_stats                    false
% 2.64/0.95  
% 2.64/0.95  ------ Abstraction refinement Options
% 2.64/0.95  
% 2.64/0.95  --abstr_ref                             []
% 2.64/0.95  --abstr_ref_prep                        false
% 2.64/0.95  --abstr_ref_until_sat                   false
% 2.64/0.95  --abstr_ref_sig_restrict                funpre
% 2.64/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/0.95  --abstr_ref_under                       []
% 2.64/0.95  
% 2.64/0.95  ------ SAT Options
% 2.64/0.95  
% 2.64/0.95  --sat_mode                              false
% 2.64/0.95  --sat_fm_restart_options                ""
% 2.64/0.95  --sat_gr_def                            false
% 2.64/0.95  --sat_epr_types                         true
% 2.64/0.95  --sat_non_cyclic_types                  false
% 2.64/0.95  --sat_finite_models                     false
% 2.64/0.95  --sat_fm_lemmas                         false
% 2.64/0.95  --sat_fm_prep                           false
% 2.64/0.95  --sat_fm_uc_incr                        true
% 2.64/0.95  --sat_out_model                         small
% 2.64/0.95  --sat_out_clauses                       false
% 2.64/0.95  
% 2.64/0.95  ------ QBF Options
% 2.64/0.95  
% 2.64/0.95  --qbf_mode                              false
% 2.64/0.95  --qbf_elim_univ                         false
% 2.64/0.95  --qbf_dom_inst                          none
% 2.64/0.95  --qbf_dom_pre_inst                      false
% 2.64/0.95  --qbf_sk_in                             false
% 2.64/0.95  --qbf_pred_elim                         true
% 2.64/0.95  --qbf_split                             512
% 2.64/0.95  
% 2.64/0.95  ------ BMC1 Options
% 2.64/0.95  
% 2.64/0.95  --bmc1_incremental                      false
% 2.64/0.95  --bmc1_axioms                           reachable_all
% 2.64/0.95  --bmc1_min_bound                        0
% 2.64/0.95  --bmc1_max_bound                        -1
% 2.64/0.95  --bmc1_max_bound_default                -1
% 2.64/0.95  --bmc1_symbol_reachability              true
% 2.64/0.95  --bmc1_property_lemmas                  false
% 2.64/0.95  --bmc1_k_induction                      false
% 2.64/0.95  --bmc1_non_equiv_states                 false
% 2.64/0.95  --bmc1_deadlock                         false
% 2.64/0.95  --bmc1_ucm                              false
% 2.64/0.95  --bmc1_add_unsat_core                   none
% 2.64/0.95  --bmc1_unsat_core_children              false
% 2.64/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/0.95  --bmc1_out_stat                         full
% 2.64/0.95  --bmc1_ground_init                      false
% 2.64/0.95  --bmc1_pre_inst_next_state              false
% 2.64/0.95  --bmc1_pre_inst_state                   false
% 2.64/0.95  --bmc1_pre_inst_reach_state             false
% 2.64/0.95  --bmc1_out_unsat_core                   false
% 2.64/0.95  --bmc1_aig_witness_out                  false
% 2.64/0.95  --bmc1_verbose                          false
% 2.64/0.95  --bmc1_dump_clauses_tptp                false
% 2.64/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.64/0.95  --bmc1_dump_file                        -
% 2.64/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.64/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.64/0.95  --bmc1_ucm_extend_mode                  1
% 2.64/0.95  --bmc1_ucm_init_mode                    2
% 2.64/0.95  --bmc1_ucm_cone_mode                    none
% 2.64/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.64/0.95  --bmc1_ucm_relax_model                  4
% 2.64/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.64/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/0.95  --bmc1_ucm_layered_model                none
% 2.64/0.95  --bmc1_ucm_max_lemma_size               10
% 2.64/0.95  
% 2.64/0.95  ------ AIG Options
% 2.64/0.95  
% 2.64/0.95  --aig_mode                              false
% 2.64/0.95  
% 2.64/0.95  ------ Instantiation Options
% 2.64/0.95  
% 2.64/0.95  --instantiation_flag                    true
% 2.64/0.95  --inst_sos_flag                         false
% 2.64/0.95  --inst_sos_phase                        true
% 2.64/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/0.95  --inst_lit_sel_side                     none
% 2.64/0.95  --inst_solver_per_active                1400
% 2.64/0.95  --inst_solver_calls_frac                1.
% 2.64/0.95  --inst_passive_queue_type               priority_queues
% 2.64/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/0.95  --inst_passive_queues_freq              [25;2]
% 2.64/0.95  --inst_dismatching                      true
% 2.64/0.95  --inst_eager_unprocessed_to_passive     true
% 2.64/0.95  --inst_prop_sim_given                   true
% 2.64/0.95  --inst_prop_sim_new                     false
% 2.64/0.95  --inst_subs_new                         false
% 2.64/0.95  --inst_eq_res_simp                      false
% 2.64/0.95  --inst_subs_given                       false
% 2.64/0.95  --inst_orphan_elimination               true
% 2.64/0.95  --inst_learning_loop_flag               true
% 2.64/0.95  --inst_learning_start                   3000
% 2.64/0.95  --inst_learning_factor                  2
% 2.64/0.95  --inst_start_prop_sim_after_learn       3
% 2.64/0.95  --inst_sel_renew                        solver
% 2.64/0.95  --inst_lit_activity_flag                true
% 2.64/0.95  --inst_restr_to_given                   false
% 2.64/0.95  --inst_activity_threshold               500
% 2.64/0.95  --inst_out_proof                        true
% 2.64/0.95  
% 2.64/0.95  ------ Resolution Options
% 2.64/0.95  
% 2.64/0.95  --resolution_flag                       false
% 2.64/0.95  --res_lit_sel                           adaptive
% 2.64/0.95  --res_lit_sel_side                      none
% 2.64/0.95  --res_ordering                          kbo
% 2.64/0.95  --res_to_prop_solver                    active
% 2.64/0.95  --res_prop_simpl_new                    false
% 2.64/0.95  --res_prop_simpl_given                  true
% 2.64/0.95  --res_passive_queue_type                priority_queues
% 2.64/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/0.95  --res_passive_queues_freq               [15;5]
% 2.64/0.95  --res_forward_subs                      full
% 2.64/0.95  --res_backward_subs                     full
% 2.64/0.95  --res_forward_subs_resolution           true
% 2.64/0.95  --res_backward_subs_resolution          true
% 2.64/0.95  --res_orphan_elimination                true
% 2.64/0.95  --res_time_limit                        2.
% 2.64/0.95  --res_out_proof                         true
% 2.64/0.95  
% 2.64/0.95  ------ Superposition Options
% 2.64/0.95  
% 2.64/0.95  --superposition_flag                    true
% 2.64/0.95  --sup_passive_queue_type                priority_queues
% 2.64/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.64/0.95  --demod_completeness_check              fast
% 2.64/0.95  --demod_use_ground                      true
% 2.64/0.95  --sup_to_prop_solver                    passive
% 2.64/0.95  --sup_prop_simpl_new                    true
% 2.64/0.95  --sup_prop_simpl_given                  true
% 2.64/0.95  --sup_fun_splitting                     false
% 2.64/0.95  --sup_smt_interval                      50000
% 2.64/0.95  
% 2.64/0.95  ------ Superposition Simplification Setup
% 2.64/0.95  
% 2.64/0.95  --sup_indices_passive                   []
% 2.64/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.95  --sup_full_bw                           [BwDemod]
% 2.64/0.95  --sup_immed_triv                        [TrivRules]
% 2.64/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.95  --sup_immed_bw_main                     []
% 2.64/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/0.95  
% 2.64/0.95  ------ Combination Options
% 2.64/0.95  
% 2.64/0.95  --comb_res_mult                         3
% 2.64/0.95  --comb_sup_mult                         2
% 2.64/0.95  --comb_inst_mult                        10
% 2.64/0.95  
% 2.64/0.95  ------ Debug Options
% 2.64/0.95  
% 2.64/0.95  --dbg_backtrace                         false
% 2.64/0.95  --dbg_dump_prop_clauses                 false
% 2.64/0.95  --dbg_dump_prop_clauses_file            -
% 2.64/0.95  --dbg_out_stat                          false
% 2.64/0.95  
% 2.64/0.95  
% 2.64/0.95  
% 2.64/0.95  
% 2.64/0.95  ------ Proving...
% 2.64/0.95  
% 2.64/0.95  
% 2.64/0.95  % SZS status Theorem for theBenchmark.p
% 2.64/0.95  
% 2.64/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 2.64/0.95  
% 2.64/0.95  fof(f11,conjecture,(
% 2.64/0.95    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 2.64/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.95  
% 2.64/0.95  fof(f12,negated_conjecture,(
% 2.64/0.95    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 2.64/0.95    inference(negated_conjecture,[],[f11])).
% 2.64/0.95  
% 2.64/0.95  fof(f23,plain,(
% 2.64/0.95    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.64/0.95    inference(ennf_transformation,[],[f12])).
% 2.64/0.95  
% 2.64/0.95  fof(f24,plain,(
% 2.64/0.95    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.64/0.95    inference(flattening,[],[f23])).
% 2.64/0.95  
% 2.64/0.95  fof(f25,plain,(
% 2.64/0.95    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.64/0.95    introduced(choice_axiom,[])).
% 2.64/0.95  
% 2.64/0.95  fof(f26,plain,(
% 2.64/0.95    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.64/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 2.64/0.95  
% 2.64/0.95  fof(f39,plain,(
% 2.64/0.95    v1_relat_1(sK0)),
% 2.64/0.95    inference(cnf_transformation,[],[f26])).
% 2.64/0.95  
% 2.64/0.95  fof(f1,axiom,(
% 2.64/0.95    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.64/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.95  
% 2.64/0.95  fof(f13,plain,(
% 2.64/0.95    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.64/0.95    inference(ennf_transformation,[],[f1])).
% 2.64/0.95  
% 2.64/0.95  fof(f27,plain,(
% 2.64/0.95    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.64/0.95    inference(cnf_transformation,[],[f13])).
% 2.64/0.95  
% 2.64/0.95  fof(f4,axiom,(
% 2.64/0.95    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 2.64/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.95  
% 2.64/0.95  fof(f15,plain,(
% 2.64/0.95    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 2.64/0.95    inference(ennf_transformation,[],[f4])).
% 2.64/0.95  
% 2.64/0.95  fof(f30,plain,(
% 2.64/0.95    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.64/0.95    inference(cnf_transformation,[],[f15])).
% 2.64/0.95  
% 2.64/0.95  fof(f10,axiom,(
% 2.64/0.95    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.64/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.95  
% 2.64/0.95  fof(f21,plain,(
% 2.64/0.95    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.64/0.95    inference(ennf_transformation,[],[f10])).
% 2.64/0.95  
% 2.64/0.95  fof(f22,plain,(
% 2.64/0.95    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.64/0.95    inference(flattening,[],[f21])).
% 2.64/0.95  
% 2.64/0.95  fof(f38,plain,(
% 2.64/0.95    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.64/0.95    inference(cnf_transformation,[],[f22])).
% 2.64/0.95  
% 2.64/0.95  fof(f41,plain,(
% 2.64/0.95    v2_funct_1(sK0)),
% 2.64/0.95    inference(cnf_transformation,[],[f26])).
% 2.64/0.95  
% 2.64/0.95  fof(f40,plain,(
% 2.64/0.95    v1_funct_1(sK0)),
% 2.64/0.95    inference(cnf_transformation,[],[f26])).
% 2.64/0.95  
% 2.64/0.95  fof(f9,axiom,(
% 2.64/0.95    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.64/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.95  
% 2.64/0.95  fof(f19,plain,(
% 2.64/0.95    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.64/0.95    inference(ennf_transformation,[],[f9])).
% 2.64/0.95  
% 2.64/0.95  fof(f20,plain,(
% 2.64/0.95    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.64/0.95    inference(flattening,[],[f19])).
% 2.64/0.95  
% 2.64/0.95  fof(f36,plain,(
% 2.64/0.95    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.64/0.95    inference(cnf_transformation,[],[f20])).
% 2.64/0.95  
% 2.64/0.95  fof(f3,axiom,(
% 2.64/0.95    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 2.64/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.95  
% 2.64/0.95  fof(f14,plain,(
% 2.64/0.95    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 2.64/0.95    inference(ennf_transformation,[],[f3])).
% 2.64/0.95  
% 2.64/0.95  fof(f29,plain,(
% 2.64/0.95    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 2.64/0.95    inference(cnf_transformation,[],[f14])).
% 2.64/0.95  
% 2.64/0.95  fof(f2,axiom,(
% 2.64/0.95    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.64/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.95  
% 2.64/0.95  fof(f28,plain,(
% 2.64/0.95    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.64/0.95    inference(cnf_transformation,[],[f2])).
% 2.64/0.95  
% 2.64/0.95  fof(f7,axiom,(
% 2.64/0.95    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.64/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.95  
% 2.64/0.95  fof(f18,plain,(
% 2.64/0.95    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.64/0.95    inference(ennf_transformation,[],[f7])).
% 2.64/0.95  
% 2.64/0.95  fof(f33,plain,(
% 2.64/0.95    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.64/0.95    inference(cnf_transformation,[],[f18])).
% 2.64/0.95  
% 2.64/0.95  fof(f8,axiom,(
% 2.64/0.95    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.64/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.95  
% 2.64/0.95  fof(f34,plain,(
% 2.64/0.95    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.64/0.95    inference(cnf_transformation,[],[f8])).
% 2.64/0.95  
% 2.64/0.95  fof(f37,plain,(
% 2.64/0.95    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.64/0.95    inference(cnf_transformation,[],[f22])).
% 2.64/0.95  
% 2.64/0.95  fof(f6,axiom,(
% 2.64/0.95    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 2.64/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.95  
% 2.64/0.95  fof(f17,plain,(
% 2.64/0.95    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.64/0.95    inference(ennf_transformation,[],[f6])).
% 2.64/0.95  
% 2.64/0.95  fof(f32,plain,(
% 2.64/0.95    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.64/0.95    inference(cnf_transformation,[],[f17])).
% 2.64/0.95  
% 2.64/0.95  fof(f5,axiom,(
% 2.64/0.95    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 2.64/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.95  
% 2.64/0.95  fof(f16,plain,(
% 2.64/0.95    ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.64/0.95    inference(ennf_transformation,[],[f5])).
% 2.64/0.95  
% 2.64/0.95  fof(f31,plain,(
% 2.64/0.95    ( ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.64/0.95    inference(cnf_transformation,[],[f16])).
% 2.64/0.95  
% 2.64/0.95  fof(f42,plain,(
% 2.64/0.95    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 2.64/0.95    inference(cnf_transformation,[],[f26])).
% 2.64/0.95  
% 2.64/0.95  cnf(c_15,negated_conjecture,
% 2.64/0.95      ( v1_relat_1(sK0) ),
% 2.64/0.95      inference(cnf_transformation,[],[f39]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_406,plain,
% 2.64/0.95      ( v1_relat_1(sK0) = iProver_top ),
% 2.64/0.95      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_0,plain,
% 2.64/0.95      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 2.64/0.95      inference(cnf_transformation,[],[f27]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_413,plain,
% 2.64/0.95      ( v1_relat_1(X0) != iProver_top
% 2.64/0.95      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 2.64/0.95      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_3,plain,
% 2.64/0.95      ( ~ v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0 ),
% 2.64/0.95      inference(cnf_transformation,[],[f30]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_410,plain,
% 2.64/0.95      ( k8_relat_1(k2_relat_1(X0),X0) = X0
% 2.64/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.64/0.95      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_671,plain,
% 2.64/0.95      ( k8_relat_1(k2_relat_1(k4_relat_1(X0)),k4_relat_1(X0)) = k4_relat_1(X0)
% 2.64/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.64/0.95      inference(superposition,[status(thm)],[c_413,c_410]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_2541,plain,
% 2.64/0.95      ( k8_relat_1(k2_relat_1(k4_relat_1(sK0)),k4_relat_1(sK0)) = k4_relat_1(sK0) ),
% 2.64/0.95      inference(superposition,[status(thm)],[c_406,c_671]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_10,plain,
% 2.64/0.95      ( ~ v1_funct_1(X0)
% 2.64/0.95      | ~ v2_funct_1(X0)
% 2.64/0.95      | ~ v1_relat_1(X0)
% 2.64/0.95      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.64/0.95      inference(cnf_transformation,[],[f38]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_13,negated_conjecture,
% 2.64/0.95      ( v2_funct_1(sK0) ),
% 2.64/0.95      inference(cnf_transformation,[],[f41]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_167,plain,
% 2.64/0.95      ( ~ v1_funct_1(X0)
% 2.64/0.95      | ~ v1_relat_1(X0)
% 2.64/0.95      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.64/0.95      | sK0 != X0 ),
% 2.64/0.95      inference(resolution_lifted,[status(thm)],[c_10,c_13]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_168,plain,
% 2.64/0.95      ( ~ v1_funct_1(sK0)
% 2.64/0.95      | ~ v1_relat_1(sK0)
% 2.64/0.95      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 2.64/0.95      inference(unflattening,[status(thm)],[c_167]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_14,negated_conjecture,
% 2.64/0.95      ( v1_funct_1(sK0) ),
% 2.64/0.95      inference(cnf_transformation,[],[f40]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_23,plain,
% 2.64/0.95      ( ~ v1_funct_1(sK0)
% 2.64/0.95      | ~ v2_funct_1(sK0)
% 2.64/0.95      | ~ v1_relat_1(sK0)
% 2.64/0.95      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 2.64/0.95      inference(instantiation,[status(thm)],[c_10]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_170,plain,
% 2.64/0.95      ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 2.64/0.95      inference(global_propositional_subsumption,
% 2.64/0.95                [status(thm)],
% 2.64/0.95                [c_168,c_15,c_14,c_13,c_23]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_9,plain,
% 2.64/0.95      ( ~ v1_funct_1(X0)
% 2.64/0.95      | ~ v2_funct_1(X0)
% 2.64/0.95      | ~ v1_relat_1(X0)
% 2.64/0.95      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.64/0.95      inference(cnf_transformation,[],[f36]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_175,plain,
% 2.64/0.95      ( ~ v1_funct_1(X0)
% 2.64/0.95      | ~ v1_relat_1(X0)
% 2.64/0.95      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.64/0.95      | sK0 != X0 ),
% 2.64/0.95      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_176,plain,
% 2.64/0.95      ( ~ v1_funct_1(sK0)
% 2.64/0.95      | ~ v1_relat_1(sK0)
% 2.64/0.95      | k2_funct_1(sK0) = k4_relat_1(sK0) ),
% 2.64/0.95      inference(unflattening,[status(thm)],[c_175]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_26,plain,
% 2.64/0.95      ( ~ v1_funct_1(sK0)
% 2.64/0.95      | ~ v2_funct_1(sK0)
% 2.64/0.95      | ~ v1_relat_1(sK0)
% 2.64/0.95      | k2_funct_1(sK0) = k4_relat_1(sK0) ),
% 2.64/0.95      inference(instantiation,[status(thm)],[c_9]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_178,plain,
% 2.64/0.95      ( k2_funct_1(sK0) = k4_relat_1(sK0) ),
% 2.64/0.95      inference(global_propositional_subsumption,
% 2.64/0.95                [status(thm)],
% 2.64/0.95                [c_176,c_15,c_14,c_13,c_26]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_424,plain,
% 2.64/0.95      ( k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0) ),
% 2.64/0.95      inference(light_normalisation,[status(thm)],[c_170,c_178]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_2543,plain,
% 2.64/0.95      ( k8_relat_1(k1_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(sK0) ),
% 2.64/0.95      inference(light_normalisation,[status(thm)],[c_2541,c_424]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_2,plain,
% 2.64/0.95      ( ~ v1_relat_1(X0)
% 2.64/0.95      | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 2.64/0.95      inference(cnf_transformation,[],[f29]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_411,plain,
% 2.64/0.95      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 2.64/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.64/0.95      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_1260,plain,
% 2.64/0.95      ( k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k4_relat_1(X0))
% 2.64/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.64/0.95      inference(superposition,[status(thm)],[c_413,c_411]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_3225,plain,
% 2.64/0.95      ( k5_relat_1(k4_relat_1(sK0),k6_relat_1(X0)) = k8_relat_1(X0,k4_relat_1(sK0)) ),
% 2.64/0.95      inference(superposition,[status(thm)],[c_406,c_1260]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_1,plain,
% 2.64/0.95      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.64/0.95      inference(cnf_transformation,[],[f28]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_412,plain,
% 2.64/0.95      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.64/0.95      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_6,plain,
% 2.64/0.95      ( ~ v1_relat_1(X0)
% 2.64/0.95      | ~ v1_relat_1(X1)
% 2.64/0.95      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 2.64/0.95      inference(cnf_transformation,[],[f33]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_407,plain,
% 2.64/0.95      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 2.64/0.95      | v1_relat_1(X0) != iProver_top
% 2.64/0.95      | v1_relat_1(X1) != iProver_top ),
% 2.64/0.95      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_621,plain,
% 2.64/0.95      ( k10_relat_1(k4_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k4_relat_1(X0),X1))
% 2.64/0.95      | v1_relat_1(X0) != iProver_top
% 2.64/0.95      | v1_relat_1(X1) != iProver_top ),
% 2.64/0.95      inference(superposition,[status(thm)],[c_413,c_407]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_2390,plain,
% 2.64/0.95      ( k10_relat_1(k4_relat_1(sK0),k1_relat_1(X0)) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0))
% 2.64/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.64/0.95      inference(superposition,[status(thm)],[c_406,c_621]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_2739,plain,
% 2.64/0.95      ( k10_relat_1(k4_relat_1(sK0),k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),k6_relat_1(X0))) ),
% 2.64/0.95      inference(superposition,[status(thm)],[c_412,c_2390]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_8,plain,
% 2.64/0.95      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.64/0.95      inference(cnf_transformation,[],[f34]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_2744,plain,
% 2.64/0.95      ( k1_relat_1(k5_relat_1(k4_relat_1(sK0),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK0),X0) ),
% 2.64/0.95      inference(light_normalisation,[status(thm)],[c_2739,c_8]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_3240,plain,
% 2.64/0.95      ( k1_relat_1(k8_relat_1(X0,k4_relat_1(sK0))) = k10_relat_1(k4_relat_1(sK0),X0) ),
% 2.64/0.95      inference(demodulation,[status(thm)],[c_3225,c_2744]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_3414,plain,
% 2.64/0.95      ( k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) = k1_relat_1(k4_relat_1(sK0)) ),
% 2.64/0.95      inference(superposition,[status(thm)],[c_2543,c_3240]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_11,plain,
% 2.64/0.95      ( ~ v1_funct_1(X0)
% 2.64/0.95      | ~ v2_funct_1(X0)
% 2.64/0.95      | ~ v1_relat_1(X0)
% 2.64/0.95      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.64/0.95      inference(cnf_transformation,[],[f37]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_159,plain,
% 2.64/0.95      ( ~ v1_funct_1(X0)
% 2.64/0.95      | ~ v1_relat_1(X0)
% 2.64/0.95      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.64/0.95      | sK0 != X0 ),
% 2.64/0.95      inference(resolution_lifted,[status(thm)],[c_11,c_13]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_160,plain,
% 2.64/0.95      ( ~ v1_funct_1(sK0)
% 2.64/0.95      | ~ v1_relat_1(sK0)
% 2.64/0.95      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.64/0.95      inference(unflattening,[status(thm)],[c_159]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_20,plain,
% 2.64/0.95      ( ~ v1_funct_1(sK0)
% 2.64/0.95      | ~ v2_funct_1(sK0)
% 2.64/0.95      | ~ v1_relat_1(sK0)
% 2.64/0.95      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.64/0.95      inference(instantiation,[status(thm)],[c_11]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_162,plain,
% 2.64/0.95      ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.64/0.95      inference(global_propositional_subsumption,
% 2.64/0.95                [status(thm)],
% 2.64/0.95                [c_160,c_15,c_14,c_13,c_20]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_427,plain,
% 2.64/0.95      ( k1_relat_1(k4_relat_1(sK0)) = k2_relat_1(sK0) ),
% 2.64/0.95      inference(light_normalisation,[status(thm)],[c_162,c_178]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_2740,plain,
% 2.64/0.95      ( k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
% 2.64/0.95      inference(superposition,[status(thm)],[c_406,c_2390]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_3415,plain,
% 2.64/0.95      ( k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) = k2_relat_1(sK0) ),
% 2.64/0.95      inference(light_normalisation,[status(thm)],[c_3414,c_427,c_2740]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_3546,plain,
% 2.64/0.95      ( k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k2_relat_1(sK0) ),
% 2.64/0.95      inference(demodulation,[status(thm)],[c_3415,c_2740]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_5,plain,
% 2.64/0.95      ( ~ v1_relat_1(X0)
% 2.64/0.95      | ~ v1_relat_1(X1)
% 2.64/0.95      | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
% 2.64/0.95      inference(cnf_transformation,[],[f32]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_408,plain,
% 2.64/0.95      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 2.64/0.95      | v1_relat_1(X1) != iProver_top
% 2.64/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.64/0.95      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_1139,plain,
% 2.64/0.95      ( k9_relat_1(sK0,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK0))
% 2.64/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.64/0.95      inference(superposition,[status(thm)],[c_406,c_408]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_1472,plain,
% 2.64/0.95      ( k9_relat_1(sK0,k2_relat_1(k4_relat_1(X0))) = k2_relat_1(k5_relat_1(k4_relat_1(X0),sK0))
% 2.64/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.64/0.95      inference(superposition,[status(thm)],[c_413,c_1139]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_1548,plain,
% 2.64/0.95      ( k9_relat_1(sK0,k2_relat_1(k4_relat_1(sK0))) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
% 2.64/0.95      inference(superposition,[status(thm)],[c_406,c_1472]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_4,plain,
% 2.64/0.95      ( ~ v1_relat_1(X0)
% 2.64/0.95      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.64/0.95      inference(cnf_transformation,[],[f31]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_409,plain,
% 2.64/0.95      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 2.64/0.95      | v1_relat_1(X0) != iProver_top ),
% 2.64/0.95      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_786,plain,
% 2.64/0.95      ( k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(sK0) ),
% 2.64/0.95      inference(superposition,[status(thm)],[c_406,c_409]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_1550,plain,
% 2.64/0.95      ( k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k2_relat_1(sK0) ),
% 2.64/0.95      inference(light_normalisation,[status(thm)],[c_1548,c_424,c_786]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_12,negated_conjecture,
% 2.64/0.95      ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
% 2.64/0.95      | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
% 2.64/0.95      inference(cnf_transformation,[],[f42]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(c_446,plain,
% 2.64/0.95      ( k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) != k2_relat_1(sK0)
% 2.64/0.95      | k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) != k2_relat_1(sK0) ),
% 2.64/0.95      inference(light_normalisation,[status(thm)],[c_12,c_178]) ).
% 2.64/0.95  
% 2.64/0.95  cnf(contradiction,plain,
% 2.64/0.95      ( $false ),
% 2.64/0.95      inference(minisat,[status(thm)],[c_3546,c_1550,c_446]) ).
% 2.64/0.95  
% 2.64/0.95  
% 2.64/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 2.64/0.95  
% 2.64/0.95  ------                               Statistics
% 2.64/0.95  
% 2.64/0.95  ------ General
% 2.64/0.95  
% 2.64/0.95  abstr_ref_over_cycles:                  0
% 2.64/0.95  abstr_ref_under_cycles:                 0
% 2.64/0.95  gc_basic_clause_elim:                   0
% 2.64/0.95  forced_gc_time:                         0
% 2.64/0.95  parsing_time:                           0.009
% 2.64/0.95  unif_index_cands_time:                  0.
% 2.64/0.95  unif_index_add_time:                    0.
% 2.64/0.95  orderings_time:                         0.
% 2.64/0.95  out_proof_time:                         0.007
% 2.64/0.95  total_time:                             0.144
% 2.64/0.95  num_of_symbols:                         44
% 2.64/0.95  num_of_terms:                           3069
% 2.64/0.95  
% 2.64/0.95  ------ Preprocessing
% 2.64/0.95  
% 2.64/0.95  num_of_splits:                          0
% 2.64/0.95  num_of_split_atoms:                     0
% 2.64/0.95  num_of_reused_defs:                     0
% 2.64/0.95  num_eq_ax_congr_red:                    13
% 2.64/0.95  num_of_sem_filtered_clauses:            1
% 2.64/0.95  num_of_subtypes:                        0
% 2.64/0.95  monotx_restored_types:                  0
% 2.64/0.95  sat_num_of_epr_types:                   0
% 2.64/0.95  sat_num_of_non_cyclic_types:            0
% 2.64/0.95  sat_guarded_non_collapsed_types:        0
% 2.64/0.95  num_pure_diseq_elim:                    0
% 2.64/0.95  simp_replaced_by:                       0
% 2.64/0.95  res_preprocessed:                       81
% 2.64/0.95  prep_upred:                             0
% 2.64/0.95  prep_unflattend:                        3
% 2.64/0.95  smt_new_axioms:                         0
% 2.64/0.95  pred_elim_cands:                        1
% 2.64/0.95  pred_elim:                              2
% 2.64/0.95  pred_elim_cl:                           2
% 2.64/0.95  pred_elim_cycles:                       4
% 2.64/0.95  merged_defs:                            0
% 2.64/0.95  merged_defs_ncl:                        0
% 2.64/0.95  bin_hyper_res:                          0
% 2.64/0.95  prep_cycles:                            4
% 2.64/0.95  pred_elim_time:                         0.001
% 2.64/0.95  splitting_time:                         0.
% 2.64/0.95  sem_filter_time:                        0.
% 2.64/0.95  monotx_time:                            0.001
% 2.64/0.95  subtype_inf_time:                       0.
% 2.64/0.95  
% 2.64/0.95  ------ Problem properties
% 2.64/0.95  
% 2.64/0.95  clauses:                                14
% 2.64/0.95  conjectures:                            2
% 2.64/0.95  epr:                                    1
% 2.64/0.95  horn:                                   14
% 2.64/0.95  ground:                                 5
% 2.64/0.95  unary:                                  7
% 2.64/0.95  binary:                                 5
% 2.64/0.95  lits:                                   23
% 2.64/0.95  lits_eq:                                12
% 2.64/0.95  fd_pure:                                0
% 2.64/0.95  fd_pseudo:                              0
% 2.64/0.95  fd_cond:                                0
% 2.64/0.95  fd_pseudo_cond:                         0
% 2.64/0.95  ac_symbols:                             0
% 2.64/0.95  
% 2.64/0.95  ------ Propositional Solver
% 2.64/0.95  
% 2.64/0.95  prop_solver_calls:                      30
% 2.64/0.95  prop_fast_solver_calls:                 409
% 2.64/0.95  smt_solver_calls:                       0
% 2.64/0.95  smt_fast_solver_calls:                  0
% 2.64/0.95  prop_num_of_clauses:                    1341
% 2.64/0.95  prop_preprocess_simplified:             3675
% 2.64/0.95  prop_fo_subsumed:                       6
% 2.64/0.95  prop_solver_time:                       0.
% 2.64/0.95  smt_solver_time:                        0.
% 2.64/0.95  smt_fast_solver_time:                   0.
% 2.64/0.95  prop_fast_solver_time:                  0.
% 2.64/0.95  prop_unsat_core_time:                   0.
% 2.64/0.95  
% 2.64/0.95  ------ QBF
% 2.64/0.95  
% 2.64/0.95  qbf_q_res:                              0
% 2.64/0.95  qbf_num_tautologies:                    0
% 2.64/0.95  qbf_prep_cycles:                        0
% 2.64/0.95  
% 2.64/0.95  ------ BMC1
% 2.64/0.95  
% 2.64/0.95  bmc1_current_bound:                     -1
% 2.64/0.95  bmc1_last_solved_bound:                 -1
% 2.64/0.95  bmc1_unsat_core_size:                   -1
% 2.64/0.95  bmc1_unsat_core_parents_size:           -1
% 2.64/0.95  bmc1_merge_next_fun:                    0
% 2.64/0.95  bmc1_unsat_core_clauses_time:           0.
% 2.64/0.95  
% 2.64/0.95  ------ Instantiation
% 2.64/0.95  
% 2.64/0.95  inst_num_of_clauses:                    794
% 2.64/0.95  inst_num_in_passive:                    122
% 2.64/0.95  inst_num_in_active:                     334
% 2.64/0.95  inst_num_in_unprocessed:                338
% 2.64/0.95  inst_num_of_loops:                      340
% 2.64/0.95  inst_num_of_learning_restarts:          0
% 2.64/0.95  inst_num_moves_active_passive:          1
% 2.64/0.95  inst_lit_activity:                      0
% 2.64/0.95  inst_lit_activity_moves:                0
% 2.64/0.95  inst_num_tautologies:                   0
% 2.64/0.95  inst_num_prop_implied:                  0
% 2.64/0.95  inst_num_existing_simplified:           0
% 2.64/0.95  inst_num_eq_res_simplified:             0
% 2.64/0.95  inst_num_child_elim:                    0
% 2.64/0.95  inst_num_of_dismatching_blockings:      354
% 2.64/0.95  inst_num_of_non_proper_insts:           763
% 2.64/0.95  inst_num_of_duplicates:                 0
% 2.64/0.95  inst_inst_num_from_inst_to_res:         0
% 2.64/0.95  inst_dismatching_checking_time:         0.
% 2.64/0.95  
% 2.64/0.95  ------ Resolution
% 2.64/0.95  
% 2.64/0.95  res_num_of_clauses:                     0
% 2.64/0.95  res_num_in_passive:                     0
% 2.64/0.95  res_num_in_active:                      0
% 2.64/0.95  res_num_of_loops:                       85
% 2.64/0.95  res_forward_subset_subsumed:            139
% 2.64/0.95  res_backward_subset_subsumed:           4
% 2.64/0.95  res_forward_subsumed:                   0
% 2.64/0.95  res_backward_subsumed:                  0
% 2.64/0.95  res_forward_subsumption_resolution:     0
% 2.64/0.95  res_backward_subsumption_resolution:    0
% 2.64/0.95  res_clause_to_clause_subsumption:       168
% 2.64/0.95  res_orphan_elimination:                 0
% 2.64/0.95  res_tautology_del:                      129
% 2.64/0.95  res_num_eq_res_simplified:              0
% 2.64/0.95  res_num_sel_changes:                    0
% 2.64/0.95  res_moves_from_active_to_pass:          0
% 2.64/0.95  
% 2.64/0.95  ------ Superposition
% 2.64/0.95  
% 2.64/0.95  sup_time_total:                         0.
% 2.64/0.95  sup_time_generating:                    0.
% 2.64/0.95  sup_time_sim_full:                      0.
% 2.64/0.95  sup_time_sim_immed:                     0.
% 2.64/0.95  
% 2.64/0.95  sup_num_of_clauses:                     78
% 2.64/0.95  sup_num_in_active:                      60
% 2.64/0.95  sup_num_in_passive:                     18
% 2.64/0.95  sup_num_of_loops:                       66
% 2.64/0.95  sup_fw_superposition:                   63
% 2.64/0.95  sup_bw_superposition:                   2
% 2.64/0.95  sup_immediate_simplified:               15
% 2.64/0.95  sup_given_eliminated:                   0
% 2.64/0.95  comparisons_done:                       0
% 2.64/0.95  comparisons_avoided:                    0
% 2.64/0.95  
% 2.64/0.95  ------ Simplifications
% 2.64/0.95  
% 2.64/0.95  
% 2.64/0.95  sim_fw_subset_subsumed:                 0
% 2.64/0.95  sim_bw_subset_subsumed:                 0
% 2.64/0.95  sim_fw_subsumed:                        0
% 2.64/0.95  sim_bw_subsumed:                        0
% 2.64/0.95  sim_fw_subsumption_res:                 0
% 2.64/0.95  sim_bw_subsumption_res:                 0
% 2.64/0.95  sim_tautology_del:                      0
% 2.64/0.95  sim_eq_tautology_del:                   0
% 2.64/0.95  sim_eq_res_simp:                        1
% 2.64/0.95  sim_fw_demodulated:                     1
% 2.64/0.95  sim_bw_demodulated:                     6
% 2.64/0.95  sim_light_normalised:                   17
% 2.64/0.95  sim_joinable_taut:                      0
% 2.64/0.95  sim_joinable_simp:                      0
% 2.64/0.95  sim_ac_normalised:                      0
% 2.64/0.95  sim_smt_subsumption:                    0
% 2.64/0.95  
%------------------------------------------------------------------------------
