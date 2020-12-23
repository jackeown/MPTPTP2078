%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:37 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 744 expanded)
%              Number of clauses        :   80 ( 242 expanded)
%              Number of leaves         :   14 ( 145 expanded)
%              Depth                    :   18
%              Number of atoms          :  333 (2942 expanded)
%              Number of equality atoms :  181 (1177 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) != k2_relat_1(X0) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) != k2_relat_1(X0) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,
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

fof(f31,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f46,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f44,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_449,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_764,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_461,plain,
    ( ~ v1_relat_1(X0_42)
    | k9_relat_1(X0_42,k1_relat_1(X0_42)) = k2_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_753,plain,
    ( k9_relat_1(X0_42,k1_relat_1(X0_42)) = k2_relat_1(X0_42)
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_1067,plain,
    ( k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_764,c_753])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_454,plain,
    ( ~ v1_relat_1(X0_42)
    | k5_relat_1(k6_relat_1(X0_41),X0_42) = k7_relat_1(X0_42,X0_41) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_760,plain,
    ( k5_relat_1(k6_relat_1(X0_41),X0_42) = k7_relat_1(X0_42,X0_41)
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_1207,plain,
    ( k5_relat_1(k6_relat_1(X0_41),sK0) = k7_relat_1(sK0,X0_41) ),
    inference(superposition,[status(thm)],[c_764,c_760])).

cnf(c_6,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_457,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0_42,X1_42)),k2_relat_1(X1_42))
    | ~ v1_relat_1(X0_42)
    | ~ v1_relat_1(X1_42) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_757,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0_42,X1_42)),k2_relat_1(X1_42)) = iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_1664,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK0,X0_41)),k2_relat_1(sK0)) = iProver_top
    | v1_relat_1(k6_relat_1(X0_41)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_757])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_460,plain,
    ( ~ v1_relat_1(X0_42)
    | k2_relat_1(k7_relat_1(X0_42,X0_41)) = k9_relat_1(X0_42,X0_41) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_754,plain,
    ( k2_relat_1(k7_relat_1(X0_42,X0_41)) = k9_relat_1(X0_42,X0_41)
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_1188,plain,
    ( k2_relat_1(k7_relat_1(sK0,X0_41)) = k9_relat_1(sK0,X0_41) ),
    inference(superposition,[status(thm)],[c_764,c_754])).

cnf(c_1696,plain,
    ( r1_tarski(k9_relat_1(sK0,X0_41),k2_relat_1(sK0)) = iProver_top
    | v1_relat_1(k6_relat_1(X0_41)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1664,c_1188])).

cnf(c_18,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_462,plain,
    ( v1_relat_1(k6_relat_1(X0_41)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_489,plain,
    ( v1_relat_1(k6_relat_1(X0_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_2875,plain,
    ( r1_tarski(k9_relat_1(sK0,X0_41),k2_relat_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1696,c_18,c_489])).

cnf(c_2882,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1067,c_2875])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_200,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_201,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_22,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_203,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_201,c_17,c_16,c_15,c_22])).

cnf(c_448,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_203])).

cnf(c_8,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_455,plain,
    ( ~ r1_tarski(k1_relat_1(X0_42),k2_relat_1(X1_42))
    | ~ v1_relat_1(X0_42)
    | ~ v1_relat_1(X1_42)
    | k2_relat_1(k5_relat_1(X1_42,X0_42)) = k2_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_759,plain,
    ( k2_relat_1(k5_relat_1(X0_42,X1_42)) = k2_relat_1(X1_42)
    | r1_tarski(k1_relat_1(X1_42),k2_relat_1(X0_42)) != iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_2129,plain,
    ( k2_relat_1(k5_relat_1(X0_42,k2_funct_1(sK0))) = k2_relat_1(k2_funct_1(sK0))
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(X0_42)) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_448,c_759])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_208,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_209,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_208])).

cnf(c_25,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_211,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_209,c_17,c_16,c_15,c_25])).

cnf(c_447,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_211])).

cnf(c_2190,plain,
    ( k2_relat_1(k5_relat_1(X0_42,k2_funct_1(sK0))) = k1_relat_1(sK0)
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(X0_42)) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2129,c_447])).

cnf(c_19,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_27,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_29,plain,
    ( v1_funct_1(sK0) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2826,plain,
    ( v1_relat_1(X0_42) != iProver_top
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(X0_42)) != iProver_top
    | k2_relat_1(k5_relat_1(X0_42,k2_funct_1(sK0))) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2190,c_18,c_19,c_29])).

cnf(c_2827,plain,
    ( k2_relat_1(k5_relat_1(X0_42,k2_funct_1(sK0))) = k1_relat_1(sK0)
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(X0_42)) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(renaming,[status(thm)],[c_2826])).

cnf(c_3486,plain,
    ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2882,c_2827])).

cnf(c_2829,plain,
    ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(sK0)
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2827])).

cnf(c_3818,plain,
    ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3486,c_18,c_2829,c_2882])).

cnf(c_1665,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0_42,k2_funct_1(sK0))),k1_relat_1(sK0)) = iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_447,c_757])).

cnf(c_2330,plain,
    ( v1_relat_1(X0_42) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(X0_42,k2_funct_1(sK0))),k1_relat_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1665,c_18,c_19,c_29])).

cnf(c_2331,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0_42,k2_funct_1(sK0))),k1_relat_1(sK0)) = iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(renaming,[status(thm)],[c_2330])).

cnf(c_3827,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3818,c_2331])).

cnf(c_2132,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0_42)) = k2_relat_1(X0_42)
    | r1_tarski(k1_relat_1(X0_42),k1_relat_1(sK0)) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_447,c_759])).

cnf(c_2658,plain,
    ( v1_relat_1(X0_42) != iProver_top
    | r1_tarski(k1_relat_1(X0_42),k1_relat_1(sK0)) != iProver_top
    | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0_42)) = k2_relat_1(X0_42) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2132,c_18,c_19,c_29])).

cnf(c_2659,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0_42)) = k2_relat_1(X0_42)
    | r1_tarski(k1_relat_1(X0_42),k1_relat_1(sK0)) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(renaming,[status(thm)],[c_2658])).

cnf(c_2661,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2659])).

cnf(c_7,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_456,plain,
    ( ~ r1_tarski(k2_relat_1(X0_42),k1_relat_1(X1_42))
    | ~ v1_relat_1(X0_42)
    | ~ v1_relat_1(X1_42)
    | k1_relat_1(k5_relat_1(X0_42,X1_42)) = k1_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_758,plain,
    ( k1_relat_1(k5_relat_1(X0_42,X1_42)) = k1_relat_1(X0_42)
    | r1_tarski(k2_relat_1(X0_42),k1_relat_1(X1_42)) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_1893,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0_42)) = k1_relat_1(k2_funct_1(sK0))
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0_42)) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_447,c_758])).

cnf(c_1954,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0_42)) = k2_relat_1(sK0)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0_42)) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1893,c_448])).

cnf(c_2543,plain,
    ( v1_relat_1(X0_42) != iProver_top
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0_42)) != iProver_top
    | k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0_42)) = k2_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1954,c_18,c_19,c_29])).

cnf(c_2544,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0_42)) = k2_relat_1(sK0)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0_42)) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(renaming,[status(thm)],[c_2543])).

cnf(c_2546,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2544])).

cnf(c_467,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_876,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != X0_41
    | k2_relat_1(sK0) != X0_41
    | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_888,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)
    | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_14,negated_conjecture,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_451,negated_conjecture,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_466,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_487,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_472,plain,
    ( X0_42 != X1_42
    | k2_relat_1(X0_42) = k2_relat_1(X1_42) ),
    theory(equality)).

cnf(c_480,plain,
    ( sK0 != sK0
    | k2_relat_1(sK0) = k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_472])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3827,c_2661,c_2546,c_888,c_451,c_487,c_480,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:35:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.99/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/0.98  
% 2.99/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.99/0.98  
% 2.99/0.98  ------  iProver source info
% 2.99/0.98  
% 2.99/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.99/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.99/0.98  git: non_committed_changes: false
% 2.99/0.98  git: last_make_outside_of_git: false
% 2.99/0.98  
% 2.99/0.98  ------ 
% 2.99/0.98  
% 2.99/0.98  ------ Input Options
% 2.99/0.98  
% 2.99/0.98  --out_options                           all
% 2.99/0.98  --tptp_safe_out                         true
% 2.99/0.98  --problem_path                          ""
% 2.99/0.98  --include_path                          ""
% 2.99/0.98  --clausifier                            res/vclausify_rel
% 2.99/0.98  --clausifier_options                    --mode clausify
% 2.99/0.98  --stdin                                 false
% 2.99/0.98  --stats_out                             all
% 2.99/0.98  
% 2.99/0.98  ------ General Options
% 2.99/0.98  
% 2.99/0.98  --fof                                   false
% 2.99/0.98  --time_out_real                         305.
% 2.99/0.98  --time_out_virtual                      -1.
% 2.99/0.98  --symbol_type_check                     false
% 2.99/0.98  --clausify_out                          false
% 2.99/0.98  --sig_cnt_out                           false
% 2.99/0.98  --trig_cnt_out                          false
% 2.99/0.98  --trig_cnt_out_tolerance                1.
% 2.99/0.98  --trig_cnt_out_sk_spl                   false
% 2.99/0.98  --abstr_cl_out                          false
% 2.99/0.98  
% 2.99/0.98  ------ Global Options
% 2.99/0.98  
% 2.99/0.98  --schedule                              default
% 2.99/0.98  --add_important_lit                     false
% 2.99/0.98  --prop_solver_per_cl                    1000
% 2.99/0.98  --min_unsat_core                        false
% 2.99/0.98  --soft_assumptions                      false
% 2.99/0.98  --soft_lemma_size                       3
% 2.99/0.98  --prop_impl_unit_size                   0
% 2.99/0.98  --prop_impl_unit                        []
% 2.99/0.98  --share_sel_clauses                     true
% 2.99/0.98  --reset_solvers                         false
% 2.99/0.98  --bc_imp_inh                            [conj_cone]
% 2.99/0.98  --conj_cone_tolerance                   3.
% 2.99/0.98  --extra_neg_conj                        none
% 2.99/0.98  --large_theory_mode                     true
% 2.99/0.98  --prolific_symb_bound                   200
% 2.99/0.98  --lt_threshold                          2000
% 2.99/0.98  --clause_weak_htbl                      true
% 2.99/0.98  --gc_record_bc_elim                     false
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing Options
% 2.99/0.98  
% 2.99/0.98  --preprocessing_flag                    true
% 2.99/0.98  --time_out_prep_mult                    0.1
% 2.99/0.98  --splitting_mode                        input
% 2.99/0.98  --splitting_grd                         true
% 2.99/0.98  --splitting_cvd                         false
% 2.99/0.98  --splitting_cvd_svl                     false
% 2.99/0.98  --splitting_nvd                         32
% 2.99/0.98  --sub_typing                            true
% 2.99/0.98  --prep_gs_sim                           true
% 2.99/0.98  --prep_unflatten                        true
% 2.99/0.98  --prep_res_sim                          true
% 2.99/0.98  --prep_upred                            true
% 2.99/0.98  --prep_sem_filter                       exhaustive
% 2.99/0.98  --prep_sem_filter_out                   false
% 2.99/0.98  --pred_elim                             true
% 2.99/0.98  --res_sim_input                         true
% 2.99/0.98  --eq_ax_congr_red                       true
% 2.99/0.98  --pure_diseq_elim                       true
% 2.99/0.98  --brand_transform                       false
% 2.99/0.98  --non_eq_to_eq                          false
% 2.99/0.98  --prep_def_merge                        true
% 2.99/0.98  --prep_def_merge_prop_impl              false
% 2.99/0.98  --prep_def_merge_mbd                    true
% 2.99/0.98  --prep_def_merge_tr_red                 false
% 2.99/0.98  --prep_def_merge_tr_cl                  false
% 2.99/0.98  --smt_preprocessing                     true
% 2.99/0.98  --smt_ac_axioms                         fast
% 2.99/0.98  --preprocessed_out                      false
% 2.99/0.98  --preprocessed_stats                    false
% 2.99/0.98  
% 2.99/0.98  ------ Abstraction refinement Options
% 2.99/0.98  
% 2.99/0.98  --abstr_ref                             []
% 2.99/0.98  --abstr_ref_prep                        false
% 2.99/0.98  --abstr_ref_until_sat                   false
% 2.99/0.98  --abstr_ref_sig_restrict                funpre
% 2.99/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.98  --abstr_ref_under                       []
% 2.99/0.98  
% 2.99/0.98  ------ SAT Options
% 2.99/0.98  
% 2.99/0.98  --sat_mode                              false
% 2.99/0.98  --sat_fm_restart_options                ""
% 2.99/0.98  --sat_gr_def                            false
% 2.99/0.98  --sat_epr_types                         true
% 2.99/0.98  --sat_non_cyclic_types                  false
% 2.99/0.98  --sat_finite_models                     false
% 2.99/0.98  --sat_fm_lemmas                         false
% 2.99/0.98  --sat_fm_prep                           false
% 2.99/0.98  --sat_fm_uc_incr                        true
% 2.99/0.98  --sat_out_model                         small
% 2.99/0.98  --sat_out_clauses                       false
% 2.99/0.98  
% 2.99/0.98  ------ QBF Options
% 2.99/0.98  
% 2.99/0.98  --qbf_mode                              false
% 2.99/0.98  --qbf_elim_univ                         false
% 2.99/0.98  --qbf_dom_inst                          none
% 2.99/0.98  --qbf_dom_pre_inst                      false
% 2.99/0.98  --qbf_sk_in                             false
% 2.99/0.98  --qbf_pred_elim                         true
% 2.99/0.98  --qbf_split                             512
% 2.99/0.98  
% 2.99/0.98  ------ BMC1 Options
% 2.99/0.98  
% 2.99/0.98  --bmc1_incremental                      false
% 2.99/0.98  --bmc1_axioms                           reachable_all
% 2.99/0.98  --bmc1_min_bound                        0
% 2.99/0.98  --bmc1_max_bound                        -1
% 2.99/0.98  --bmc1_max_bound_default                -1
% 2.99/0.98  --bmc1_symbol_reachability              true
% 2.99/0.98  --bmc1_property_lemmas                  false
% 2.99/0.98  --bmc1_k_induction                      false
% 2.99/0.98  --bmc1_non_equiv_states                 false
% 2.99/0.98  --bmc1_deadlock                         false
% 2.99/0.98  --bmc1_ucm                              false
% 2.99/0.98  --bmc1_add_unsat_core                   none
% 2.99/0.98  --bmc1_unsat_core_children              false
% 2.99/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.98  --bmc1_out_stat                         full
% 2.99/0.98  --bmc1_ground_init                      false
% 2.99/0.98  --bmc1_pre_inst_next_state              false
% 2.99/0.98  --bmc1_pre_inst_state                   false
% 2.99/0.98  --bmc1_pre_inst_reach_state             false
% 2.99/0.98  --bmc1_out_unsat_core                   false
% 2.99/0.98  --bmc1_aig_witness_out                  false
% 2.99/0.98  --bmc1_verbose                          false
% 2.99/0.98  --bmc1_dump_clauses_tptp                false
% 2.99/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.98  --bmc1_dump_file                        -
% 2.99/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.98  --bmc1_ucm_extend_mode                  1
% 2.99/0.98  --bmc1_ucm_init_mode                    2
% 2.99/0.98  --bmc1_ucm_cone_mode                    none
% 2.99/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.98  --bmc1_ucm_relax_model                  4
% 2.99/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.98  --bmc1_ucm_layered_model                none
% 2.99/0.98  --bmc1_ucm_max_lemma_size               10
% 2.99/0.98  
% 2.99/0.98  ------ AIG Options
% 2.99/0.98  
% 2.99/0.98  --aig_mode                              false
% 2.99/0.98  
% 2.99/0.98  ------ Instantiation Options
% 2.99/0.98  
% 2.99/0.98  --instantiation_flag                    true
% 2.99/0.98  --inst_sos_flag                         false
% 2.99/0.98  --inst_sos_phase                        true
% 2.99/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.98  --inst_lit_sel_side                     num_symb
% 2.99/0.98  --inst_solver_per_active                1400
% 2.99/0.98  --inst_solver_calls_frac                1.
% 2.99/0.98  --inst_passive_queue_type               priority_queues
% 2.99/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.98  --inst_passive_queues_freq              [25;2]
% 2.99/0.98  --inst_dismatching                      true
% 2.99/0.98  --inst_eager_unprocessed_to_passive     true
% 2.99/0.98  --inst_prop_sim_given                   true
% 2.99/0.98  --inst_prop_sim_new                     false
% 2.99/0.98  --inst_subs_new                         false
% 2.99/0.98  --inst_eq_res_simp                      false
% 2.99/0.98  --inst_subs_given                       false
% 2.99/0.98  --inst_orphan_elimination               true
% 2.99/0.98  --inst_learning_loop_flag               true
% 2.99/0.98  --inst_learning_start                   3000
% 2.99/0.98  --inst_learning_factor                  2
% 2.99/0.98  --inst_start_prop_sim_after_learn       3
% 2.99/0.98  --inst_sel_renew                        solver
% 2.99/0.98  --inst_lit_activity_flag                true
% 2.99/0.98  --inst_restr_to_given                   false
% 2.99/0.98  --inst_activity_threshold               500
% 2.99/0.98  --inst_out_proof                        true
% 2.99/0.98  
% 2.99/0.98  ------ Resolution Options
% 2.99/0.98  
% 2.99/0.98  --resolution_flag                       true
% 2.99/0.98  --res_lit_sel                           adaptive
% 2.99/0.98  --res_lit_sel_side                      none
% 2.99/0.98  --res_ordering                          kbo
% 2.99/0.98  --res_to_prop_solver                    active
% 2.99/0.98  --res_prop_simpl_new                    false
% 2.99/0.98  --res_prop_simpl_given                  true
% 2.99/0.98  --res_passive_queue_type                priority_queues
% 2.99/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.98  --res_passive_queues_freq               [15;5]
% 2.99/0.98  --res_forward_subs                      full
% 2.99/0.98  --res_backward_subs                     full
% 2.99/0.98  --res_forward_subs_resolution           true
% 2.99/0.98  --res_backward_subs_resolution          true
% 2.99/0.98  --res_orphan_elimination                true
% 2.99/0.98  --res_time_limit                        2.
% 2.99/0.98  --res_out_proof                         true
% 2.99/0.98  
% 2.99/0.98  ------ Superposition Options
% 2.99/0.98  
% 2.99/0.98  --superposition_flag                    true
% 2.99/0.98  --sup_passive_queue_type                priority_queues
% 2.99/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.98  --demod_completeness_check              fast
% 2.99/0.98  --demod_use_ground                      true
% 2.99/0.98  --sup_to_prop_solver                    passive
% 2.99/0.98  --sup_prop_simpl_new                    true
% 2.99/0.98  --sup_prop_simpl_given                  true
% 2.99/0.98  --sup_fun_splitting                     false
% 2.99/0.98  --sup_smt_interval                      50000
% 2.99/0.98  
% 2.99/0.98  ------ Superposition Simplification Setup
% 2.99/0.98  
% 2.99/0.98  --sup_indices_passive                   []
% 2.99/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.98  --sup_full_bw                           [BwDemod]
% 2.99/0.98  --sup_immed_triv                        [TrivRules]
% 2.99/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.98  --sup_immed_bw_main                     []
% 2.99/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.98  
% 2.99/0.98  ------ Combination Options
% 2.99/0.98  
% 2.99/0.98  --comb_res_mult                         3
% 2.99/0.98  --comb_sup_mult                         2
% 2.99/0.98  --comb_inst_mult                        10
% 2.99/0.98  
% 2.99/0.98  ------ Debug Options
% 2.99/0.98  
% 2.99/0.98  --dbg_backtrace                         false
% 2.99/0.98  --dbg_dump_prop_clauses                 false
% 2.99/0.98  --dbg_dump_prop_clauses_file            -
% 2.99/0.98  --dbg_out_stat                          false
% 2.99/0.98  ------ Parsing...
% 2.99/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.99/0.98  ------ Proving...
% 2.99/0.98  ------ Problem Properties 
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  clauses                                 17
% 2.99/0.98  conjectures                             3
% 2.99/0.98  EPR                                     2
% 2.99/0.98  Horn                                    17
% 2.99/0.98  unary                                   5
% 2.99/0.98  binary                                  7
% 2.99/0.98  lits                                    36
% 2.99/0.98  lits eq                                 11
% 2.99/0.98  fd_pure                                 0
% 2.99/0.98  fd_pseudo                               0
% 2.99/0.98  fd_cond                                 0
% 2.99/0.98  fd_pseudo_cond                          0
% 2.99/0.98  AC symbols                              0
% 2.99/0.98  
% 2.99/0.98  ------ Schedule dynamic 5 is on 
% 2.99/0.98  
% 2.99/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  ------ 
% 2.99/0.98  Current options:
% 2.99/0.98  ------ 
% 2.99/0.98  
% 2.99/0.98  ------ Input Options
% 2.99/0.98  
% 2.99/0.98  --out_options                           all
% 2.99/0.98  --tptp_safe_out                         true
% 2.99/0.98  --problem_path                          ""
% 2.99/0.98  --include_path                          ""
% 2.99/0.98  --clausifier                            res/vclausify_rel
% 2.99/0.98  --clausifier_options                    --mode clausify
% 2.99/0.98  --stdin                                 false
% 2.99/0.98  --stats_out                             all
% 2.99/0.98  
% 2.99/0.98  ------ General Options
% 2.99/0.98  
% 2.99/0.98  --fof                                   false
% 2.99/0.98  --time_out_real                         305.
% 2.99/0.98  --time_out_virtual                      -1.
% 2.99/0.98  --symbol_type_check                     false
% 2.99/0.98  --clausify_out                          false
% 2.99/0.98  --sig_cnt_out                           false
% 2.99/0.98  --trig_cnt_out                          false
% 2.99/0.98  --trig_cnt_out_tolerance                1.
% 2.99/0.98  --trig_cnt_out_sk_spl                   false
% 2.99/0.98  --abstr_cl_out                          false
% 2.99/0.98  
% 2.99/0.98  ------ Global Options
% 2.99/0.98  
% 2.99/0.98  --schedule                              default
% 2.99/0.98  --add_important_lit                     false
% 2.99/0.98  --prop_solver_per_cl                    1000
% 2.99/0.98  --min_unsat_core                        false
% 2.99/0.98  --soft_assumptions                      false
% 2.99/0.98  --soft_lemma_size                       3
% 2.99/0.98  --prop_impl_unit_size                   0
% 2.99/0.98  --prop_impl_unit                        []
% 2.99/0.98  --share_sel_clauses                     true
% 2.99/0.98  --reset_solvers                         false
% 2.99/0.98  --bc_imp_inh                            [conj_cone]
% 2.99/0.98  --conj_cone_tolerance                   3.
% 2.99/0.98  --extra_neg_conj                        none
% 2.99/0.98  --large_theory_mode                     true
% 2.99/0.98  --prolific_symb_bound                   200
% 2.99/0.98  --lt_threshold                          2000
% 2.99/0.98  --clause_weak_htbl                      true
% 2.99/0.98  --gc_record_bc_elim                     false
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing Options
% 2.99/0.98  
% 2.99/0.98  --preprocessing_flag                    true
% 2.99/0.98  --time_out_prep_mult                    0.1
% 2.99/0.98  --splitting_mode                        input
% 2.99/0.98  --splitting_grd                         true
% 2.99/0.98  --splitting_cvd                         false
% 2.99/0.98  --splitting_cvd_svl                     false
% 2.99/0.98  --splitting_nvd                         32
% 2.99/0.98  --sub_typing                            true
% 2.99/0.98  --prep_gs_sim                           true
% 2.99/0.98  --prep_unflatten                        true
% 2.99/0.98  --prep_res_sim                          true
% 2.99/0.98  --prep_upred                            true
% 2.99/0.98  --prep_sem_filter                       exhaustive
% 2.99/0.98  --prep_sem_filter_out                   false
% 2.99/0.98  --pred_elim                             true
% 2.99/0.98  --res_sim_input                         true
% 2.99/0.98  --eq_ax_congr_red                       true
% 2.99/0.98  --pure_diseq_elim                       true
% 2.99/0.98  --brand_transform                       false
% 2.99/0.98  --non_eq_to_eq                          false
% 2.99/0.98  --prep_def_merge                        true
% 2.99/0.98  --prep_def_merge_prop_impl              false
% 2.99/0.98  --prep_def_merge_mbd                    true
% 2.99/0.98  --prep_def_merge_tr_red                 false
% 2.99/0.98  --prep_def_merge_tr_cl                  false
% 2.99/0.98  --smt_preprocessing                     true
% 2.99/0.98  --smt_ac_axioms                         fast
% 2.99/0.98  --preprocessed_out                      false
% 2.99/0.98  --preprocessed_stats                    false
% 2.99/0.98  
% 2.99/0.98  ------ Abstraction refinement Options
% 2.99/0.98  
% 2.99/0.98  --abstr_ref                             []
% 2.99/0.98  --abstr_ref_prep                        false
% 2.99/0.98  --abstr_ref_until_sat                   false
% 2.99/0.98  --abstr_ref_sig_restrict                funpre
% 2.99/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.99/0.98  --abstr_ref_under                       []
% 2.99/0.98  
% 2.99/0.98  ------ SAT Options
% 2.99/0.98  
% 2.99/0.98  --sat_mode                              false
% 2.99/0.98  --sat_fm_restart_options                ""
% 2.99/0.98  --sat_gr_def                            false
% 2.99/0.98  --sat_epr_types                         true
% 2.99/0.98  --sat_non_cyclic_types                  false
% 2.99/0.98  --sat_finite_models                     false
% 2.99/0.98  --sat_fm_lemmas                         false
% 2.99/0.98  --sat_fm_prep                           false
% 2.99/0.98  --sat_fm_uc_incr                        true
% 2.99/0.98  --sat_out_model                         small
% 2.99/0.98  --sat_out_clauses                       false
% 2.99/0.98  
% 2.99/0.98  ------ QBF Options
% 2.99/0.98  
% 2.99/0.98  --qbf_mode                              false
% 2.99/0.98  --qbf_elim_univ                         false
% 2.99/0.98  --qbf_dom_inst                          none
% 2.99/0.98  --qbf_dom_pre_inst                      false
% 2.99/0.98  --qbf_sk_in                             false
% 2.99/0.98  --qbf_pred_elim                         true
% 2.99/0.98  --qbf_split                             512
% 2.99/0.98  
% 2.99/0.98  ------ BMC1 Options
% 2.99/0.98  
% 2.99/0.98  --bmc1_incremental                      false
% 2.99/0.98  --bmc1_axioms                           reachable_all
% 2.99/0.98  --bmc1_min_bound                        0
% 2.99/0.98  --bmc1_max_bound                        -1
% 2.99/0.98  --bmc1_max_bound_default                -1
% 2.99/0.98  --bmc1_symbol_reachability              true
% 2.99/0.98  --bmc1_property_lemmas                  false
% 2.99/0.98  --bmc1_k_induction                      false
% 2.99/0.98  --bmc1_non_equiv_states                 false
% 2.99/0.98  --bmc1_deadlock                         false
% 2.99/0.98  --bmc1_ucm                              false
% 2.99/0.98  --bmc1_add_unsat_core                   none
% 2.99/0.98  --bmc1_unsat_core_children              false
% 2.99/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.99/0.98  --bmc1_out_stat                         full
% 2.99/0.98  --bmc1_ground_init                      false
% 2.99/0.98  --bmc1_pre_inst_next_state              false
% 2.99/0.98  --bmc1_pre_inst_state                   false
% 2.99/0.98  --bmc1_pre_inst_reach_state             false
% 2.99/0.98  --bmc1_out_unsat_core                   false
% 2.99/0.98  --bmc1_aig_witness_out                  false
% 2.99/0.98  --bmc1_verbose                          false
% 2.99/0.98  --bmc1_dump_clauses_tptp                false
% 2.99/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.99/0.98  --bmc1_dump_file                        -
% 2.99/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.99/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.99/0.98  --bmc1_ucm_extend_mode                  1
% 2.99/0.98  --bmc1_ucm_init_mode                    2
% 2.99/0.98  --bmc1_ucm_cone_mode                    none
% 2.99/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.99/0.98  --bmc1_ucm_relax_model                  4
% 2.99/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.99/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.99/0.98  --bmc1_ucm_layered_model                none
% 2.99/0.98  --bmc1_ucm_max_lemma_size               10
% 2.99/0.98  
% 2.99/0.98  ------ AIG Options
% 2.99/0.98  
% 2.99/0.98  --aig_mode                              false
% 2.99/0.98  
% 2.99/0.98  ------ Instantiation Options
% 2.99/0.98  
% 2.99/0.98  --instantiation_flag                    true
% 2.99/0.98  --inst_sos_flag                         false
% 2.99/0.98  --inst_sos_phase                        true
% 2.99/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.99/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.99/0.98  --inst_lit_sel_side                     none
% 2.99/0.98  --inst_solver_per_active                1400
% 2.99/0.98  --inst_solver_calls_frac                1.
% 2.99/0.98  --inst_passive_queue_type               priority_queues
% 2.99/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.99/0.98  --inst_passive_queues_freq              [25;2]
% 2.99/0.98  --inst_dismatching                      true
% 2.99/0.98  --inst_eager_unprocessed_to_passive     true
% 2.99/0.98  --inst_prop_sim_given                   true
% 2.99/0.98  --inst_prop_sim_new                     false
% 2.99/0.98  --inst_subs_new                         false
% 2.99/0.98  --inst_eq_res_simp                      false
% 2.99/0.98  --inst_subs_given                       false
% 2.99/0.98  --inst_orphan_elimination               true
% 2.99/0.98  --inst_learning_loop_flag               true
% 2.99/0.98  --inst_learning_start                   3000
% 2.99/0.98  --inst_learning_factor                  2
% 2.99/0.98  --inst_start_prop_sim_after_learn       3
% 2.99/0.98  --inst_sel_renew                        solver
% 2.99/0.98  --inst_lit_activity_flag                true
% 2.99/0.98  --inst_restr_to_given                   false
% 2.99/0.98  --inst_activity_threshold               500
% 2.99/0.98  --inst_out_proof                        true
% 2.99/0.98  
% 2.99/0.98  ------ Resolution Options
% 2.99/0.98  
% 2.99/0.98  --resolution_flag                       false
% 2.99/0.98  --res_lit_sel                           adaptive
% 2.99/0.98  --res_lit_sel_side                      none
% 2.99/0.98  --res_ordering                          kbo
% 2.99/0.98  --res_to_prop_solver                    active
% 2.99/0.98  --res_prop_simpl_new                    false
% 2.99/0.98  --res_prop_simpl_given                  true
% 2.99/0.98  --res_passive_queue_type                priority_queues
% 2.99/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.99/0.98  --res_passive_queues_freq               [15;5]
% 2.99/0.98  --res_forward_subs                      full
% 2.99/0.98  --res_backward_subs                     full
% 2.99/0.98  --res_forward_subs_resolution           true
% 2.99/0.98  --res_backward_subs_resolution          true
% 2.99/0.98  --res_orphan_elimination                true
% 2.99/0.98  --res_time_limit                        2.
% 2.99/0.98  --res_out_proof                         true
% 2.99/0.98  
% 2.99/0.98  ------ Superposition Options
% 2.99/0.98  
% 2.99/0.98  --superposition_flag                    true
% 2.99/0.98  --sup_passive_queue_type                priority_queues
% 2.99/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.99/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.99/0.98  --demod_completeness_check              fast
% 2.99/0.98  --demod_use_ground                      true
% 2.99/0.98  --sup_to_prop_solver                    passive
% 2.99/0.98  --sup_prop_simpl_new                    true
% 2.99/0.98  --sup_prop_simpl_given                  true
% 2.99/0.98  --sup_fun_splitting                     false
% 2.99/0.98  --sup_smt_interval                      50000
% 2.99/0.98  
% 2.99/0.98  ------ Superposition Simplification Setup
% 2.99/0.98  
% 2.99/0.98  --sup_indices_passive                   []
% 2.99/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.99/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.99/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.98  --sup_full_bw                           [BwDemod]
% 2.99/0.98  --sup_immed_triv                        [TrivRules]
% 2.99/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.99/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.98  --sup_immed_bw_main                     []
% 2.99/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.99/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.99/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.99/0.98  
% 2.99/0.98  ------ Combination Options
% 2.99/0.98  
% 2.99/0.98  --comb_res_mult                         3
% 2.99/0.98  --comb_sup_mult                         2
% 2.99/0.98  --comb_inst_mult                        10
% 2.99/0.98  
% 2.99/0.98  ------ Debug Options
% 2.99/0.98  
% 2.99/0.98  --dbg_backtrace                         false
% 2.99/0.98  --dbg_dump_prop_clauses                 false
% 2.99/0.98  --dbg_dump_prop_clauses_file            -
% 2.99/0.98  --dbg_out_stat                          false
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  ------ Proving...
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  % SZS status Theorem for theBenchmark.p
% 2.99/0.98  
% 2.99/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.99/0.98  
% 2.99/0.98  fof(f12,conjecture,(
% 2.99/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 2.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f13,negated_conjecture,(
% 2.99/0.98    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 2.99/0.98    inference(negated_conjecture,[],[f12])).
% 2.99/0.98  
% 2.99/0.98  fof(f28,plain,(
% 2.99/0.98    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) != k2_relat_1(X0)) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.99/0.98    inference(ennf_transformation,[],[f13])).
% 2.99/0.98  
% 2.99/0.98  fof(f29,plain,(
% 2.99/0.98    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) != k2_relat_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.99/0.98    inference(flattening,[],[f28])).
% 2.99/0.98  
% 2.99/0.98  fof(f30,plain,(
% 2.99/0.98    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) != k2_relat_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.99/0.98    introduced(choice_axiom,[])).
% 2.99/0.98  
% 2.99/0.98  fof(f31,plain,(
% 2.99/0.98    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.99/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 2.99/0.98  
% 2.99/0.98  fof(f46,plain,(
% 2.99/0.98    v1_relat_1(sK0)),
% 2.99/0.98    inference(cnf_transformation,[],[f31])).
% 2.99/0.98  
% 2.99/0.98  fof(f3,axiom,(
% 2.99/0.98    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f15,plain,(
% 2.99/0.98    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.99/0.98    inference(ennf_transformation,[],[f3])).
% 2.99/0.98  
% 2.99/0.98  fof(f34,plain,(
% 2.99/0.98    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f15])).
% 2.99/0.98  
% 2.99/0.98  fof(f9,axiom,(
% 2.99/0.98    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f23,plain,(
% 2.99/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.99/0.98    inference(ennf_transformation,[],[f9])).
% 2.99/0.98  
% 2.99/0.98  fof(f41,plain,(
% 2.99/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f23])).
% 2.99/0.98  
% 2.99/0.98  fof(f6,axiom,(
% 2.99/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 2.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f18,plain,(
% 2.99/0.98    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.99/0.98    inference(ennf_transformation,[],[f6])).
% 2.99/0.98  
% 2.99/0.98  fof(f38,plain,(
% 2.99/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f18])).
% 2.99/0.98  
% 2.99/0.98  fof(f4,axiom,(
% 2.99/0.98    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f16,plain,(
% 2.99/0.98    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.99/0.98    inference(ennf_transformation,[],[f4])).
% 2.99/0.98  
% 2.99/0.98  fof(f35,plain,(
% 2.99/0.98    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f16])).
% 2.99/0.98  
% 2.99/0.98  fof(f2,axiom,(
% 2.99/0.98    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f33,plain,(
% 2.99/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.99/0.98    inference(cnf_transformation,[],[f2])).
% 2.99/0.98  
% 2.99/0.98  fof(f11,axiom,(
% 2.99/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f26,plain,(
% 2.99/0.98    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.99/0.98    inference(ennf_transformation,[],[f11])).
% 2.99/0.98  
% 2.99/0.98  fof(f27,plain,(
% 2.99/0.98    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.99/0.98    inference(flattening,[],[f26])).
% 2.99/0.98  
% 2.99/0.98  fof(f44,plain,(
% 2.99/0.98    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f27])).
% 2.99/0.98  
% 2.99/0.98  fof(f48,plain,(
% 2.99/0.98    v2_funct_1(sK0)),
% 2.99/0.98    inference(cnf_transformation,[],[f31])).
% 2.99/0.98  
% 2.99/0.98  fof(f47,plain,(
% 2.99/0.98    v1_funct_1(sK0)),
% 2.99/0.98    inference(cnf_transformation,[],[f31])).
% 2.99/0.98  
% 2.99/0.98  fof(f8,axiom,(
% 2.99/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 2.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f21,plain,(
% 2.99/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.99/0.98    inference(ennf_transformation,[],[f8])).
% 2.99/0.98  
% 2.99/0.98  fof(f22,plain,(
% 2.99/0.98    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.99/0.98    inference(flattening,[],[f21])).
% 2.99/0.98  
% 2.99/0.98  fof(f40,plain,(
% 2.99/0.98    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f22])).
% 2.99/0.98  
% 2.99/0.98  fof(f45,plain,(
% 2.99/0.98    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f27])).
% 2.99/0.98  
% 2.99/0.98  fof(f10,axiom,(
% 2.99/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f24,plain,(
% 2.99/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.99/0.98    inference(ennf_transformation,[],[f10])).
% 2.99/0.98  
% 2.99/0.98  fof(f25,plain,(
% 2.99/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.99/0.98    inference(flattening,[],[f24])).
% 2.99/0.98  
% 2.99/0.98  fof(f42,plain,(
% 2.99/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f25])).
% 2.99/0.98  
% 2.99/0.98  fof(f7,axiom,(
% 2.99/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 2.99/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.99/0.98  
% 2.99/0.98  fof(f19,plain,(
% 2.99/0.98    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.99/0.98    inference(ennf_transformation,[],[f7])).
% 2.99/0.98  
% 2.99/0.98  fof(f20,plain,(
% 2.99/0.98    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.99/0.98    inference(flattening,[],[f19])).
% 2.99/0.98  
% 2.99/0.98  fof(f39,plain,(
% 2.99/0.98    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.99/0.98    inference(cnf_transformation,[],[f20])).
% 2.99/0.98  
% 2.99/0.98  fof(f49,plain,(
% 2.99/0.98    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)),
% 2.99/0.98    inference(cnf_transformation,[],[f31])).
% 2.99/0.98  
% 2.99/0.98  cnf(c_17,negated_conjecture,
% 2.99/0.98      ( v1_relat_1(sK0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_449,negated_conjecture,
% 2.99/0.98      ( v1_relat_1(sK0) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_764,plain,
% 2.99/0.98      ( v1_relat_1(sK0) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2,plain,
% 2.99/0.98      ( ~ v1_relat_1(X0)
% 2.99/0.98      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_461,plain,
% 2.99/0.98      ( ~ v1_relat_1(X0_42)
% 2.99/0.98      | k9_relat_1(X0_42,k1_relat_1(X0_42)) = k2_relat_1(X0_42) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_753,plain,
% 2.99/0.98      ( k9_relat_1(X0_42,k1_relat_1(X0_42)) = k2_relat_1(X0_42)
% 2.99/0.98      | v1_relat_1(X0_42) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1067,plain,
% 2.99/0.98      ( k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(sK0) ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_764,c_753]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_9,plain,
% 2.99/0.98      ( ~ v1_relat_1(X0)
% 2.99/0.98      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 2.99/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_454,plain,
% 2.99/0.98      ( ~ v1_relat_1(X0_42)
% 2.99/0.98      | k5_relat_1(k6_relat_1(X0_41),X0_42) = k7_relat_1(X0_42,X0_41) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_760,plain,
% 2.99/0.98      ( k5_relat_1(k6_relat_1(X0_41),X0_42) = k7_relat_1(X0_42,X0_41)
% 2.99/0.98      | v1_relat_1(X0_42) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_454]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1207,plain,
% 2.99/0.98      ( k5_relat_1(k6_relat_1(X0_41),sK0) = k7_relat_1(sK0,X0_41) ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_764,c_760]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_6,plain,
% 2.99/0.98      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 2.99/0.98      | ~ v1_relat_1(X0)
% 2.99/0.98      | ~ v1_relat_1(X1) ),
% 2.99/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_457,plain,
% 2.99/0.98      ( r1_tarski(k2_relat_1(k5_relat_1(X0_42,X1_42)),k2_relat_1(X1_42))
% 2.99/0.98      | ~ v1_relat_1(X0_42)
% 2.99/0.98      | ~ v1_relat_1(X1_42) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_757,plain,
% 2.99/0.98      ( r1_tarski(k2_relat_1(k5_relat_1(X0_42,X1_42)),k2_relat_1(X1_42)) = iProver_top
% 2.99/0.98      | v1_relat_1(X0_42) != iProver_top
% 2.99/0.98      | v1_relat_1(X1_42) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1664,plain,
% 2.99/0.98      ( r1_tarski(k2_relat_1(k7_relat_1(sK0,X0_41)),k2_relat_1(sK0)) = iProver_top
% 2.99/0.98      | v1_relat_1(k6_relat_1(X0_41)) != iProver_top
% 2.99/0.98      | v1_relat_1(sK0) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_1207,c_757]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3,plain,
% 2.99/0.98      ( ~ v1_relat_1(X0)
% 2.99/0.98      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.99/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_460,plain,
% 2.99/0.98      ( ~ v1_relat_1(X0_42)
% 2.99/0.98      | k2_relat_1(k7_relat_1(X0_42,X0_41)) = k9_relat_1(X0_42,X0_41) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_754,plain,
% 2.99/0.98      ( k2_relat_1(k7_relat_1(X0_42,X0_41)) = k9_relat_1(X0_42,X0_41)
% 2.99/0.98      | v1_relat_1(X0_42) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_460]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1188,plain,
% 2.99/0.98      ( k2_relat_1(k7_relat_1(sK0,X0_41)) = k9_relat_1(sK0,X0_41) ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_764,c_754]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1696,plain,
% 2.99/0.98      ( r1_tarski(k9_relat_1(sK0,X0_41),k2_relat_1(sK0)) = iProver_top
% 2.99/0.98      | v1_relat_1(k6_relat_1(X0_41)) != iProver_top
% 2.99/0.98      | v1_relat_1(sK0) != iProver_top ),
% 2.99/0.98      inference(light_normalisation,[status(thm)],[c_1664,c_1188]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_18,plain,
% 2.99/0.98      ( v1_relat_1(sK0) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1,plain,
% 2.99/0.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.99/0.98      inference(cnf_transformation,[],[f33]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_462,plain,
% 2.99/0.98      ( v1_relat_1(k6_relat_1(X0_41)) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_489,plain,
% 2.99/0.98      ( v1_relat_1(k6_relat_1(X0_41)) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2875,plain,
% 2.99/0.98      ( r1_tarski(k9_relat_1(sK0,X0_41),k2_relat_1(sK0)) = iProver_top ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_1696,c_18,c_489]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2882,plain,
% 2.99/0.98      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_1067,c_2875]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_13,plain,
% 2.99/0.98      ( ~ v2_funct_1(X0)
% 2.99/0.98      | ~ v1_funct_1(X0)
% 2.99/0.98      | ~ v1_relat_1(X0)
% 2.99/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_15,negated_conjecture,
% 2.99/0.98      ( v2_funct_1(sK0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_200,plain,
% 2.99/0.98      ( ~ v1_funct_1(X0)
% 2.99/0.98      | ~ v1_relat_1(X0)
% 2.99/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.99/0.98      | sK0 != X0 ),
% 2.99/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_15]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_201,plain,
% 2.99/0.98      ( ~ v1_funct_1(sK0)
% 2.99/0.98      | ~ v1_relat_1(sK0)
% 2.99/0.98      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.99/0.98      inference(unflattening,[status(thm)],[c_200]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_16,negated_conjecture,
% 2.99/0.98      ( v1_funct_1(sK0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_22,plain,
% 2.99/0.98      ( ~ v2_funct_1(sK0)
% 2.99/0.98      | ~ v1_funct_1(sK0)
% 2.99/0.98      | ~ v1_relat_1(sK0)
% 2.99/0.98      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_203,plain,
% 2.99/0.98      ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_201,c_17,c_16,c_15,c_22]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_448,plain,
% 2.99/0.98      ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_203]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_8,plain,
% 2.99/0.98      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 2.99/0.98      | ~ v1_relat_1(X0)
% 2.99/0.98      | ~ v1_relat_1(X1)
% 2.99/0.98      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_455,plain,
% 2.99/0.98      ( ~ r1_tarski(k1_relat_1(X0_42),k2_relat_1(X1_42))
% 2.99/0.98      | ~ v1_relat_1(X0_42)
% 2.99/0.98      | ~ v1_relat_1(X1_42)
% 2.99/0.98      | k2_relat_1(k5_relat_1(X1_42,X0_42)) = k2_relat_1(X0_42) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_759,plain,
% 2.99/0.98      ( k2_relat_1(k5_relat_1(X0_42,X1_42)) = k2_relat_1(X1_42)
% 2.99/0.98      | r1_tarski(k1_relat_1(X1_42),k2_relat_1(X0_42)) != iProver_top
% 2.99/0.98      | v1_relat_1(X1_42) != iProver_top
% 2.99/0.98      | v1_relat_1(X0_42) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2129,plain,
% 2.99/0.98      ( k2_relat_1(k5_relat_1(X0_42,k2_funct_1(sK0))) = k2_relat_1(k2_funct_1(sK0))
% 2.99/0.98      | r1_tarski(k2_relat_1(sK0),k2_relat_1(X0_42)) != iProver_top
% 2.99/0.98      | v1_relat_1(X0_42) != iProver_top
% 2.99/0.98      | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_448,c_759]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_12,plain,
% 2.99/0.98      ( ~ v2_funct_1(X0)
% 2.99/0.98      | ~ v1_funct_1(X0)
% 2.99/0.98      | ~ v1_relat_1(X0)
% 2.99/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_208,plain,
% 2.99/0.98      ( ~ v1_funct_1(X0)
% 2.99/0.98      | ~ v1_relat_1(X0)
% 2.99/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.99/0.98      | sK0 != X0 ),
% 2.99/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_209,plain,
% 2.99/0.98      ( ~ v1_funct_1(sK0)
% 2.99/0.98      | ~ v1_relat_1(sK0)
% 2.99/0.98      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 2.99/0.98      inference(unflattening,[status(thm)],[c_208]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_25,plain,
% 2.99/0.98      ( ~ v2_funct_1(sK0)
% 2.99/0.98      | ~ v1_funct_1(sK0)
% 2.99/0.98      | ~ v1_relat_1(sK0)
% 2.99/0.98      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_211,plain,
% 2.99/0.98      ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_209,c_17,c_16,c_15,c_25]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_447,plain,
% 2.99/0.98      ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_211]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2190,plain,
% 2.99/0.98      ( k2_relat_1(k5_relat_1(X0_42,k2_funct_1(sK0))) = k1_relat_1(sK0)
% 2.99/0.98      | r1_tarski(k2_relat_1(sK0),k2_relat_1(X0_42)) != iProver_top
% 2.99/0.98      | v1_relat_1(X0_42) != iProver_top
% 2.99/0.98      | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
% 2.99/0.98      inference(light_normalisation,[status(thm)],[c_2129,c_447]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_19,plain,
% 2.99/0.98      ( v1_funct_1(sK0) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_11,plain,
% 2.99/0.98      ( ~ v1_funct_1(X0)
% 2.99/0.98      | ~ v1_relat_1(X0)
% 2.99/0.98      | v1_relat_1(k2_funct_1(X0)) ),
% 2.99/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_27,plain,
% 2.99/0.98      ( v1_funct_1(X0) != iProver_top
% 2.99/0.98      | v1_relat_1(X0) != iProver_top
% 2.99/0.98      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_29,plain,
% 2.99/0.98      ( v1_funct_1(sK0) != iProver_top
% 2.99/0.98      | v1_relat_1(k2_funct_1(sK0)) = iProver_top
% 2.99/0.98      | v1_relat_1(sK0) != iProver_top ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_27]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2826,plain,
% 2.99/0.98      ( v1_relat_1(X0_42) != iProver_top
% 2.99/0.98      | r1_tarski(k2_relat_1(sK0),k2_relat_1(X0_42)) != iProver_top
% 2.99/0.98      | k2_relat_1(k5_relat_1(X0_42,k2_funct_1(sK0))) = k1_relat_1(sK0) ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_2190,c_18,c_19,c_29]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2827,plain,
% 2.99/0.98      ( k2_relat_1(k5_relat_1(X0_42,k2_funct_1(sK0))) = k1_relat_1(sK0)
% 2.99/0.98      | r1_tarski(k2_relat_1(sK0),k2_relat_1(X0_42)) != iProver_top
% 2.99/0.98      | v1_relat_1(X0_42) != iProver_top ),
% 2.99/0.98      inference(renaming,[status(thm)],[c_2826]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3486,plain,
% 2.99/0.98      ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(sK0)
% 2.99/0.98      | v1_relat_1(sK0) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_2882,c_2827]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2829,plain,
% 2.99/0.98      ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(sK0)
% 2.99/0.98      | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top
% 2.99/0.98      | v1_relat_1(sK0) != iProver_top ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_2827]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3818,plain,
% 2.99/0.98      ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(sK0) ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_3486,c_18,c_2829,c_2882]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1665,plain,
% 2.99/0.98      ( r1_tarski(k2_relat_1(k5_relat_1(X0_42,k2_funct_1(sK0))),k1_relat_1(sK0)) = iProver_top
% 2.99/0.98      | v1_relat_1(X0_42) != iProver_top
% 2.99/0.98      | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_447,c_757]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2330,plain,
% 2.99/0.98      ( v1_relat_1(X0_42) != iProver_top
% 2.99/0.98      | r1_tarski(k2_relat_1(k5_relat_1(X0_42,k2_funct_1(sK0))),k1_relat_1(sK0)) = iProver_top ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_1665,c_18,c_19,c_29]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2331,plain,
% 2.99/0.98      ( r1_tarski(k2_relat_1(k5_relat_1(X0_42,k2_funct_1(sK0))),k1_relat_1(sK0)) = iProver_top
% 2.99/0.98      | v1_relat_1(X0_42) != iProver_top ),
% 2.99/0.98      inference(renaming,[status(thm)],[c_2330]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_3827,plain,
% 2.99/0.98      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) = iProver_top
% 2.99/0.98      | v1_relat_1(sK0) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_3818,c_2331]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2132,plain,
% 2.99/0.98      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0_42)) = k2_relat_1(X0_42)
% 2.99/0.98      | r1_tarski(k1_relat_1(X0_42),k1_relat_1(sK0)) != iProver_top
% 2.99/0.98      | v1_relat_1(X0_42) != iProver_top
% 2.99/0.98      | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_447,c_759]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2658,plain,
% 2.99/0.98      ( v1_relat_1(X0_42) != iProver_top
% 2.99/0.98      | r1_tarski(k1_relat_1(X0_42),k1_relat_1(sK0)) != iProver_top
% 2.99/0.98      | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0_42)) = k2_relat_1(X0_42) ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_2132,c_18,c_19,c_29]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2659,plain,
% 2.99/0.98      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0_42)) = k2_relat_1(X0_42)
% 2.99/0.98      | r1_tarski(k1_relat_1(X0_42),k1_relat_1(sK0)) != iProver_top
% 2.99/0.98      | v1_relat_1(X0_42) != iProver_top ),
% 2.99/0.98      inference(renaming,[status(thm)],[c_2658]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2661,plain,
% 2.99/0.98      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0)
% 2.99/0.98      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top
% 2.99/0.98      | v1_relat_1(sK0) != iProver_top ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_2659]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_7,plain,
% 2.99/0.98      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 2.99/0.98      | ~ v1_relat_1(X0)
% 2.99/0.98      | ~ v1_relat_1(X1)
% 2.99/0.98      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_456,plain,
% 2.99/0.98      ( ~ r1_tarski(k2_relat_1(X0_42),k1_relat_1(X1_42))
% 2.99/0.98      | ~ v1_relat_1(X0_42)
% 2.99/0.98      | ~ v1_relat_1(X1_42)
% 2.99/0.98      | k1_relat_1(k5_relat_1(X0_42,X1_42)) = k1_relat_1(X0_42) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_758,plain,
% 2.99/0.98      ( k1_relat_1(k5_relat_1(X0_42,X1_42)) = k1_relat_1(X0_42)
% 2.99/0.98      | r1_tarski(k2_relat_1(X0_42),k1_relat_1(X1_42)) != iProver_top
% 2.99/0.98      | v1_relat_1(X0_42) != iProver_top
% 2.99/0.98      | v1_relat_1(X1_42) != iProver_top ),
% 2.99/0.98      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1893,plain,
% 2.99/0.98      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0_42)) = k1_relat_1(k2_funct_1(sK0))
% 2.99/0.98      | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0_42)) != iProver_top
% 2.99/0.98      | v1_relat_1(X0_42) != iProver_top
% 2.99/0.98      | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
% 2.99/0.98      inference(superposition,[status(thm)],[c_447,c_758]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_1954,plain,
% 2.99/0.98      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0_42)) = k2_relat_1(sK0)
% 2.99/0.98      | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0_42)) != iProver_top
% 2.99/0.98      | v1_relat_1(X0_42) != iProver_top
% 2.99/0.98      | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
% 2.99/0.98      inference(light_normalisation,[status(thm)],[c_1893,c_448]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2543,plain,
% 2.99/0.98      ( v1_relat_1(X0_42) != iProver_top
% 2.99/0.98      | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0_42)) != iProver_top
% 2.99/0.98      | k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0_42)) = k2_relat_1(sK0) ),
% 2.99/0.98      inference(global_propositional_subsumption,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_1954,c_18,c_19,c_29]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2544,plain,
% 2.99/0.98      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0_42)) = k2_relat_1(sK0)
% 2.99/0.98      | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0_42)) != iProver_top
% 2.99/0.98      | v1_relat_1(X0_42) != iProver_top ),
% 2.99/0.98      inference(renaming,[status(thm)],[c_2543]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_2546,plain,
% 2.99/0.98      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0)
% 2.99/0.98      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top
% 2.99/0.98      | v1_relat_1(sK0) != iProver_top ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_2544]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_467,plain,
% 2.99/0.98      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 2.99/0.98      theory(equality) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_876,plain,
% 2.99/0.98      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != X0_41
% 2.99/0.98      | k2_relat_1(sK0) != X0_41
% 2.99/0.98      | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_467]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_888,plain,
% 2.99/0.98      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)
% 2.99/0.98      | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
% 2.99/0.98      | k2_relat_1(sK0) != k2_relat_1(sK0) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_876]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_14,negated_conjecture,
% 2.99/0.98      ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
% 2.99/0.98      | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0) ),
% 2.99/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_451,negated_conjecture,
% 2.99/0.98      ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
% 2.99/0.98      | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0) ),
% 2.99/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_466,plain,( X0_42 = X0_42 ),theory(equality) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_487,plain,
% 2.99/0.98      ( sK0 = sK0 ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_466]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_472,plain,
% 2.99/0.98      ( X0_42 != X1_42 | k2_relat_1(X0_42) = k2_relat_1(X1_42) ),
% 2.99/0.98      theory(equality) ).
% 2.99/0.98  
% 2.99/0.98  cnf(c_480,plain,
% 2.99/0.98      ( sK0 != sK0 | k2_relat_1(sK0) = k2_relat_1(sK0) ),
% 2.99/0.98      inference(instantiation,[status(thm)],[c_472]) ).
% 2.99/0.98  
% 2.99/0.98  cnf(contradiction,plain,
% 2.99/0.98      ( $false ),
% 2.99/0.98      inference(minisat,
% 2.99/0.98                [status(thm)],
% 2.99/0.98                [c_3827,c_2661,c_2546,c_888,c_451,c_487,c_480,c_18]) ).
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.99/0.98  
% 2.99/0.98  ------                               Statistics
% 2.99/0.98  
% 2.99/0.98  ------ General
% 2.99/0.98  
% 2.99/0.98  abstr_ref_over_cycles:                  0
% 2.99/0.98  abstr_ref_under_cycles:                 0
% 2.99/0.98  gc_basic_clause_elim:                   0
% 2.99/0.98  forced_gc_time:                         0
% 2.99/0.98  parsing_time:                           0.01
% 2.99/0.98  unif_index_cands_time:                  0.
% 2.99/0.98  unif_index_add_time:                    0.
% 2.99/0.98  orderings_time:                         0.
% 2.99/0.98  out_proof_time:                         0.011
% 2.99/0.98  total_time:                             0.153
% 2.99/0.98  num_of_symbols:                         46
% 2.99/0.98  num_of_terms:                           3395
% 2.99/0.98  
% 2.99/0.98  ------ Preprocessing
% 2.99/0.98  
% 2.99/0.98  num_of_splits:                          0
% 2.99/0.98  num_of_split_atoms:                     0
% 2.99/0.98  num_of_reused_defs:                     0
% 2.99/0.98  num_eq_ax_congr_red:                    15
% 2.99/0.98  num_of_sem_filtered_clauses:            1
% 2.99/0.98  num_of_subtypes:                        2
% 2.99/0.98  monotx_restored_types:                  0
% 2.99/0.98  sat_num_of_epr_types:                   0
% 2.99/0.98  sat_num_of_non_cyclic_types:            0
% 2.99/0.98  sat_guarded_non_collapsed_types:        0
% 2.99/0.98  num_pure_diseq_elim:                    0
% 2.99/0.98  simp_replaced_by:                       0
% 2.99/0.98  res_preprocessed:                       94
% 2.99/0.98  prep_upred:                             0
% 2.99/0.98  prep_unflattend:                        2
% 2.99/0.98  smt_new_axioms:                         0
% 2.99/0.98  pred_elim_cands:                        3
% 2.99/0.98  pred_elim:                              1
% 2.99/0.98  pred_elim_cl:                           1
% 2.99/0.98  pred_elim_cycles:                       3
% 2.99/0.98  merged_defs:                            0
% 2.99/0.98  merged_defs_ncl:                        0
% 2.99/0.98  bin_hyper_res:                          0
% 2.99/0.98  prep_cycles:                            4
% 2.99/0.98  pred_elim_time:                         0.002
% 2.99/0.98  splitting_time:                         0.
% 2.99/0.98  sem_filter_time:                        0.
% 2.99/0.98  monotx_time:                            0.
% 2.99/0.98  subtype_inf_time:                       0.
% 2.99/0.98  
% 2.99/0.98  ------ Problem properties
% 2.99/0.98  
% 2.99/0.98  clauses:                                17
% 2.99/0.98  conjectures:                            3
% 2.99/0.98  epr:                                    2
% 2.99/0.98  horn:                                   17
% 2.99/0.98  ground:                                 5
% 2.99/0.98  unary:                                  5
% 2.99/0.98  binary:                                 7
% 2.99/0.98  lits:                                   36
% 2.99/0.98  lits_eq:                                11
% 2.99/0.98  fd_pure:                                0
% 2.99/0.98  fd_pseudo:                              0
% 2.99/0.98  fd_cond:                                0
% 2.99/0.98  fd_pseudo_cond:                         0
% 2.99/0.98  ac_symbols:                             0
% 2.99/0.98  
% 2.99/0.98  ------ Propositional Solver
% 2.99/0.98  
% 2.99/0.98  prop_solver_calls:                      27
% 2.99/0.98  prop_fast_solver_calls:                 565
% 2.99/0.98  smt_solver_calls:                       0
% 2.99/0.98  smt_fast_solver_calls:                  0
% 2.99/0.98  prop_num_of_clauses:                    1174
% 2.99/0.98  prop_preprocess_simplified:             4082
% 2.99/0.98  prop_fo_subsumed:                       14
% 2.99/0.98  prop_solver_time:                       0.
% 2.99/0.98  smt_solver_time:                        0.
% 2.99/0.98  smt_fast_solver_time:                   0.
% 2.99/0.98  prop_fast_solver_time:                  0.
% 2.99/0.98  prop_unsat_core_time:                   0.
% 2.99/0.98  
% 2.99/0.98  ------ QBF
% 2.99/0.98  
% 2.99/0.98  qbf_q_res:                              0
% 2.99/0.98  qbf_num_tautologies:                    0
% 2.99/0.98  qbf_prep_cycles:                        0
% 2.99/0.98  
% 2.99/0.98  ------ BMC1
% 2.99/0.98  
% 2.99/0.98  bmc1_current_bound:                     -1
% 2.99/0.98  bmc1_last_solved_bound:                 -1
% 2.99/0.98  bmc1_unsat_core_size:                   -1
% 2.99/0.98  bmc1_unsat_core_parents_size:           -1
% 2.99/0.98  bmc1_merge_next_fun:                    0
% 2.99/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.99/0.98  
% 2.99/0.98  ------ Instantiation
% 2.99/0.98  
% 2.99/0.98  inst_num_of_clauses:                    481
% 2.99/0.98  inst_num_in_passive:                    42
% 2.99/0.98  inst_num_in_active:                     225
% 2.99/0.98  inst_num_in_unprocessed:                214
% 2.99/0.98  inst_num_of_loops:                      230
% 2.99/0.98  inst_num_of_learning_restarts:          0
% 2.99/0.98  inst_num_moves_active_passive:          1
% 2.99/0.98  inst_lit_activity:                      0
% 2.99/0.98  inst_lit_activity_moves:                0
% 2.99/0.98  inst_num_tautologies:                   0
% 2.99/0.98  inst_num_prop_implied:                  0
% 2.99/0.98  inst_num_existing_simplified:           0
% 2.99/0.98  inst_num_eq_res_simplified:             0
% 2.99/0.98  inst_num_child_elim:                    0
% 2.99/0.98  inst_num_of_dismatching_blockings:      369
% 2.99/0.98  inst_num_of_non_proper_insts:           604
% 2.99/0.98  inst_num_of_duplicates:                 0
% 2.99/0.98  inst_inst_num_from_inst_to_res:         0
% 2.99/0.98  inst_dismatching_checking_time:         0.
% 2.99/0.98  
% 2.99/0.98  ------ Resolution
% 2.99/0.98  
% 2.99/0.98  res_num_of_clauses:                     0
% 2.99/0.98  res_num_in_passive:                     0
% 2.99/0.98  res_num_in_active:                      0
% 2.99/0.98  res_num_of_loops:                       98
% 2.99/0.98  res_forward_subset_subsumed:            96
% 2.99/0.98  res_backward_subset_subsumed:           2
% 2.99/0.98  res_forward_subsumed:                   0
% 2.99/0.98  res_backward_subsumed:                  0
% 2.99/0.98  res_forward_subsumption_resolution:     0
% 2.99/0.98  res_backward_subsumption_resolution:    0
% 2.99/0.98  res_clause_to_clause_subsumption:       202
% 2.99/0.98  res_orphan_elimination:                 0
% 2.99/0.98  res_tautology_del:                      126
% 2.99/0.98  res_num_eq_res_simplified:              0
% 2.99/0.98  res_num_sel_changes:                    0
% 2.99/0.98  res_moves_from_active_to_pass:          0
% 2.99/0.98  
% 2.99/0.98  ------ Superposition
% 2.99/0.98  
% 2.99/0.98  sup_time_total:                         0.
% 2.99/0.98  sup_time_generating:                    0.
% 2.99/0.98  sup_time_sim_full:                      0.
% 2.99/0.98  sup_time_sim_immed:                     0.
% 2.99/0.98  
% 2.99/0.98  sup_num_of_clauses:                     115
% 2.99/0.98  sup_num_in_active:                      45
% 2.99/0.98  sup_num_in_passive:                     70
% 2.99/0.98  sup_num_of_loops:                       44
% 2.99/0.98  sup_fw_superposition:                   68
% 2.99/0.98  sup_bw_superposition:                   33
% 2.99/0.98  sup_immediate_simplified:               23
% 2.99/0.98  sup_given_eliminated:                   0
% 2.99/0.98  comparisons_done:                       0
% 2.99/0.98  comparisons_avoided:                    0
% 2.99/0.98  
% 2.99/0.98  ------ Simplifications
% 2.99/0.98  
% 2.99/0.98  
% 2.99/0.98  sim_fw_subset_subsumed:                 0
% 2.99/0.98  sim_bw_subset_subsumed:                 0
% 2.99/0.98  sim_fw_subsumed:                        0
% 2.99/0.98  sim_bw_subsumed:                        0
% 2.99/0.98  sim_fw_subsumption_res:                 0
% 2.99/0.98  sim_bw_subsumption_res:                 0
% 2.99/0.98  sim_tautology_del:                      0
% 2.99/0.98  sim_eq_tautology_del:                   0
% 2.99/0.98  sim_eq_res_simp:                        0
% 2.99/0.98  sim_fw_demodulated:                     0
% 2.99/0.98  sim_bw_demodulated:                     0
% 2.99/0.98  sim_light_normalised:                   23
% 2.99/0.98  sim_joinable_taut:                      0
% 2.99/0.98  sim_joinable_simp:                      0
% 2.99/0.98  sim_ac_normalised:                      0
% 2.99/0.98  sim_smt_subsumption:                    0
% 2.99/0.98  
%------------------------------------------------------------------------------
