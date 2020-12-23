%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0658+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:49 EST 2020

% Result     : Theorem 0.98s
% Output     : CNFRefutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 218 expanded)
%              Number of clauses        :   44 (  66 expanded)
%              Number of leaves         :    6 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  289 ( 869 expanded)
%              Number of equality atoms :  134 ( 274 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,
    ( ? [X0] :
        ( k2_funct_1(k2_funct_1(X0)) != X0
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( k2_funct_1(k2_funct_1(sK0)) != sK0
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( k2_funct_1(k2_funct_1(sK0)) != sK0
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f34,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    k2_funct_1(k2_funct_1(sK0)) != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f26,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_11,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_228,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_476,plain,
    ( v2_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_228])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_232,plain,
    ( ~ v2_funct_1(X0_37)
    | ~ v1_relat_1(X0_37)
    | ~ v1_funct_1(X0_37)
    | k5_relat_1(k2_funct_1(X0_37),X0_37) = k6_relat_1(k2_relat_1(X0_37)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_473,plain,
    ( k5_relat_1(k2_funct_1(X0_37),X0_37) = k6_relat_1(k2_relat_1(X0_37))
    | v2_funct_1(X0_37) != iProver_top
    | v1_relat_1(X0_37) != iProver_top
    | v1_funct_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_232])).

cnf(c_767,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_476,c_473])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_275,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_1046,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_767,c_13,c_12,c_11,c_275])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
    | k1_relat_1(X1) != k2_relat_1(X0)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_230,plain,
    ( ~ v2_funct_1(X0_37)
    | ~ v1_relat_1(X0_37)
    | ~ v1_relat_1(X1_37)
    | ~ v1_funct_1(X0_37)
    | ~ v1_funct_1(X1_37)
    | k1_relat_1(X1_37) != k2_relat_1(X0_37)
    | k5_relat_1(X0_37,X1_37) != k6_relat_1(k1_relat_1(X0_37))
    | k2_funct_1(X0_37) = X1_37 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_475,plain,
    ( k1_relat_1(X0_37) != k2_relat_1(X1_37)
    | k5_relat_1(X1_37,X0_37) != k6_relat_1(k1_relat_1(X1_37))
    | k2_funct_1(X1_37) = X0_37
    | v2_funct_1(X1_37) != iProver_top
    | v1_relat_1(X1_37) != iProver_top
    | v1_relat_1(X0_37) != iProver_top
    | v1_funct_1(X1_37) != iProver_top
    | v1_funct_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_230])).

cnf(c_1049,plain,
    ( k2_relat_1(k2_funct_1(sK0)) != k1_relat_1(sK0)
    | k6_relat_1(k1_relat_1(k2_funct_1(sK0))) != k6_relat_1(k2_relat_1(sK0))
    | k2_funct_1(k2_funct_1(sK0)) = sK0
    | v2_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1046,c_475])).

cnf(c_5,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_234,plain,
    ( ~ v2_funct_1(X0_37)
    | ~ v1_relat_1(X0_37)
    | ~ v1_funct_1(X0_37)
    | k2_relat_1(k2_funct_1(X0_37)) = k1_relat_1(X0_37) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_471,plain,
    ( k2_relat_1(k2_funct_1(X0_37)) = k1_relat_1(X0_37)
    | v2_funct_1(X0_37) != iProver_top
    | v1_relat_1(X0_37) != iProver_top
    | v1_funct_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_234])).

cnf(c_663,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_476,c_471])).

cnf(c_269,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_981,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_663,c_13,c_12,c_11,c_269])).

cnf(c_6,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_233,plain,
    ( ~ v2_funct_1(X0_37)
    | ~ v1_relat_1(X0_37)
    | ~ v1_funct_1(X0_37)
    | k1_relat_1(k2_funct_1(X0_37)) = k2_relat_1(X0_37) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_472,plain,
    ( k1_relat_1(k2_funct_1(X0_37)) = k2_relat_1(X0_37)
    | v2_funct_1(X0_37) != iProver_top
    | v1_relat_1(X0_37) != iProver_top
    | v1_funct_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_233])).

cnf(c_738,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0)
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_476,c_472])).

cnf(c_272,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_233])).

cnf(c_985,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_738,c_13,c_12,c_11,c_272])).

cnf(c_1050,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0))
    | k2_funct_1(k2_funct_1(sK0)) = sK0
    | v2_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1049,c_981,c_985])).

cnf(c_1051,plain,
    ( k2_funct_1(k2_funct_1(sK0)) = sK0
    | v2_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1050])).

cnf(c_10,negated_conjecture,
    ( k2_funct_1(k2_funct_1(sK0)) != sK0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_229,negated_conjecture,
    ( k2_funct_1(k2_funct_1(sK0)) != sK0 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_38,plain,
    ( v2_funct_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_40,plain,
    ( v2_funct_1(k2_funct_1(sK0)) = iProver_top
    | v2_funct_1(sK0) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_3,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_35,plain,
    ( v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_37,plain,
    ( v2_funct_1(sK0) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) = iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_4,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_32,plain,
    ( v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_34,plain,
    ( v2_funct_1(sK0) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_16,plain,
    ( v2_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_15,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1051,c_229,c_40,c_37,c_34,c_16,c_15,c_14])).


%------------------------------------------------------------------------------
