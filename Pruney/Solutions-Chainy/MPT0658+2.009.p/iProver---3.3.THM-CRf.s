%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:55 EST 2020

% Result     : Theorem 0.83s
% Output     : CNFRefutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 312 expanded)
%              Number of clauses        :   52 (  95 expanded)
%              Number of leaves         :    7 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  341 (1219 expanded)
%              Number of equality atoms :  162 ( 395 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    8 (   4 average)
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

fof(f32,plain,(
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

fof(f27,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
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
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
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
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    k2_funct_1(k2_funct_1(sK0)) != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_9,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_354,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_602,plain,
    ( v2_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_6,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_357,plain,
    ( ~ v2_funct_1(X0_37)
    | ~ v1_relat_1(X0_37)
    | ~ v1_funct_1(X0_37)
    | k5_relat_1(X0_37,k2_funct_1(X0_37)) = k6_relat_1(k1_relat_1(X0_37)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_600,plain,
    ( k5_relat_1(X0_37,k2_funct_1(X0_37)) = k6_relat_1(k1_relat_1(X0_37))
    | v2_funct_1(X0_37) != iProver_top
    | v1_relat_1(X0_37) != iProver_top
    | v1_funct_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_948,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_602,c_600])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_10,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_404,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_1137,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_948,c_11,c_10,c_9,c_404])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
    | k2_relat_1(X1) != k1_relat_1(X0)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_356,plain,
    ( ~ v2_funct_1(X0_37)
    | ~ v1_relat_1(X0_37)
    | ~ v1_relat_1(X1_37)
    | ~ v1_funct_1(X0_37)
    | ~ v1_funct_1(X1_37)
    | k2_relat_1(X1_37) != k1_relat_1(X0_37)
    | k5_relat_1(X1_37,X0_37) != k6_relat_1(k2_relat_1(X0_37))
    | k2_funct_1(X0_37) = X1_37 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_601,plain,
    ( k2_relat_1(X0_37) != k1_relat_1(X1_37)
    | k5_relat_1(X0_37,X1_37) != k6_relat_1(k2_relat_1(X1_37))
    | k2_funct_1(X1_37) = X0_37
    | v2_funct_1(X1_37) != iProver_top
    | v1_relat_1(X0_37) != iProver_top
    | v1_relat_1(X1_37) != iProver_top
    | v1_funct_1(X0_37) != iProver_top
    | v1_funct_1(X1_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_356])).

cnf(c_1140,plain,
    ( k1_relat_1(k2_funct_1(sK0)) != k2_relat_1(sK0)
    | k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k6_relat_1(k1_relat_1(sK0))
    | k2_funct_1(k2_funct_1(sK0)) = sK0
    | v2_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1137,c_601])).

cnf(c_3,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_360,plain,
    ( ~ v2_funct_1(X0_37)
    | ~ v1_relat_1(X0_37)
    | ~ v1_funct_1(X0_37)
    | k2_relat_1(k2_funct_1(X0_37)) = k1_relat_1(X0_37) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_597,plain,
    ( k2_relat_1(k2_funct_1(X0_37)) = k1_relat_1(X0_37)
    | v2_funct_1(X0_37) != iProver_top
    | v1_relat_1(X0_37) != iProver_top
    | v1_funct_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_788,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_602,c_597])).

cnf(c_395,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_791,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_788,c_11,c_10,c_9,c_395])).

cnf(c_4,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_359,plain,
    ( ~ v2_funct_1(X0_37)
    | ~ v1_relat_1(X0_37)
    | ~ v1_funct_1(X0_37)
    | k1_relat_1(k2_funct_1(X0_37)) = k2_relat_1(X0_37) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_598,plain,
    ( k1_relat_1(k2_funct_1(X0_37)) = k2_relat_1(X0_37)
    | v2_funct_1(X0_37) != iProver_top
    | v1_relat_1(X0_37) != iProver_top
    | v1_funct_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_852,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0)
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_602,c_598])).

cnf(c_398,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_1032,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_852,c_11,c_10,c_9,c_398])).

cnf(c_1150,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
    | k2_funct_1(k2_funct_1(sK0)) = sK0
    | v2_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1140,c_791,c_1032])).

cnf(c_1151,plain,
    ( k2_funct_1(k2_funct_1(sK0)) = sK0
    | v2_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1150])).

cnf(c_5,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_358,plain,
    ( ~ v2_funct_1(X0_37)
    | ~ v1_relat_1(X0_37)
    | ~ v1_funct_1(X0_37)
    | k5_relat_1(k2_funct_1(X0_37),X0_37) = k6_relat_1(k2_relat_1(X0_37)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_599,plain,
    ( k5_relat_1(k2_funct_1(X0_37),X0_37) = k6_relat_1(k2_relat_1(X0_37))
    | v2_funct_1(X0_37) != iProver_top
    | v1_relat_1(X0_37) != iProver_top
    | v1_funct_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_941,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_602,c_599])).

cnf(c_401,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_1117,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_941,c_11,c_10,c_9,c_401])).

cnf(c_2,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_361,plain,
    ( v2_funct_1(X0_37)
    | ~ v1_relat_1(X0_37)
    | ~ v1_relat_1(X1_37)
    | ~ v1_funct_1(X0_37)
    | ~ v1_funct_1(X1_37)
    | k5_relat_1(X0_37,X1_37) != k6_relat_1(k1_relat_1(X0_37)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_596,plain,
    ( k5_relat_1(X0_37,X1_37) != k6_relat_1(k1_relat_1(X0_37))
    | v2_funct_1(X0_37) = iProver_top
    | v1_relat_1(X1_37) != iProver_top
    | v1_relat_1(X0_37) != iProver_top
    | v1_funct_1(X1_37) != iProver_top
    | v1_funct_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_1121,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1(sK0))) != k6_relat_1(k2_relat_1(sK0))
    | v2_funct_1(k2_funct_1(sK0)) = iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_596])).

cnf(c_1128,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0))
    | v2_funct_1(k2_funct_1(sK0)) = iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1121,c_1032])).

cnf(c_1129,plain,
    ( v2_funct_1(k2_funct_1(sK0)) = iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1128])).

cnf(c_8,negated_conjecture,
    ( k2_funct_1(k2_funct_1(sK0)) != sK0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_355,negated_conjecture,
    ( k2_funct_1(k2_funct_1(sK0)) != sK0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_34,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_36,plain,
    ( v1_relat_1(sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK0)) = iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_31,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_33,plain,
    ( v1_relat_1(k2_funct_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_funct_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_13,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1151,c_1129,c_355,c_36,c_33,c_13,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:49:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.83/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.83/0.98  
% 0.83/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.83/0.98  
% 0.83/0.98  ------  iProver source info
% 0.83/0.98  
% 0.83/0.98  git: date: 2020-06-30 10:37:57 +0100
% 0.83/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.83/0.98  git: non_committed_changes: false
% 0.83/0.98  git: last_make_outside_of_git: false
% 0.83/0.98  
% 0.83/0.98  ------ 
% 0.83/0.98  
% 0.83/0.98  ------ Input Options
% 0.83/0.98  
% 0.83/0.98  --out_options                           all
% 0.83/0.98  --tptp_safe_out                         true
% 0.83/0.98  --problem_path                          ""
% 0.83/0.98  --include_path                          ""
% 0.83/0.98  --clausifier                            res/vclausify_rel
% 0.83/0.98  --clausifier_options                    --mode clausify
% 0.83/0.98  --stdin                                 false
% 0.83/0.98  --stats_out                             all
% 0.83/0.98  
% 0.83/0.98  ------ General Options
% 0.83/0.98  
% 0.83/0.98  --fof                                   false
% 0.83/0.98  --time_out_real                         305.
% 0.83/0.98  --time_out_virtual                      -1.
% 0.83/0.98  --symbol_type_check                     false
% 0.83/0.98  --clausify_out                          false
% 0.83/0.98  --sig_cnt_out                           false
% 0.83/0.98  --trig_cnt_out                          false
% 0.83/0.98  --trig_cnt_out_tolerance                1.
% 0.83/0.98  --trig_cnt_out_sk_spl                   false
% 0.83/0.98  --abstr_cl_out                          false
% 0.83/0.98  
% 0.83/0.98  ------ Global Options
% 0.83/0.98  
% 0.83/0.98  --schedule                              default
% 0.83/0.98  --add_important_lit                     false
% 0.83/0.98  --prop_solver_per_cl                    1000
% 0.83/0.98  --min_unsat_core                        false
% 0.83/0.98  --soft_assumptions                      false
% 0.83/0.98  --soft_lemma_size                       3
% 0.83/0.98  --prop_impl_unit_size                   0
% 0.83/0.98  --prop_impl_unit                        []
% 0.83/0.98  --share_sel_clauses                     true
% 0.83/0.98  --reset_solvers                         false
% 0.83/0.98  --bc_imp_inh                            [conj_cone]
% 0.83/0.98  --conj_cone_tolerance                   3.
% 0.83/0.98  --extra_neg_conj                        none
% 0.83/0.98  --large_theory_mode                     true
% 0.83/0.98  --prolific_symb_bound                   200
% 0.83/0.98  --lt_threshold                          2000
% 0.83/0.98  --clause_weak_htbl                      true
% 0.83/0.98  --gc_record_bc_elim                     false
% 0.83/0.98  
% 0.83/0.98  ------ Preprocessing Options
% 0.83/0.98  
% 0.83/0.98  --preprocessing_flag                    true
% 0.83/0.98  --time_out_prep_mult                    0.1
% 0.83/0.98  --splitting_mode                        input
% 0.83/0.98  --splitting_grd                         true
% 0.83/0.98  --splitting_cvd                         false
% 0.83/0.98  --splitting_cvd_svl                     false
% 0.83/0.98  --splitting_nvd                         32
% 0.83/0.98  --sub_typing                            true
% 0.83/0.98  --prep_gs_sim                           true
% 0.83/0.98  --prep_unflatten                        true
% 0.83/0.98  --prep_res_sim                          true
% 0.83/0.98  --prep_upred                            true
% 0.83/0.98  --prep_sem_filter                       exhaustive
% 0.83/0.98  --prep_sem_filter_out                   false
% 0.83/0.98  --pred_elim                             true
% 0.83/0.98  --res_sim_input                         true
% 0.83/0.98  --eq_ax_congr_red                       true
% 0.83/0.98  --pure_diseq_elim                       true
% 0.83/0.98  --brand_transform                       false
% 0.83/0.98  --non_eq_to_eq                          false
% 0.83/0.98  --prep_def_merge                        true
% 0.83/0.98  --prep_def_merge_prop_impl              false
% 0.83/0.98  --prep_def_merge_mbd                    true
% 0.83/0.98  --prep_def_merge_tr_red                 false
% 0.83/0.98  --prep_def_merge_tr_cl                  false
% 0.83/0.98  --smt_preprocessing                     true
% 0.83/0.98  --smt_ac_axioms                         fast
% 0.83/0.98  --preprocessed_out                      false
% 0.83/0.98  --preprocessed_stats                    false
% 0.83/0.98  
% 0.83/0.98  ------ Abstraction refinement Options
% 0.83/0.98  
% 0.83/0.98  --abstr_ref                             []
% 0.83/0.98  --abstr_ref_prep                        false
% 0.83/0.98  --abstr_ref_until_sat                   false
% 0.83/0.98  --abstr_ref_sig_restrict                funpre
% 0.83/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.83/0.98  --abstr_ref_under                       []
% 0.83/0.98  
% 0.83/0.98  ------ SAT Options
% 0.83/0.98  
% 0.83/0.98  --sat_mode                              false
% 0.83/0.98  --sat_fm_restart_options                ""
% 0.83/0.98  --sat_gr_def                            false
% 0.83/0.98  --sat_epr_types                         true
% 0.83/0.98  --sat_non_cyclic_types                  false
% 0.83/0.98  --sat_finite_models                     false
% 0.83/0.98  --sat_fm_lemmas                         false
% 0.83/0.98  --sat_fm_prep                           false
% 0.83/0.98  --sat_fm_uc_incr                        true
% 0.83/0.98  --sat_out_model                         small
% 0.83/0.98  --sat_out_clauses                       false
% 0.83/0.98  
% 0.83/0.98  ------ QBF Options
% 0.83/0.98  
% 0.83/0.98  --qbf_mode                              false
% 0.83/0.98  --qbf_elim_univ                         false
% 0.83/0.98  --qbf_dom_inst                          none
% 0.83/0.98  --qbf_dom_pre_inst                      false
% 0.83/0.98  --qbf_sk_in                             false
% 0.83/0.98  --qbf_pred_elim                         true
% 0.83/0.98  --qbf_split                             512
% 0.83/0.98  
% 0.83/0.98  ------ BMC1 Options
% 0.83/0.98  
% 0.83/0.98  --bmc1_incremental                      false
% 0.83/0.98  --bmc1_axioms                           reachable_all
% 0.83/0.98  --bmc1_min_bound                        0
% 0.83/0.98  --bmc1_max_bound                        -1
% 0.83/0.98  --bmc1_max_bound_default                -1
% 0.83/0.98  --bmc1_symbol_reachability              true
% 0.83/0.98  --bmc1_property_lemmas                  false
% 0.83/0.98  --bmc1_k_induction                      false
% 0.83/0.98  --bmc1_non_equiv_states                 false
% 0.83/0.98  --bmc1_deadlock                         false
% 0.83/0.98  --bmc1_ucm                              false
% 0.83/0.98  --bmc1_add_unsat_core                   none
% 0.83/0.98  --bmc1_unsat_core_children              false
% 0.83/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.83/0.98  --bmc1_out_stat                         full
% 0.83/0.98  --bmc1_ground_init                      false
% 0.83/0.98  --bmc1_pre_inst_next_state              false
% 0.83/0.98  --bmc1_pre_inst_state                   false
% 0.83/0.98  --bmc1_pre_inst_reach_state             false
% 0.83/0.98  --bmc1_out_unsat_core                   false
% 0.83/0.98  --bmc1_aig_witness_out                  false
% 0.83/0.98  --bmc1_verbose                          false
% 0.83/0.98  --bmc1_dump_clauses_tptp                false
% 0.83/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.83/0.98  --bmc1_dump_file                        -
% 0.83/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.83/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.83/0.98  --bmc1_ucm_extend_mode                  1
% 0.83/0.98  --bmc1_ucm_init_mode                    2
% 0.83/0.98  --bmc1_ucm_cone_mode                    none
% 0.83/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.83/0.98  --bmc1_ucm_relax_model                  4
% 0.83/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.83/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.83/0.98  --bmc1_ucm_layered_model                none
% 0.83/0.98  --bmc1_ucm_max_lemma_size               10
% 0.83/0.98  
% 0.83/0.98  ------ AIG Options
% 0.83/0.98  
% 0.83/0.98  --aig_mode                              false
% 0.83/0.98  
% 0.83/0.98  ------ Instantiation Options
% 0.83/0.98  
% 0.83/0.98  --instantiation_flag                    true
% 0.83/0.98  --inst_sos_flag                         false
% 0.83/0.98  --inst_sos_phase                        true
% 0.83/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.83/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.83/0.98  --inst_lit_sel_side                     num_symb
% 0.83/0.98  --inst_solver_per_active                1400
% 0.83/0.98  --inst_solver_calls_frac                1.
% 0.83/0.98  --inst_passive_queue_type               priority_queues
% 0.83/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.83/0.98  --inst_passive_queues_freq              [25;2]
% 0.83/0.98  --inst_dismatching                      true
% 0.83/0.98  --inst_eager_unprocessed_to_passive     true
% 0.83/0.98  --inst_prop_sim_given                   true
% 0.83/0.98  --inst_prop_sim_new                     false
% 0.83/0.98  --inst_subs_new                         false
% 0.83/0.98  --inst_eq_res_simp                      false
% 0.83/0.98  --inst_subs_given                       false
% 0.83/0.98  --inst_orphan_elimination               true
% 0.83/0.98  --inst_learning_loop_flag               true
% 0.83/0.98  --inst_learning_start                   3000
% 0.83/0.98  --inst_learning_factor                  2
% 0.83/0.98  --inst_start_prop_sim_after_learn       3
% 0.83/0.98  --inst_sel_renew                        solver
% 0.83/0.98  --inst_lit_activity_flag                true
% 0.83/0.98  --inst_restr_to_given                   false
% 0.83/0.98  --inst_activity_threshold               500
% 0.83/0.98  --inst_out_proof                        true
% 0.83/0.98  
% 0.83/0.98  ------ Resolution Options
% 0.83/0.98  
% 0.83/0.98  --resolution_flag                       true
% 0.83/0.98  --res_lit_sel                           adaptive
% 0.83/0.98  --res_lit_sel_side                      none
% 0.83/0.98  --res_ordering                          kbo
% 0.83/0.98  --res_to_prop_solver                    active
% 0.83/0.98  --res_prop_simpl_new                    false
% 0.83/0.98  --res_prop_simpl_given                  true
% 0.83/0.98  --res_passive_queue_type                priority_queues
% 0.83/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.83/0.98  --res_passive_queues_freq               [15;5]
% 0.83/0.98  --res_forward_subs                      full
% 0.83/0.98  --res_backward_subs                     full
% 0.83/0.98  --res_forward_subs_resolution           true
% 0.83/0.98  --res_backward_subs_resolution          true
% 0.83/0.98  --res_orphan_elimination                true
% 0.83/0.98  --res_time_limit                        2.
% 0.83/0.98  --res_out_proof                         true
% 0.83/0.98  
% 0.83/0.98  ------ Superposition Options
% 0.83/0.98  
% 0.83/0.98  --superposition_flag                    true
% 0.83/0.98  --sup_passive_queue_type                priority_queues
% 0.83/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.83/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.83/0.98  --demod_completeness_check              fast
% 0.83/0.98  --demod_use_ground                      true
% 0.83/0.98  --sup_to_prop_solver                    passive
% 0.83/0.98  --sup_prop_simpl_new                    true
% 0.83/0.98  --sup_prop_simpl_given                  true
% 0.83/0.98  --sup_fun_splitting                     false
% 0.83/0.98  --sup_smt_interval                      50000
% 0.83/0.98  
% 0.83/0.98  ------ Superposition Simplification Setup
% 0.83/0.98  
% 0.83/0.98  --sup_indices_passive                   []
% 0.83/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.83/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.98  --sup_full_bw                           [BwDemod]
% 0.83/0.98  --sup_immed_triv                        [TrivRules]
% 0.83/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.83/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.98  --sup_immed_bw_main                     []
% 0.83/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.83/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/0.98  
% 0.83/0.98  ------ Combination Options
% 0.83/0.98  
% 0.83/0.98  --comb_res_mult                         3
% 0.83/0.98  --comb_sup_mult                         2
% 0.83/0.98  --comb_inst_mult                        10
% 0.83/0.98  
% 0.83/0.98  ------ Debug Options
% 0.83/0.98  
% 0.83/0.98  --dbg_backtrace                         false
% 0.83/0.98  --dbg_dump_prop_clauses                 false
% 0.83/0.98  --dbg_dump_prop_clauses_file            -
% 0.83/0.98  --dbg_out_stat                          false
% 0.83/0.98  ------ Parsing...
% 0.83/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.83/0.98  
% 0.83/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.83/0.98  
% 0.83/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.83/0.98  
% 0.83/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.83/0.98  ------ Proving...
% 0.83/0.98  ------ Problem Properties 
% 0.83/0.98  
% 0.83/0.98  
% 0.83/0.98  clauses                                 12
% 0.83/0.98  conjectures                             4
% 0.83/0.98  EPR                                     3
% 0.83/0.98  Horn                                    12
% 0.83/0.98  unary                                   4
% 0.83/0.98  binary                                  0
% 0.83/0.98  lits                                    40
% 0.83/0.98  lits eq                                 9
% 0.83/0.98  fd_pure                                 0
% 0.83/0.98  fd_pseudo                               0
% 0.83/0.98  fd_cond                                 0
% 0.83/0.98  fd_pseudo_cond                          1
% 0.83/0.98  AC symbols                              0
% 0.83/0.98  
% 0.83/0.98  ------ Schedule dynamic 5 is on 
% 0.83/0.98  
% 0.83/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.83/0.98  
% 0.83/0.98  
% 0.83/0.98  ------ 
% 0.83/0.98  Current options:
% 0.83/0.98  ------ 
% 0.83/0.98  
% 0.83/0.98  ------ Input Options
% 0.83/0.98  
% 0.83/0.98  --out_options                           all
% 0.83/0.98  --tptp_safe_out                         true
% 0.83/0.98  --problem_path                          ""
% 0.83/0.98  --include_path                          ""
% 0.83/0.98  --clausifier                            res/vclausify_rel
% 0.83/0.98  --clausifier_options                    --mode clausify
% 0.83/0.98  --stdin                                 false
% 0.83/0.98  --stats_out                             all
% 0.83/0.98  
% 0.83/0.98  ------ General Options
% 0.83/0.98  
% 0.83/0.98  --fof                                   false
% 0.83/0.98  --time_out_real                         305.
% 0.83/0.98  --time_out_virtual                      -1.
% 0.83/0.98  --symbol_type_check                     false
% 0.83/0.98  --clausify_out                          false
% 0.83/0.98  --sig_cnt_out                           false
% 0.83/0.98  --trig_cnt_out                          false
% 0.83/0.98  --trig_cnt_out_tolerance                1.
% 0.83/0.98  --trig_cnt_out_sk_spl                   false
% 0.83/0.98  --abstr_cl_out                          false
% 0.83/0.98  
% 0.83/0.98  ------ Global Options
% 0.83/0.98  
% 0.83/0.98  --schedule                              default
% 0.83/0.98  --add_important_lit                     false
% 0.83/0.98  --prop_solver_per_cl                    1000
% 0.83/0.98  --min_unsat_core                        false
% 0.83/0.98  --soft_assumptions                      false
% 0.83/0.98  --soft_lemma_size                       3
% 0.83/0.98  --prop_impl_unit_size                   0
% 0.83/0.98  --prop_impl_unit                        []
% 0.83/0.98  --share_sel_clauses                     true
% 0.83/0.98  --reset_solvers                         false
% 0.83/0.98  --bc_imp_inh                            [conj_cone]
% 0.83/0.98  --conj_cone_tolerance                   3.
% 0.83/0.98  --extra_neg_conj                        none
% 0.83/0.98  --large_theory_mode                     true
% 0.83/0.98  --prolific_symb_bound                   200
% 0.83/0.98  --lt_threshold                          2000
% 0.83/0.98  --clause_weak_htbl                      true
% 0.83/0.98  --gc_record_bc_elim                     false
% 0.83/0.98  
% 0.83/0.98  ------ Preprocessing Options
% 0.83/0.98  
% 0.83/0.98  --preprocessing_flag                    true
% 0.83/0.98  --time_out_prep_mult                    0.1
% 0.83/0.98  --splitting_mode                        input
% 0.83/0.98  --splitting_grd                         true
% 0.83/0.98  --splitting_cvd                         false
% 0.83/0.98  --splitting_cvd_svl                     false
% 0.83/0.98  --splitting_nvd                         32
% 0.83/0.98  --sub_typing                            true
% 0.83/0.98  --prep_gs_sim                           true
% 0.83/0.98  --prep_unflatten                        true
% 0.83/0.98  --prep_res_sim                          true
% 0.83/0.98  --prep_upred                            true
% 0.83/0.98  --prep_sem_filter                       exhaustive
% 0.83/0.98  --prep_sem_filter_out                   false
% 0.83/0.98  --pred_elim                             true
% 0.83/0.98  --res_sim_input                         true
% 0.83/0.98  --eq_ax_congr_red                       true
% 0.83/0.98  --pure_diseq_elim                       true
% 0.83/0.98  --brand_transform                       false
% 0.83/0.98  --non_eq_to_eq                          false
% 0.83/0.98  --prep_def_merge                        true
% 0.83/0.98  --prep_def_merge_prop_impl              false
% 0.83/0.98  --prep_def_merge_mbd                    true
% 0.83/0.98  --prep_def_merge_tr_red                 false
% 0.83/0.98  --prep_def_merge_tr_cl                  false
% 0.83/0.98  --smt_preprocessing                     true
% 0.83/0.98  --smt_ac_axioms                         fast
% 0.83/0.98  --preprocessed_out                      false
% 0.83/0.98  --preprocessed_stats                    false
% 0.83/0.98  
% 0.83/0.98  ------ Abstraction refinement Options
% 0.83/0.98  
% 0.83/0.98  --abstr_ref                             []
% 0.83/0.98  --abstr_ref_prep                        false
% 0.83/0.98  --abstr_ref_until_sat                   false
% 0.83/0.98  --abstr_ref_sig_restrict                funpre
% 0.83/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.83/0.98  --abstr_ref_under                       []
% 0.83/0.98  
% 0.83/0.98  ------ SAT Options
% 0.83/0.98  
% 0.83/0.98  --sat_mode                              false
% 0.83/0.98  --sat_fm_restart_options                ""
% 0.83/0.98  --sat_gr_def                            false
% 0.83/0.99  --sat_epr_types                         true
% 0.83/0.99  --sat_non_cyclic_types                  false
% 0.83/0.99  --sat_finite_models                     false
% 0.83/0.99  --sat_fm_lemmas                         false
% 0.83/0.99  --sat_fm_prep                           false
% 0.83/0.99  --sat_fm_uc_incr                        true
% 0.83/0.99  --sat_out_model                         small
% 0.83/0.99  --sat_out_clauses                       false
% 0.83/0.99  
% 0.83/0.99  ------ QBF Options
% 0.83/0.99  
% 0.83/0.99  --qbf_mode                              false
% 0.83/0.99  --qbf_elim_univ                         false
% 0.83/0.99  --qbf_dom_inst                          none
% 0.83/0.99  --qbf_dom_pre_inst                      false
% 0.83/0.99  --qbf_sk_in                             false
% 0.83/0.99  --qbf_pred_elim                         true
% 0.83/0.99  --qbf_split                             512
% 0.83/0.99  
% 0.83/0.99  ------ BMC1 Options
% 0.83/0.99  
% 0.83/0.99  --bmc1_incremental                      false
% 0.83/0.99  --bmc1_axioms                           reachable_all
% 0.83/0.99  --bmc1_min_bound                        0
% 0.83/0.99  --bmc1_max_bound                        -1
% 0.83/0.99  --bmc1_max_bound_default                -1
% 0.83/0.99  --bmc1_symbol_reachability              true
% 0.83/0.99  --bmc1_property_lemmas                  false
% 0.83/0.99  --bmc1_k_induction                      false
% 0.83/0.99  --bmc1_non_equiv_states                 false
% 0.83/0.99  --bmc1_deadlock                         false
% 0.83/0.99  --bmc1_ucm                              false
% 0.83/0.99  --bmc1_add_unsat_core                   none
% 0.83/0.99  --bmc1_unsat_core_children              false
% 0.83/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.83/0.99  --bmc1_out_stat                         full
% 0.83/0.99  --bmc1_ground_init                      false
% 0.83/0.99  --bmc1_pre_inst_next_state              false
% 0.83/0.99  --bmc1_pre_inst_state                   false
% 0.83/0.99  --bmc1_pre_inst_reach_state             false
% 0.83/0.99  --bmc1_out_unsat_core                   false
% 0.83/0.99  --bmc1_aig_witness_out                  false
% 0.83/0.99  --bmc1_verbose                          false
% 0.83/0.99  --bmc1_dump_clauses_tptp                false
% 0.83/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.83/0.99  --bmc1_dump_file                        -
% 0.83/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.83/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.83/0.99  --bmc1_ucm_extend_mode                  1
% 0.83/0.99  --bmc1_ucm_init_mode                    2
% 0.83/0.99  --bmc1_ucm_cone_mode                    none
% 0.83/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.83/0.99  --bmc1_ucm_relax_model                  4
% 0.83/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.83/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.83/0.99  --bmc1_ucm_layered_model                none
% 0.83/0.99  --bmc1_ucm_max_lemma_size               10
% 0.83/0.99  
% 0.83/0.99  ------ AIG Options
% 0.83/0.99  
% 0.83/0.99  --aig_mode                              false
% 0.83/0.99  
% 0.83/0.99  ------ Instantiation Options
% 0.83/0.99  
% 0.83/0.99  --instantiation_flag                    true
% 0.83/0.99  --inst_sos_flag                         false
% 0.83/0.99  --inst_sos_phase                        true
% 0.83/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.83/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.83/0.99  --inst_lit_sel_side                     none
% 0.83/0.99  --inst_solver_per_active                1400
% 0.83/0.99  --inst_solver_calls_frac                1.
% 0.83/0.99  --inst_passive_queue_type               priority_queues
% 0.83/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.83/0.99  --inst_passive_queues_freq              [25;2]
% 0.83/0.99  --inst_dismatching                      true
% 0.83/0.99  --inst_eager_unprocessed_to_passive     true
% 0.83/0.99  --inst_prop_sim_given                   true
% 0.83/0.99  --inst_prop_sim_new                     false
% 0.83/0.99  --inst_subs_new                         false
% 0.83/0.99  --inst_eq_res_simp                      false
% 0.83/0.99  --inst_subs_given                       false
% 0.83/0.99  --inst_orphan_elimination               true
% 0.83/0.99  --inst_learning_loop_flag               true
% 0.83/0.99  --inst_learning_start                   3000
% 0.83/0.99  --inst_learning_factor                  2
% 0.83/0.99  --inst_start_prop_sim_after_learn       3
% 0.83/0.99  --inst_sel_renew                        solver
% 0.83/0.99  --inst_lit_activity_flag                true
% 0.83/0.99  --inst_restr_to_given                   false
% 0.83/0.99  --inst_activity_threshold               500
% 0.83/0.99  --inst_out_proof                        true
% 0.83/0.99  
% 0.83/0.99  ------ Resolution Options
% 0.83/0.99  
% 0.83/0.99  --resolution_flag                       false
% 0.83/0.99  --res_lit_sel                           adaptive
% 0.83/0.99  --res_lit_sel_side                      none
% 0.83/0.99  --res_ordering                          kbo
% 0.83/0.99  --res_to_prop_solver                    active
% 0.83/0.99  --res_prop_simpl_new                    false
% 0.83/0.99  --res_prop_simpl_given                  true
% 0.83/0.99  --res_passive_queue_type                priority_queues
% 0.83/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.83/0.99  --res_passive_queues_freq               [15;5]
% 0.83/0.99  --res_forward_subs                      full
% 0.83/0.99  --res_backward_subs                     full
% 0.83/0.99  --res_forward_subs_resolution           true
% 0.83/0.99  --res_backward_subs_resolution          true
% 0.83/0.99  --res_orphan_elimination                true
% 0.83/0.99  --res_time_limit                        2.
% 0.83/0.99  --res_out_proof                         true
% 0.83/0.99  
% 0.83/0.99  ------ Superposition Options
% 0.83/0.99  
% 0.83/0.99  --superposition_flag                    true
% 0.83/0.99  --sup_passive_queue_type                priority_queues
% 0.83/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.83/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.83/0.99  --demod_completeness_check              fast
% 0.83/0.99  --demod_use_ground                      true
% 0.83/0.99  --sup_to_prop_solver                    passive
% 0.83/0.99  --sup_prop_simpl_new                    true
% 0.83/0.99  --sup_prop_simpl_given                  true
% 0.83/0.99  --sup_fun_splitting                     false
% 0.83/0.99  --sup_smt_interval                      50000
% 0.83/0.99  
% 0.83/0.99  ------ Superposition Simplification Setup
% 0.83/0.99  
% 0.83/0.99  --sup_indices_passive                   []
% 0.83/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.83/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.99  --sup_full_bw                           [BwDemod]
% 0.83/0.99  --sup_immed_triv                        [TrivRules]
% 0.83/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.83/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.99  --sup_immed_bw_main                     []
% 0.83/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.83/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/0.99  
% 0.83/0.99  ------ Combination Options
% 0.83/0.99  
% 0.83/0.99  --comb_res_mult                         3
% 0.83/0.99  --comb_sup_mult                         2
% 0.83/0.99  --comb_inst_mult                        10
% 0.83/0.99  
% 0.83/0.99  ------ Debug Options
% 0.83/0.99  
% 0.83/0.99  --dbg_backtrace                         false
% 0.83/0.99  --dbg_dump_prop_clauses                 false
% 0.83/0.99  --dbg_dump_prop_clauses_file            -
% 0.83/0.99  --dbg_out_stat                          false
% 0.83/0.99  
% 0.83/0.99  
% 0.83/0.99  
% 0.83/0.99  
% 0.83/0.99  ------ Proving...
% 0.83/0.99  
% 0.83/0.99  
% 0.83/0.99  % SZS status Theorem for theBenchmark.p
% 0.83/0.99  
% 0.83/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 0.83/0.99  
% 0.83/0.99  fof(f6,conjecture,(
% 0.83/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/0.99  
% 0.83/0.99  fof(f7,negated_conjecture,(
% 0.83/0.99    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.83/0.99    inference(negated_conjecture,[],[f6])).
% 0.83/0.99  
% 0.83/0.99  fof(f18,plain,(
% 0.83/0.99    ? [X0] : ((k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.83/0.99    inference(ennf_transformation,[],[f7])).
% 0.83/0.99  
% 0.83/0.99  fof(f19,plain,(
% 0.83/0.99    ? [X0] : (k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.83/0.99    inference(flattening,[],[f18])).
% 0.83/0.99  
% 0.83/0.99  fof(f20,plain,(
% 0.83/0.99    ? [X0] : (k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (k2_funct_1(k2_funct_1(sK0)) != sK0 & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.83/0.99    introduced(choice_axiom,[])).
% 0.83/0.99  
% 0.83/0.99  fof(f21,plain,(
% 0.83/0.99    k2_funct_1(k2_funct_1(sK0)) != sK0 & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 0.83/0.99  
% 0.83/0.99  fof(f32,plain,(
% 0.83/0.99    v2_funct_1(sK0)),
% 0.83/0.99    inference(cnf_transformation,[],[f21])).
% 0.83/0.99  
% 0.83/0.99  fof(f4,axiom,(
% 0.83/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/0.99  
% 0.83/0.99  fof(f14,plain,(
% 0.83/0.99    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.83/0.99    inference(ennf_transformation,[],[f4])).
% 0.83/0.99  
% 0.83/0.99  fof(f15,plain,(
% 0.83/0.99    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.83/0.99    inference(flattening,[],[f14])).
% 0.83/0.99  
% 0.83/0.99  fof(f27,plain,(
% 0.83/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.83/0.99    inference(cnf_transformation,[],[f15])).
% 0.83/0.99  
% 0.83/0.99  fof(f30,plain,(
% 0.83/0.99    v1_relat_1(sK0)),
% 0.83/0.99    inference(cnf_transformation,[],[f21])).
% 0.83/0.99  
% 0.83/0.99  fof(f31,plain,(
% 0.83/0.99    v1_funct_1(sK0)),
% 0.83/0.99    inference(cnf_transformation,[],[f21])).
% 0.83/0.99  
% 0.83/0.99  fof(f5,axiom,(
% 0.83/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/0.99  
% 0.83/0.99  fof(f16,plain,(
% 0.83/0.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.83/0.99    inference(ennf_transformation,[],[f5])).
% 0.83/0.99  
% 0.83/0.99  fof(f17,plain,(
% 0.83/0.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.83/0.99    inference(flattening,[],[f16])).
% 0.83/0.99  
% 0.83/0.99  fof(f29,plain,(
% 0.83/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.83/0.99    inference(cnf_transformation,[],[f17])).
% 0.83/0.99  
% 0.83/0.99  fof(f3,axiom,(
% 0.83/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 0.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/0.99  
% 0.83/0.99  fof(f12,plain,(
% 0.83/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.83/0.99    inference(ennf_transformation,[],[f3])).
% 0.83/0.99  
% 0.83/0.99  fof(f13,plain,(
% 0.83/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.83/0.99    inference(flattening,[],[f12])).
% 0.83/0.99  
% 0.83/0.99  fof(f26,plain,(
% 0.83/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.83/0.99    inference(cnf_transformation,[],[f13])).
% 0.83/0.99  
% 0.83/0.99  fof(f25,plain,(
% 0.83/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.83/0.99    inference(cnf_transformation,[],[f13])).
% 0.83/0.99  
% 0.83/0.99  fof(f28,plain,(
% 0.83/0.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.83/0.99    inference(cnf_transformation,[],[f15])).
% 0.83/0.99  
% 0.83/0.99  fof(f2,axiom,(
% 0.83/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/0.99  
% 0.83/0.99  fof(f10,plain,(
% 0.83/0.99    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.83/0.99    inference(ennf_transformation,[],[f2])).
% 0.83/0.99  
% 0.83/0.99  fof(f11,plain,(
% 0.83/0.99    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.83/0.99    inference(flattening,[],[f10])).
% 0.83/0.99  
% 0.83/0.99  fof(f24,plain,(
% 0.83/0.99    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.83/0.99    inference(cnf_transformation,[],[f11])).
% 0.83/0.99  
% 0.83/0.99  fof(f33,plain,(
% 0.83/0.99    k2_funct_1(k2_funct_1(sK0)) != sK0),
% 0.83/0.99    inference(cnf_transformation,[],[f21])).
% 0.83/0.99  
% 0.83/0.99  fof(f1,axiom,(
% 0.83/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/0.99  
% 0.83/0.99  fof(f8,plain,(
% 0.83/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.83/0.99    inference(ennf_transformation,[],[f1])).
% 0.83/0.99  
% 0.83/0.99  fof(f9,plain,(
% 0.83/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.83/0.99    inference(flattening,[],[f8])).
% 0.83/0.99  
% 0.83/0.99  fof(f23,plain,(
% 0.83/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.83/0.99    inference(cnf_transformation,[],[f9])).
% 0.83/0.99  
% 0.83/0.99  fof(f22,plain,(
% 0.83/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.83/0.99    inference(cnf_transformation,[],[f9])).
% 0.83/0.99  
% 0.83/0.99  cnf(c_9,negated_conjecture,
% 0.83/0.99      ( v2_funct_1(sK0) ),
% 0.83/0.99      inference(cnf_transformation,[],[f32]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_354,negated_conjecture,
% 0.83/0.99      ( v2_funct_1(sK0) ),
% 0.83/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_602,plain,
% 0.83/0.99      ( v2_funct_1(sK0) = iProver_top ),
% 0.83/0.99      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_6,plain,
% 0.83/0.99      ( ~ v2_funct_1(X0)
% 0.83/0.99      | ~ v1_relat_1(X0)
% 0.83/0.99      | ~ v1_funct_1(X0)
% 0.83/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 0.83/0.99      inference(cnf_transformation,[],[f27]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_357,plain,
% 0.83/0.99      ( ~ v2_funct_1(X0_37)
% 0.83/0.99      | ~ v1_relat_1(X0_37)
% 0.83/0.99      | ~ v1_funct_1(X0_37)
% 0.83/0.99      | k5_relat_1(X0_37,k2_funct_1(X0_37)) = k6_relat_1(k1_relat_1(X0_37)) ),
% 0.83/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_600,plain,
% 0.83/0.99      ( k5_relat_1(X0_37,k2_funct_1(X0_37)) = k6_relat_1(k1_relat_1(X0_37))
% 0.83/0.99      | v2_funct_1(X0_37) != iProver_top
% 0.83/0.99      | v1_relat_1(X0_37) != iProver_top
% 0.83/0.99      | v1_funct_1(X0_37) != iProver_top ),
% 0.83/0.99      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_948,plain,
% 0.83/0.99      ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))
% 0.83/0.99      | v1_relat_1(sK0) != iProver_top
% 0.83/0.99      | v1_funct_1(sK0) != iProver_top ),
% 0.83/0.99      inference(superposition,[status(thm)],[c_602,c_600]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_11,negated_conjecture,
% 0.83/0.99      ( v1_relat_1(sK0) ),
% 0.83/0.99      inference(cnf_transformation,[],[f30]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_10,negated_conjecture,
% 0.83/0.99      ( v1_funct_1(sK0) ),
% 0.83/0.99      inference(cnf_transformation,[],[f31]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_404,plain,
% 0.83/0.99      ( ~ v2_funct_1(sK0)
% 0.83/0.99      | ~ v1_relat_1(sK0)
% 0.83/0.99      | ~ v1_funct_1(sK0)
% 0.83/0.99      | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
% 0.83/0.99      inference(instantiation,[status(thm)],[c_357]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_1137,plain,
% 0.83/0.99      ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
% 0.83/0.99      inference(global_propositional_subsumption,
% 0.83/0.99                [status(thm)],
% 0.83/0.99                [c_948,c_11,c_10,c_9,c_404]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_7,plain,
% 0.83/0.99      ( ~ v2_funct_1(X0)
% 0.83/0.99      | ~ v1_relat_1(X0)
% 0.83/0.99      | ~ v1_relat_1(X1)
% 0.83/0.99      | ~ v1_funct_1(X0)
% 0.83/0.99      | ~ v1_funct_1(X1)
% 0.83/0.99      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
% 0.83/0.99      | k2_relat_1(X1) != k1_relat_1(X0)
% 0.83/0.99      | k2_funct_1(X0) = X1 ),
% 0.83/0.99      inference(cnf_transformation,[],[f29]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_356,plain,
% 0.83/0.99      ( ~ v2_funct_1(X0_37)
% 0.83/0.99      | ~ v1_relat_1(X0_37)
% 0.83/0.99      | ~ v1_relat_1(X1_37)
% 0.83/0.99      | ~ v1_funct_1(X0_37)
% 0.83/0.99      | ~ v1_funct_1(X1_37)
% 0.83/0.99      | k2_relat_1(X1_37) != k1_relat_1(X0_37)
% 0.83/0.99      | k5_relat_1(X1_37,X0_37) != k6_relat_1(k2_relat_1(X0_37))
% 0.83/0.99      | k2_funct_1(X0_37) = X1_37 ),
% 0.83/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_601,plain,
% 0.83/0.99      ( k2_relat_1(X0_37) != k1_relat_1(X1_37)
% 0.83/0.99      | k5_relat_1(X0_37,X1_37) != k6_relat_1(k2_relat_1(X1_37))
% 0.83/0.99      | k2_funct_1(X1_37) = X0_37
% 0.83/0.99      | v2_funct_1(X1_37) != iProver_top
% 0.83/0.99      | v1_relat_1(X0_37) != iProver_top
% 0.83/0.99      | v1_relat_1(X1_37) != iProver_top
% 0.83/0.99      | v1_funct_1(X0_37) != iProver_top
% 0.83/0.99      | v1_funct_1(X1_37) != iProver_top ),
% 0.83/0.99      inference(predicate_to_equality,[status(thm)],[c_356]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_1140,plain,
% 0.83/0.99      ( k1_relat_1(k2_funct_1(sK0)) != k2_relat_1(sK0)
% 0.83/0.99      | k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k6_relat_1(k1_relat_1(sK0))
% 0.83/0.99      | k2_funct_1(k2_funct_1(sK0)) = sK0
% 0.83/0.99      | v2_funct_1(k2_funct_1(sK0)) != iProver_top
% 0.83/0.99      | v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 0.83/0.99      | v1_relat_1(sK0) != iProver_top
% 0.83/0.99      | v1_funct_1(k2_funct_1(sK0)) != iProver_top
% 0.83/0.99      | v1_funct_1(sK0) != iProver_top ),
% 0.83/0.99      inference(superposition,[status(thm)],[c_1137,c_601]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_3,plain,
% 0.83/0.99      ( ~ v2_funct_1(X0)
% 0.83/0.99      | ~ v1_relat_1(X0)
% 0.83/0.99      | ~ v1_funct_1(X0)
% 0.83/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 0.83/0.99      inference(cnf_transformation,[],[f26]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_360,plain,
% 0.83/0.99      ( ~ v2_funct_1(X0_37)
% 0.83/0.99      | ~ v1_relat_1(X0_37)
% 0.83/0.99      | ~ v1_funct_1(X0_37)
% 0.83/0.99      | k2_relat_1(k2_funct_1(X0_37)) = k1_relat_1(X0_37) ),
% 0.83/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_597,plain,
% 0.83/0.99      ( k2_relat_1(k2_funct_1(X0_37)) = k1_relat_1(X0_37)
% 0.83/0.99      | v2_funct_1(X0_37) != iProver_top
% 0.83/0.99      | v1_relat_1(X0_37) != iProver_top
% 0.83/0.99      | v1_funct_1(X0_37) != iProver_top ),
% 0.83/0.99      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_788,plain,
% 0.83/0.99      ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
% 0.83/0.99      | v1_relat_1(sK0) != iProver_top
% 0.83/0.99      | v1_funct_1(sK0) != iProver_top ),
% 0.83/0.99      inference(superposition,[status(thm)],[c_602,c_597]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_395,plain,
% 0.83/0.99      ( ~ v2_funct_1(sK0)
% 0.83/0.99      | ~ v1_relat_1(sK0)
% 0.83/0.99      | ~ v1_funct_1(sK0)
% 0.83/0.99      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 0.83/0.99      inference(instantiation,[status(thm)],[c_360]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_791,plain,
% 0.83/0.99      ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 0.83/0.99      inference(global_propositional_subsumption,
% 0.83/0.99                [status(thm)],
% 0.83/0.99                [c_788,c_11,c_10,c_9,c_395]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_4,plain,
% 0.83/0.99      ( ~ v2_funct_1(X0)
% 0.83/0.99      | ~ v1_relat_1(X0)
% 0.83/0.99      | ~ v1_funct_1(X0)
% 0.83/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 0.83/0.99      inference(cnf_transformation,[],[f25]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_359,plain,
% 0.83/0.99      ( ~ v2_funct_1(X0_37)
% 0.83/0.99      | ~ v1_relat_1(X0_37)
% 0.83/0.99      | ~ v1_funct_1(X0_37)
% 0.83/0.99      | k1_relat_1(k2_funct_1(X0_37)) = k2_relat_1(X0_37) ),
% 0.83/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_598,plain,
% 0.83/0.99      ( k1_relat_1(k2_funct_1(X0_37)) = k2_relat_1(X0_37)
% 0.83/0.99      | v2_funct_1(X0_37) != iProver_top
% 0.83/0.99      | v1_relat_1(X0_37) != iProver_top
% 0.83/0.99      | v1_funct_1(X0_37) != iProver_top ),
% 0.83/0.99      inference(predicate_to_equality,[status(thm)],[c_359]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_852,plain,
% 0.83/0.99      ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0)
% 0.83/0.99      | v1_relat_1(sK0) != iProver_top
% 0.83/0.99      | v1_funct_1(sK0) != iProver_top ),
% 0.83/0.99      inference(superposition,[status(thm)],[c_602,c_598]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_398,plain,
% 0.83/0.99      ( ~ v2_funct_1(sK0)
% 0.83/0.99      | ~ v1_relat_1(sK0)
% 0.83/0.99      | ~ v1_funct_1(sK0)
% 0.83/0.99      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 0.83/0.99      inference(instantiation,[status(thm)],[c_359]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_1032,plain,
% 0.83/0.99      ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 0.83/0.99      inference(global_propositional_subsumption,
% 0.83/0.99                [status(thm)],
% 0.83/0.99                [c_852,c_11,c_10,c_9,c_398]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_1150,plain,
% 0.83/0.99      ( k2_relat_1(sK0) != k2_relat_1(sK0)
% 0.83/0.99      | k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
% 0.83/0.99      | k2_funct_1(k2_funct_1(sK0)) = sK0
% 0.83/0.99      | v2_funct_1(k2_funct_1(sK0)) != iProver_top
% 0.83/0.99      | v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 0.83/0.99      | v1_relat_1(sK0) != iProver_top
% 0.83/0.99      | v1_funct_1(k2_funct_1(sK0)) != iProver_top
% 0.83/0.99      | v1_funct_1(sK0) != iProver_top ),
% 0.83/0.99      inference(light_normalisation,[status(thm)],[c_1140,c_791,c_1032]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_1151,plain,
% 0.83/0.99      ( k2_funct_1(k2_funct_1(sK0)) = sK0
% 0.83/0.99      | v2_funct_1(k2_funct_1(sK0)) != iProver_top
% 0.83/0.99      | v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 0.83/0.99      | v1_relat_1(sK0) != iProver_top
% 0.83/0.99      | v1_funct_1(k2_funct_1(sK0)) != iProver_top
% 0.83/0.99      | v1_funct_1(sK0) != iProver_top ),
% 0.83/0.99      inference(equality_resolution_simp,[status(thm)],[c_1150]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_5,plain,
% 0.83/0.99      ( ~ v2_funct_1(X0)
% 0.83/0.99      | ~ v1_relat_1(X0)
% 0.83/0.99      | ~ v1_funct_1(X0)
% 0.83/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
% 0.83/0.99      inference(cnf_transformation,[],[f28]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_358,plain,
% 0.83/0.99      ( ~ v2_funct_1(X0_37)
% 0.83/0.99      | ~ v1_relat_1(X0_37)
% 0.83/0.99      | ~ v1_funct_1(X0_37)
% 0.83/0.99      | k5_relat_1(k2_funct_1(X0_37),X0_37) = k6_relat_1(k2_relat_1(X0_37)) ),
% 0.83/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_599,plain,
% 0.83/0.99      ( k5_relat_1(k2_funct_1(X0_37),X0_37) = k6_relat_1(k2_relat_1(X0_37))
% 0.83/0.99      | v2_funct_1(X0_37) != iProver_top
% 0.83/0.99      | v1_relat_1(X0_37) != iProver_top
% 0.83/0.99      | v1_funct_1(X0_37) != iProver_top ),
% 0.83/0.99      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_941,plain,
% 0.83/0.99      ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
% 0.83/0.99      | v1_relat_1(sK0) != iProver_top
% 0.83/0.99      | v1_funct_1(sK0) != iProver_top ),
% 0.83/0.99      inference(superposition,[status(thm)],[c_602,c_599]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_401,plain,
% 0.83/0.99      ( ~ v2_funct_1(sK0)
% 0.83/0.99      | ~ v1_relat_1(sK0)
% 0.83/0.99      | ~ v1_funct_1(sK0)
% 0.83/0.99      | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 0.83/0.99      inference(instantiation,[status(thm)],[c_358]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_1117,plain,
% 0.83/0.99      ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 0.83/0.99      inference(global_propositional_subsumption,
% 0.83/0.99                [status(thm)],
% 0.83/0.99                [c_941,c_11,c_10,c_9,c_401]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_2,plain,
% 0.83/0.99      ( v2_funct_1(X0)
% 0.83/0.99      | ~ v1_relat_1(X0)
% 0.83/0.99      | ~ v1_relat_1(X1)
% 0.83/0.99      | ~ v1_funct_1(X0)
% 0.83/0.99      | ~ v1_funct_1(X1)
% 0.83/0.99      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) ),
% 0.83/0.99      inference(cnf_transformation,[],[f24]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_361,plain,
% 0.83/0.99      ( v2_funct_1(X0_37)
% 0.83/0.99      | ~ v1_relat_1(X0_37)
% 0.83/0.99      | ~ v1_relat_1(X1_37)
% 0.83/0.99      | ~ v1_funct_1(X0_37)
% 0.83/0.99      | ~ v1_funct_1(X1_37)
% 0.83/0.99      | k5_relat_1(X0_37,X1_37) != k6_relat_1(k1_relat_1(X0_37)) ),
% 0.83/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_596,plain,
% 0.83/0.99      ( k5_relat_1(X0_37,X1_37) != k6_relat_1(k1_relat_1(X0_37))
% 0.83/0.99      | v2_funct_1(X0_37) = iProver_top
% 0.83/0.99      | v1_relat_1(X1_37) != iProver_top
% 0.83/0.99      | v1_relat_1(X0_37) != iProver_top
% 0.83/0.99      | v1_funct_1(X1_37) != iProver_top
% 0.83/0.99      | v1_funct_1(X0_37) != iProver_top ),
% 0.83/0.99      inference(predicate_to_equality,[status(thm)],[c_361]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_1121,plain,
% 0.83/0.99      ( k6_relat_1(k1_relat_1(k2_funct_1(sK0))) != k6_relat_1(k2_relat_1(sK0))
% 0.83/0.99      | v2_funct_1(k2_funct_1(sK0)) = iProver_top
% 0.83/0.99      | v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 0.83/0.99      | v1_relat_1(sK0) != iProver_top
% 0.83/0.99      | v1_funct_1(k2_funct_1(sK0)) != iProver_top
% 0.83/0.99      | v1_funct_1(sK0) != iProver_top ),
% 0.83/0.99      inference(superposition,[status(thm)],[c_1117,c_596]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_1128,plain,
% 0.83/0.99      ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0))
% 0.83/0.99      | v2_funct_1(k2_funct_1(sK0)) = iProver_top
% 0.83/0.99      | v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 0.83/0.99      | v1_relat_1(sK0) != iProver_top
% 0.83/0.99      | v1_funct_1(k2_funct_1(sK0)) != iProver_top
% 0.83/0.99      | v1_funct_1(sK0) != iProver_top ),
% 0.83/0.99      inference(light_normalisation,[status(thm)],[c_1121,c_1032]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_1129,plain,
% 0.83/0.99      ( v2_funct_1(k2_funct_1(sK0)) = iProver_top
% 0.83/0.99      | v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 0.83/0.99      | v1_relat_1(sK0) != iProver_top
% 0.83/0.99      | v1_funct_1(k2_funct_1(sK0)) != iProver_top
% 0.83/0.99      | v1_funct_1(sK0) != iProver_top ),
% 0.83/0.99      inference(equality_resolution_simp,[status(thm)],[c_1128]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_8,negated_conjecture,
% 0.83/0.99      ( k2_funct_1(k2_funct_1(sK0)) != sK0 ),
% 0.83/0.99      inference(cnf_transformation,[],[f33]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_355,negated_conjecture,
% 0.83/0.99      ( k2_funct_1(k2_funct_1(sK0)) != sK0 ),
% 0.83/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_0,plain,
% 0.83/0.99      ( ~ v1_relat_1(X0)
% 0.83/0.99      | ~ v1_funct_1(X0)
% 0.83/0.99      | v1_funct_1(k2_funct_1(X0)) ),
% 0.83/0.99      inference(cnf_transformation,[],[f23]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_34,plain,
% 0.83/0.99      ( v1_relat_1(X0) != iProver_top
% 0.83/0.99      | v1_funct_1(X0) != iProver_top
% 0.83/0.99      | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
% 0.83/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_36,plain,
% 0.83/0.99      ( v1_relat_1(sK0) != iProver_top
% 0.83/0.99      | v1_funct_1(k2_funct_1(sK0)) = iProver_top
% 0.83/0.99      | v1_funct_1(sK0) != iProver_top ),
% 0.83/0.99      inference(instantiation,[status(thm)],[c_34]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_1,plain,
% 0.83/0.99      ( ~ v1_relat_1(X0)
% 0.83/0.99      | v1_relat_1(k2_funct_1(X0))
% 0.83/0.99      | ~ v1_funct_1(X0) ),
% 0.83/0.99      inference(cnf_transformation,[],[f22]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_31,plain,
% 0.83/0.99      ( v1_relat_1(X0) != iProver_top
% 0.83/0.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top
% 0.83/0.99      | v1_funct_1(X0) != iProver_top ),
% 0.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_33,plain,
% 0.83/0.99      ( v1_relat_1(k2_funct_1(sK0)) = iProver_top
% 0.83/0.99      | v1_relat_1(sK0) != iProver_top
% 0.83/0.99      | v1_funct_1(sK0) != iProver_top ),
% 0.83/0.99      inference(instantiation,[status(thm)],[c_31]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_13,plain,
% 0.83/0.99      ( v1_funct_1(sK0) = iProver_top ),
% 0.83/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(c_12,plain,
% 0.83/0.99      ( v1_relat_1(sK0) = iProver_top ),
% 0.83/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.83/0.99  
% 0.83/0.99  cnf(contradiction,plain,
% 0.83/0.99      ( $false ),
% 0.83/0.99      inference(minisat,
% 0.83/0.99                [status(thm)],
% 0.83/0.99                [c_1151,c_1129,c_355,c_36,c_33,c_13,c_12]) ).
% 0.83/0.99  
% 0.83/0.99  
% 0.83/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 0.83/0.99  
% 0.83/0.99  ------                               Statistics
% 0.83/0.99  
% 0.83/0.99  ------ General
% 0.83/0.99  
% 0.83/0.99  abstr_ref_over_cycles:                  0
% 0.83/0.99  abstr_ref_under_cycles:                 0
% 0.83/0.99  gc_basic_clause_elim:                   0
% 0.83/0.99  forced_gc_time:                         0
% 0.83/0.99  parsing_time:                           0.008
% 0.83/0.99  unif_index_cands_time:                  0.
% 0.83/0.99  unif_index_add_time:                    0.
% 0.83/0.99  orderings_time:                         0.
% 0.83/0.99  out_proof_time:                         0.01
% 0.83/0.99  total_time:                             0.067
% 0.83/0.99  num_of_symbols:                         40
% 0.83/0.99  num_of_terms:                           838
% 0.83/0.99  
% 0.83/0.99  ------ Preprocessing
% 0.83/0.99  
% 0.83/0.99  num_of_splits:                          0
% 0.83/0.99  num_of_split_atoms:                     0
% 0.83/0.99  num_of_reused_defs:                     0
% 0.83/0.99  num_eq_ax_congr_red:                    0
% 0.83/0.99  num_of_sem_filtered_clauses:            1
% 0.83/0.99  num_of_subtypes:                        3
% 0.83/0.99  monotx_restored_types:                  0
% 0.83/0.99  sat_num_of_epr_types:                   0
% 0.83/0.99  sat_num_of_non_cyclic_types:            0
% 0.83/0.99  sat_guarded_non_collapsed_types:        1
% 0.83/0.99  num_pure_diseq_elim:                    0
% 0.83/0.99  simp_replaced_by:                       0
% 0.83/0.99  res_preprocessed:                       65
% 0.83/0.99  prep_upred:                             0
% 0.83/0.99  prep_unflattend:                        5
% 0.83/0.99  smt_new_axioms:                         0
% 0.83/0.99  pred_elim_cands:                        3
% 0.83/0.99  pred_elim:                              0
% 0.83/0.99  pred_elim_cl:                           0
% 0.83/0.99  pred_elim_cycles:                       1
% 0.83/0.99  merged_defs:                            0
% 0.83/0.99  merged_defs_ncl:                        0
% 0.83/0.99  bin_hyper_res:                          0
% 0.83/0.99  prep_cycles:                            3
% 0.83/0.99  pred_elim_time:                         0.003
% 0.83/0.99  splitting_time:                         0.
% 0.83/0.99  sem_filter_time:                        0.
% 0.83/0.99  monotx_time:                            0.
% 0.83/0.99  subtype_inf_time:                       0.
% 0.83/0.99  
% 0.83/0.99  ------ Problem properties
% 0.83/0.99  
% 0.83/0.99  clauses:                                12
% 0.83/0.99  conjectures:                            4
% 0.83/0.99  epr:                                    3
% 0.83/0.99  horn:                                   12
% 0.83/0.99  ground:                                 4
% 0.83/0.99  unary:                                  4
% 0.83/0.99  binary:                                 0
% 0.83/0.99  lits:                                   40
% 0.83/0.99  lits_eq:                                9
% 0.83/0.99  fd_pure:                                0
% 0.83/0.99  fd_pseudo:                              0
% 0.83/0.99  fd_cond:                                0
% 0.83/0.99  fd_pseudo_cond:                         1
% 0.83/0.99  ac_symbols:                             0
% 0.83/0.99  
% 0.83/0.99  ------ Propositional Solver
% 0.83/0.99  
% 0.83/0.99  prop_solver_calls:                      23
% 0.83/0.99  prop_fast_solver_calls:                 488
% 0.83/0.99  smt_solver_calls:                       0
% 0.83/0.99  smt_fast_solver_calls:                  0
% 0.83/0.99  prop_num_of_clauses:                    287
% 0.83/0.99  prop_preprocess_simplified:             1808
% 0.83/0.99  prop_fo_subsumed:                       18
% 0.83/0.99  prop_solver_time:                       0.
% 0.83/0.99  smt_solver_time:                        0.
% 0.83/0.99  smt_fast_solver_time:                   0.
% 0.83/0.99  prop_fast_solver_time:                  0.
% 0.83/0.99  prop_unsat_core_time:                   0.
% 0.83/0.99  
% 0.83/0.99  ------ QBF
% 0.83/0.99  
% 0.83/0.99  qbf_q_res:                              0
% 0.83/0.99  qbf_num_tautologies:                    0
% 0.83/0.99  qbf_prep_cycles:                        0
% 0.83/0.99  
% 0.83/0.99  ------ BMC1
% 0.83/0.99  
% 0.83/0.99  bmc1_current_bound:                     -1
% 0.83/0.99  bmc1_last_solved_bound:                 -1
% 0.83/0.99  bmc1_unsat_core_size:                   -1
% 0.83/0.99  bmc1_unsat_core_parents_size:           -1
% 0.83/0.99  bmc1_merge_next_fun:                    0
% 0.83/0.99  bmc1_unsat_core_clauses_time:           0.
% 0.83/0.99  
% 0.83/0.99  ------ Instantiation
% 0.83/0.99  
% 0.83/0.99  inst_num_of_clauses:                    120
% 0.83/0.99  inst_num_in_passive:                    36
% 0.83/0.99  inst_num_in_active:                     76
% 0.83/0.99  inst_num_in_unprocessed:                8
% 0.83/0.99  inst_num_of_loops:                      80
% 0.83/0.99  inst_num_of_learning_restarts:          0
% 0.83/0.99  inst_num_moves_active_passive:          0
% 0.83/0.99  inst_lit_activity:                      0
% 0.83/0.99  inst_lit_activity_moves:                0
% 0.83/0.99  inst_num_tautologies:                   0
% 0.83/0.99  inst_num_prop_implied:                  0
% 0.83/0.99  inst_num_existing_simplified:           0
% 0.83/0.99  inst_num_eq_res_simplified:             0
% 0.83/0.99  inst_num_child_elim:                    0
% 0.83/0.99  inst_num_of_dismatching_blockings:      26
% 0.83/0.99  inst_num_of_non_proper_insts:           102
% 0.83/0.99  inst_num_of_duplicates:                 0
% 0.83/0.99  inst_inst_num_from_inst_to_res:         0
% 0.83/0.99  inst_dismatching_checking_time:         0.
% 0.83/0.99  
% 0.83/0.99  ------ Resolution
% 0.83/0.99  
% 0.83/0.99  res_num_of_clauses:                     0
% 0.83/0.99  res_num_in_passive:                     0
% 0.83/0.99  res_num_in_active:                      0
% 0.83/0.99  res_num_of_loops:                       68
% 0.83/0.99  res_forward_subset_subsumed:            32
% 0.83/0.99  res_backward_subset_subsumed:           0
% 0.83/0.99  res_forward_subsumed:                   0
% 0.83/0.99  res_backward_subsumed:                  0
% 0.83/0.99  res_forward_subsumption_resolution:     0
% 0.83/0.99  res_backward_subsumption_resolution:    0
% 0.83/0.99  res_clause_to_clause_subsumption:       29
% 0.83/0.99  res_orphan_elimination:                 0
% 0.83/0.99  res_tautology_del:                      30
% 0.83/0.99  res_num_eq_res_simplified:              0
% 0.83/0.99  res_num_sel_changes:                    0
% 0.83/0.99  res_moves_from_active_to_pass:          0
% 0.83/0.99  
% 0.83/0.99  ------ Superposition
% 0.83/0.99  
% 0.83/0.99  sup_time_total:                         0.
% 0.83/0.99  sup_time_generating:                    0.
% 0.83/0.99  sup_time_sim_full:                      0.
% 0.83/0.99  sup_time_sim_immed:                     0.
% 0.83/0.99  
% 0.83/0.99  sup_num_of_clauses:                     18
% 0.83/0.99  sup_num_in_active:                      16
% 0.83/0.99  sup_num_in_passive:                     2
% 0.83/0.99  sup_num_of_loops:                       15
% 0.83/0.99  sup_fw_superposition:                   4
% 0.83/0.99  sup_bw_superposition:                   4
% 0.83/0.99  sup_immediate_simplified:               3
% 0.83/0.99  sup_given_eliminated:                   0
% 0.83/0.99  comparisons_done:                       0
% 0.83/0.99  comparisons_avoided:                    0
% 0.83/0.99  
% 0.83/0.99  ------ Simplifications
% 0.83/0.99  
% 0.83/0.99  
% 0.83/0.99  sim_fw_subset_subsumed:                 1
% 0.83/0.99  sim_bw_subset_subsumed:                 0
% 0.83/0.99  sim_fw_subsumed:                        0
% 0.83/0.99  sim_bw_subsumed:                        0
% 0.83/0.99  sim_fw_subsumption_res:                 0
% 0.83/0.99  sim_bw_subsumption_res:                 0
% 0.83/0.99  sim_tautology_del:                      0
% 0.83/0.99  sim_eq_tautology_del:                   1
% 0.83/0.99  sim_eq_res_simp:                        2
% 0.83/0.99  sim_fw_demodulated:                     0
% 0.83/0.99  sim_bw_demodulated:                     0
% 0.83/0.99  sim_light_normalised:                   2
% 0.83/0.99  sim_joinable_taut:                      0
% 0.83/0.99  sim_joinable_simp:                      0
% 0.83/0.99  sim_ac_normalised:                      0
% 0.83/0.99  sim_smt_subsumption:                    0
% 0.83/0.99  
%------------------------------------------------------------------------------
