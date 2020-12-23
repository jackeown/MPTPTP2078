%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:38 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 401 expanded)
%              Number of clauses        :   75 ( 127 expanded)
%              Number of leaves         :   15 (  82 expanded)
%              Depth                    :   19
%              Number of atoms          :  333 (1589 expanded)
%              Number of equality atoms :  202 ( 675 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) != k2_relat_1(X0) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) != k2_relat_1(X0) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,
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

fof(f28,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f43,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f41,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_496,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_497,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_500,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_498,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_relat_1(X1) != k1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(k5_relat_1(X2,X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_505,plain,
    ( k1_relat_1(X0) != k1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1400,plain,
    ( k1_relat_1(X0) != X1
    | k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X2,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_505])).

cnf(c_2007,plain,
    ( k1_relat_1(k5_relat_1(X0,k6_relat_1(k1_relat_1(X1)))) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(X1))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1400])).

cnf(c_6144,plain,
    ( k1_relat_1(k5_relat_1(X0,k6_relat_1(k1_relat_1(X1)))) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_498,c_2007])).

cnf(c_6153,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X0),k6_relat_1(k1_relat_1(X1)))) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X1))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_500,c_6144])).

cnf(c_12951,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0)))) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_497,c_6153])).

cnf(c_18,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13156,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0)))) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12951,c_18])).

cnf(c_13157,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0)))) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13156])).

cnf(c_13162,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(superposition,[status(thm)],[c_496,c_13157])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_15,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_180,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_181,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_180])).

cnf(c_22,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_183,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_181,c_17,c_16,c_15,c_22])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_503,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1198,plain,
    ( k5_relat_1(k2_funct_1(X0),k6_relat_1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_500,c_503])).

cnf(c_2907,plain,
    ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) = k2_funct_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_497,c_1198])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_188,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_189,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_25,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_191,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_189,c_17,c_16,c_15,c_25])).

cnf(c_2908,plain,
    ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k2_funct_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2907,c_191])).

cnf(c_3088,plain,
    ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k2_funct_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2908,c_18])).

cnf(c_13163,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_13162,c_183,c_3088])).

cnf(c_4,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k2_relat_1(X1) != k2_relat_1(X0)
    | k2_relat_1(k5_relat_1(X1,X2)) = k2_relat_1(k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_504,plain,
    ( k2_relat_1(X0) != k2_relat_1(X1)
    | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1281,plain,
    ( k2_relat_1(X0) != X1
    | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_504])).

cnf(c_1411,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
    | k1_relat_1(sK0) != X0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_191,c_1281])).

cnf(c_27,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1282,plain,
    ( k2_relat_1(X0) != k1_relat_1(sK0)
    | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1)) = k2_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_191,c_504])).

cnf(c_19,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

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

cnf(c_1503,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1)) = k2_relat_1(k5_relat_1(X0,X1))
    | k2_relat_1(X0) != k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1282,c_18,c_19,c_35])).

cnf(c_1504,plain,
    ( k2_relat_1(X0) != k1_relat_1(sK0)
    | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1)) = k2_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1503])).

cnf(c_1509,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
    | k1_relat_1(sK0) != X0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1504])).

cnf(c_1626,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
    | k1_relat_1(sK0) != X0
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1411,c_27,c_1509])).

cnf(c_1632,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1626])).

cnf(c_1639,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(superposition,[status(thm)],[c_496,c_1632])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_502,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_961,plain,
    ( k5_relat_1(k6_relat_1(X0),sK0) = k7_relat_1(sK0,X0) ),
    inference(superposition,[status(thm)],[c_496,c_502])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_506,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1108,plain,
    ( k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
    inference(superposition,[status(thm)],[c_496,c_506])).

cnf(c_1640,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_1639,c_961,c_1108])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_507,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_840,plain,
    ( k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_496,c_507])).

cnf(c_1641,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_1640,c_840])).

cnf(c_287,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_523,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != X0
    | k2_relat_1(sK0) != X0
    | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_527,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(X0)
    | k2_relat_1(sK0) != k2_relat_1(X0)
    | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_528,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)
    | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_286,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_305,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_290,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_298,plain,
    ( k2_relat_1(sK0) = k2_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_290])).

cnf(c_14,negated_conjecture,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13163,c_1641,c_528,c_305,c_298,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.81/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/0.97  
% 3.81/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.81/0.97  
% 3.81/0.97  ------  iProver source info
% 3.81/0.97  
% 3.81/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.81/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.81/0.97  git: non_committed_changes: false
% 3.81/0.97  git: last_make_outside_of_git: false
% 3.81/0.97  
% 3.81/0.97  ------ 
% 3.81/0.97  
% 3.81/0.97  ------ Input Options
% 3.81/0.97  
% 3.81/0.97  --out_options                           all
% 3.81/0.97  --tptp_safe_out                         true
% 3.81/0.97  --problem_path                          ""
% 3.81/0.97  --include_path                          ""
% 3.81/0.97  --clausifier                            res/vclausify_rel
% 3.81/0.97  --clausifier_options                    ""
% 3.81/0.97  --stdin                                 false
% 3.81/0.97  --stats_out                             all
% 3.81/0.97  
% 3.81/0.97  ------ General Options
% 3.81/0.97  
% 3.81/0.97  --fof                                   false
% 3.81/0.97  --time_out_real                         305.
% 3.81/0.97  --time_out_virtual                      -1.
% 3.81/0.97  --symbol_type_check                     false
% 3.81/0.97  --clausify_out                          false
% 3.81/0.97  --sig_cnt_out                           false
% 3.81/0.97  --trig_cnt_out                          false
% 3.81/0.97  --trig_cnt_out_tolerance                1.
% 3.81/0.97  --trig_cnt_out_sk_spl                   false
% 3.81/0.97  --abstr_cl_out                          false
% 3.81/0.97  
% 3.81/0.97  ------ Global Options
% 3.81/0.97  
% 3.81/0.97  --schedule                              default
% 3.81/0.97  --add_important_lit                     false
% 3.81/0.97  --prop_solver_per_cl                    1000
% 3.81/0.97  --min_unsat_core                        false
% 3.81/0.97  --soft_assumptions                      false
% 3.81/0.97  --soft_lemma_size                       3
% 3.81/0.97  --prop_impl_unit_size                   0
% 3.81/0.97  --prop_impl_unit                        []
% 3.81/0.97  --share_sel_clauses                     true
% 3.81/0.97  --reset_solvers                         false
% 3.81/0.97  --bc_imp_inh                            [conj_cone]
% 3.81/0.97  --conj_cone_tolerance                   3.
% 3.81/0.97  --extra_neg_conj                        none
% 3.81/0.97  --large_theory_mode                     true
% 3.81/0.97  --prolific_symb_bound                   200
% 3.81/0.97  --lt_threshold                          2000
% 3.81/0.97  --clause_weak_htbl                      true
% 3.81/0.97  --gc_record_bc_elim                     false
% 3.81/0.97  
% 3.81/0.97  ------ Preprocessing Options
% 3.81/0.97  
% 3.81/0.97  --preprocessing_flag                    true
% 3.81/0.97  --time_out_prep_mult                    0.1
% 3.81/0.97  --splitting_mode                        input
% 3.81/0.97  --splitting_grd                         true
% 3.81/0.97  --splitting_cvd                         false
% 3.81/0.97  --splitting_cvd_svl                     false
% 3.81/0.97  --splitting_nvd                         32
% 3.81/0.97  --sub_typing                            true
% 3.81/0.97  --prep_gs_sim                           true
% 3.81/0.97  --prep_unflatten                        true
% 3.81/0.97  --prep_res_sim                          true
% 3.81/0.97  --prep_upred                            true
% 3.81/0.97  --prep_sem_filter                       exhaustive
% 3.81/0.97  --prep_sem_filter_out                   false
% 3.81/0.97  --pred_elim                             true
% 3.81/0.97  --res_sim_input                         true
% 3.81/0.97  --eq_ax_congr_red                       true
% 3.81/0.97  --pure_diseq_elim                       true
% 3.81/0.97  --brand_transform                       false
% 3.81/0.97  --non_eq_to_eq                          false
% 3.81/0.97  --prep_def_merge                        true
% 3.81/0.97  --prep_def_merge_prop_impl              false
% 3.81/0.97  --prep_def_merge_mbd                    true
% 3.81/0.97  --prep_def_merge_tr_red                 false
% 3.81/0.97  --prep_def_merge_tr_cl                  false
% 3.81/0.97  --smt_preprocessing                     true
% 3.81/0.97  --smt_ac_axioms                         fast
% 3.81/0.97  --preprocessed_out                      false
% 3.81/0.97  --preprocessed_stats                    false
% 3.81/0.97  
% 3.81/0.97  ------ Abstraction refinement Options
% 3.81/0.97  
% 3.81/0.97  --abstr_ref                             []
% 3.81/0.97  --abstr_ref_prep                        false
% 3.81/0.97  --abstr_ref_until_sat                   false
% 3.81/0.97  --abstr_ref_sig_restrict                funpre
% 3.81/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/0.97  --abstr_ref_under                       []
% 3.81/0.97  
% 3.81/0.97  ------ SAT Options
% 3.81/0.97  
% 3.81/0.97  --sat_mode                              false
% 3.81/0.97  --sat_fm_restart_options                ""
% 3.81/0.97  --sat_gr_def                            false
% 3.81/0.97  --sat_epr_types                         true
% 3.81/0.97  --sat_non_cyclic_types                  false
% 3.81/0.97  --sat_finite_models                     false
% 3.81/0.97  --sat_fm_lemmas                         false
% 3.81/0.97  --sat_fm_prep                           false
% 3.81/0.97  --sat_fm_uc_incr                        true
% 3.81/0.97  --sat_out_model                         small
% 3.81/0.97  --sat_out_clauses                       false
% 3.81/0.97  
% 3.81/0.97  ------ QBF Options
% 3.81/0.97  
% 3.81/0.97  --qbf_mode                              false
% 3.81/0.97  --qbf_elim_univ                         false
% 3.81/0.97  --qbf_dom_inst                          none
% 3.81/0.97  --qbf_dom_pre_inst                      false
% 3.81/0.97  --qbf_sk_in                             false
% 3.81/0.97  --qbf_pred_elim                         true
% 3.81/0.97  --qbf_split                             512
% 3.81/0.97  
% 3.81/0.97  ------ BMC1 Options
% 3.81/0.97  
% 3.81/0.97  --bmc1_incremental                      false
% 3.81/0.97  --bmc1_axioms                           reachable_all
% 3.81/0.97  --bmc1_min_bound                        0
% 3.81/0.97  --bmc1_max_bound                        -1
% 3.81/0.97  --bmc1_max_bound_default                -1
% 3.81/0.97  --bmc1_symbol_reachability              true
% 3.81/0.97  --bmc1_property_lemmas                  false
% 3.81/0.97  --bmc1_k_induction                      false
% 3.81/0.97  --bmc1_non_equiv_states                 false
% 3.81/0.97  --bmc1_deadlock                         false
% 3.81/0.97  --bmc1_ucm                              false
% 3.81/0.97  --bmc1_add_unsat_core                   none
% 3.81/0.97  --bmc1_unsat_core_children              false
% 3.81/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/0.97  --bmc1_out_stat                         full
% 3.81/0.97  --bmc1_ground_init                      false
% 3.81/0.97  --bmc1_pre_inst_next_state              false
% 3.81/0.97  --bmc1_pre_inst_state                   false
% 3.81/0.97  --bmc1_pre_inst_reach_state             false
% 3.81/0.97  --bmc1_out_unsat_core                   false
% 3.81/0.97  --bmc1_aig_witness_out                  false
% 3.81/0.97  --bmc1_verbose                          false
% 3.81/0.97  --bmc1_dump_clauses_tptp                false
% 3.81/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.81/0.97  --bmc1_dump_file                        -
% 3.81/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.81/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.81/0.97  --bmc1_ucm_extend_mode                  1
% 3.81/0.97  --bmc1_ucm_init_mode                    2
% 3.81/0.97  --bmc1_ucm_cone_mode                    none
% 3.81/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.81/0.97  --bmc1_ucm_relax_model                  4
% 3.81/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.81/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/0.97  --bmc1_ucm_layered_model                none
% 3.81/0.98  --bmc1_ucm_max_lemma_size               10
% 3.81/0.98  
% 3.81/0.98  ------ AIG Options
% 3.81/0.98  
% 3.81/0.98  --aig_mode                              false
% 3.81/0.98  
% 3.81/0.98  ------ Instantiation Options
% 3.81/0.98  
% 3.81/0.98  --instantiation_flag                    true
% 3.81/0.98  --inst_sos_flag                         true
% 3.81/0.98  --inst_sos_phase                        true
% 3.81/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/0.98  --inst_lit_sel_side                     num_symb
% 3.81/0.98  --inst_solver_per_active                1400
% 3.81/0.98  --inst_solver_calls_frac                1.
% 3.81/0.98  --inst_passive_queue_type               priority_queues
% 3.81/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/0.98  --inst_passive_queues_freq              [25;2]
% 3.81/0.98  --inst_dismatching                      true
% 3.81/0.98  --inst_eager_unprocessed_to_passive     true
% 3.81/0.98  --inst_prop_sim_given                   true
% 3.81/0.98  --inst_prop_sim_new                     false
% 3.81/0.98  --inst_subs_new                         false
% 3.81/0.98  --inst_eq_res_simp                      false
% 3.81/0.98  --inst_subs_given                       false
% 3.81/0.98  --inst_orphan_elimination               true
% 3.81/0.98  --inst_learning_loop_flag               true
% 3.81/0.98  --inst_learning_start                   3000
% 3.81/0.98  --inst_learning_factor                  2
% 3.81/0.98  --inst_start_prop_sim_after_learn       3
% 3.81/0.98  --inst_sel_renew                        solver
% 3.81/0.98  --inst_lit_activity_flag                true
% 3.81/0.98  --inst_restr_to_given                   false
% 3.81/0.98  --inst_activity_threshold               500
% 3.81/0.98  --inst_out_proof                        true
% 3.81/0.98  
% 3.81/0.98  ------ Resolution Options
% 3.81/0.98  
% 3.81/0.98  --resolution_flag                       true
% 3.81/0.98  --res_lit_sel                           adaptive
% 3.81/0.98  --res_lit_sel_side                      none
% 3.81/0.98  --res_ordering                          kbo
% 3.81/0.98  --res_to_prop_solver                    active
% 3.81/0.98  --res_prop_simpl_new                    false
% 3.81/0.98  --res_prop_simpl_given                  true
% 3.81/0.98  --res_passive_queue_type                priority_queues
% 3.81/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/0.98  --res_passive_queues_freq               [15;5]
% 3.81/0.98  --res_forward_subs                      full
% 3.81/0.98  --res_backward_subs                     full
% 3.81/0.98  --res_forward_subs_resolution           true
% 3.81/0.98  --res_backward_subs_resolution          true
% 3.81/0.98  --res_orphan_elimination                true
% 3.81/0.98  --res_time_limit                        2.
% 3.81/0.98  --res_out_proof                         true
% 3.81/0.98  
% 3.81/0.98  ------ Superposition Options
% 3.81/0.98  
% 3.81/0.98  --superposition_flag                    true
% 3.81/0.98  --sup_passive_queue_type                priority_queues
% 3.81/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.81/0.98  --demod_completeness_check              fast
% 3.81/0.98  --demod_use_ground                      true
% 3.81/0.98  --sup_to_prop_solver                    passive
% 3.81/0.98  --sup_prop_simpl_new                    true
% 3.81/0.98  --sup_prop_simpl_given                  true
% 3.81/0.98  --sup_fun_splitting                     true
% 3.81/0.98  --sup_smt_interval                      50000
% 3.81/0.98  
% 3.81/0.98  ------ Superposition Simplification Setup
% 3.81/0.98  
% 3.81/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.81/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.81/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.81/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.81/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.81/0.98  --sup_immed_triv                        [TrivRules]
% 3.81/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.98  --sup_immed_bw_main                     []
% 3.81/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.81/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.98  --sup_input_bw                          []
% 3.81/0.98  
% 3.81/0.98  ------ Combination Options
% 3.81/0.98  
% 3.81/0.98  --comb_res_mult                         3
% 3.81/0.98  --comb_sup_mult                         2
% 3.81/0.98  --comb_inst_mult                        10
% 3.81/0.98  
% 3.81/0.98  ------ Debug Options
% 3.81/0.98  
% 3.81/0.98  --dbg_backtrace                         false
% 3.81/0.98  --dbg_dump_prop_clauses                 false
% 3.81/0.98  --dbg_dump_prop_clauses_file            -
% 3.81/0.98  --dbg_out_stat                          false
% 3.81/0.98  ------ Parsing...
% 3.81/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/0.98  ------ Proving...
% 3.81/0.98  ------ Problem Properties 
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  clauses                                 17
% 3.81/0.98  conjectures                             3
% 3.81/0.98  EPR                                     2
% 3.81/0.98  Horn                                    17
% 3.81/0.98  unary                                   8
% 3.81/0.98  binary                                  5
% 3.81/0.98  lits                                    34
% 3.81/0.98  lits eq                                 14
% 3.81/0.98  fd_pure                                 0
% 3.81/0.98  fd_pseudo                               0
% 3.81/0.98  fd_cond                                 0
% 3.81/0.98  fd_pseudo_cond                          0
% 3.81/0.98  AC symbols                              0
% 3.81/0.98  
% 3.81/0.98  ------ Schedule dynamic 5 is on 
% 3.81/0.98  
% 3.81/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ 
% 3.81/0.98  Current options:
% 3.81/0.98  ------ 
% 3.81/0.98  
% 3.81/0.98  ------ Input Options
% 3.81/0.98  
% 3.81/0.98  --out_options                           all
% 3.81/0.98  --tptp_safe_out                         true
% 3.81/0.98  --problem_path                          ""
% 3.81/0.98  --include_path                          ""
% 3.81/0.98  --clausifier                            res/vclausify_rel
% 3.81/0.98  --clausifier_options                    ""
% 3.81/0.98  --stdin                                 false
% 3.81/0.98  --stats_out                             all
% 3.81/0.98  
% 3.81/0.98  ------ General Options
% 3.81/0.98  
% 3.81/0.98  --fof                                   false
% 3.81/0.98  --time_out_real                         305.
% 3.81/0.98  --time_out_virtual                      -1.
% 3.81/0.98  --symbol_type_check                     false
% 3.81/0.98  --clausify_out                          false
% 3.81/0.98  --sig_cnt_out                           false
% 3.81/0.98  --trig_cnt_out                          false
% 3.81/0.98  --trig_cnt_out_tolerance                1.
% 3.81/0.98  --trig_cnt_out_sk_spl                   false
% 3.81/0.98  --abstr_cl_out                          false
% 3.81/0.98  
% 3.81/0.98  ------ Global Options
% 3.81/0.98  
% 3.81/0.98  --schedule                              default
% 3.81/0.98  --add_important_lit                     false
% 3.81/0.98  --prop_solver_per_cl                    1000
% 3.81/0.98  --min_unsat_core                        false
% 3.81/0.98  --soft_assumptions                      false
% 3.81/0.98  --soft_lemma_size                       3
% 3.81/0.98  --prop_impl_unit_size                   0
% 3.81/0.98  --prop_impl_unit                        []
% 3.81/0.98  --share_sel_clauses                     true
% 3.81/0.98  --reset_solvers                         false
% 3.81/0.98  --bc_imp_inh                            [conj_cone]
% 3.81/0.98  --conj_cone_tolerance                   3.
% 3.81/0.98  --extra_neg_conj                        none
% 3.81/0.98  --large_theory_mode                     true
% 3.81/0.98  --prolific_symb_bound                   200
% 3.81/0.98  --lt_threshold                          2000
% 3.81/0.98  --clause_weak_htbl                      true
% 3.81/0.98  --gc_record_bc_elim                     false
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing Options
% 3.81/0.98  
% 3.81/0.98  --preprocessing_flag                    true
% 3.81/0.98  --time_out_prep_mult                    0.1
% 3.81/0.98  --splitting_mode                        input
% 3.81/0.98  --splitting_grd                         true
% 3.81/0.98  --splitting_cvd                         false
% 3.81/0.98  --splitting_cvd_svl                     false
% 3.81/0.98  --splitting_nvd                         32
% 3.81/0.98  --sub_typing                            true
% 3.81/0.98  --prep_gs_sim                           true
% 3.81/0.98  --prep_unflatten                        true
% 3.81/0.98  --prep_res_sim                          true
% 3.81/0.98  --prep_upred                            true
% 3.81/0.98  --prep_sem_filter                       exhaustive
% 3.81/0.98  --prep_sem_filter_out                   false
% 3.81/0.98  --pred_elim                             true
% 3.81/0.98  --res_sim_input                         true
% 3.81/0.98  --eq_ax_congr_red                       true
% 3.81/0.98  --pure_diseq_elim                       true
% 3.81/0.98  --brand_transform                       false
% 3.81/0.98  --non_eq_to_eq                          false
% 3.81/0.98  --prep_def_merge                        true
% 3.81/0.98  --prep_def_merge_prop_impl              false
% 3.81/0.98  --prep_def_merge_mbd                    true
% 3.81/0.98  --prep_def_merge_tr_red                 false
% 3.81/0.98  --prep_def_merge_tr_cl                  false
% 3.81/0.98  --smt_preprocessing                     true
% 3.81/0.98  --smt_ac_axioms                         fast
% 3.81/0.98  --preprocessed_out                      false
% 3.81/0.98  --preprocessed_stats                    false
% 3.81/0.98  
% 3.81/0.98  ------ Abstraction refinement Options
% 3.81/0.98  
% 3.81/0.98  --abstr_ref                             []
% 3.81/0.98  --abstr_ref_prep                        false
% 3.81/0.98  --abstr_ref_until_sat                   false
% 3.81/0.98  --abstr_ref_sig_restrict                funpre
% 3.81/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/0.98  --abstr_ref_under                       []
% 3.81/0.98  
% 3.81/0.98  ------ SAT Options
% 3.81/0.98  
% 3.81/0.98  --sat_mode                              false
% 3.81/0.98  --sat_fm_restart_options                ""
% 3.81/0.98  --sat_gr_def                            false
% 3.81/0.98  --sat_epr_types                         true
% 3.81/0.98  --sat_non_cyclic_types                  false
% 3.81/0.98  --sat_finite_models                     false
% 3.81/0.98  --sat_fm_lemmas                         false
% 3.81/0.98  --sat_fm_prep                           false
% 3.81/0.98  --sat_fm_uc_incr                        true
% 3.81/0.98  --sat_out_model                         small
% 3.81/0.98  --sat_out_clauses                       false
% 3.81/0.98  
% 3.81/0.98  ------ QBF Options
% 3.81/0.98  
% 3.81/0.98  --qbf_mode                              false
% 3.81/0.98  --qbf_elim_univ                         false
% 3.81/0.98  --qbf_dom_inst                          none
% 3.81/0.98  --qbf_dom_pre_inst                      false
% 3.81/0.98  --qbf_sk_in                             false
% 3.81/0.98  --qbf_pred_elim                         true
% 3.81/0.98  --qbf_split                             512
% 3.81/0.98  
% 3.81/0.98  ------ BMC1 Options
% 3.81/0.98  
% 3.81/0.98  --bmc1_incremental                      false
% 3.81/0.98  --bmc1_axioms                           reachable_all
% 3.81/0.98  --bmc1_min_bound                        0
% 3.81/0.98  --bmc1_max_bound                        -1
% 3.81/0.98  --bmc1_max_bound_default                -1
% 3.81/0.98  --bmc1_symbol_reachability              true
% 3.81/0.98  --bmc1_property_lemmas                  false
% 3.81/0.98  --bmc1_k_induction                      false
% 3.81/0.98  --bmc1_non_equiv_states                 false
% 3.81/0.98  --bmc1_deadlock                         false
% 3.81/0.98  --bmc1_ucm                              false
% 3.81/0.98  --bmc1_add_unsat_core                   none
% 3.81/0.98  --bmc1_unsat_core_children              false
% 3.81/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/0.98  --bmc1_out_stat                         full
% 3.81/0.98  --bmc1_ground_init                      false
% 3.81/0.98  --bmc1_pre_inst_next_state              false
% 3.81/0.98  --bmc1_pre_inst_state                   false
% 3.81/0.98  --bmc1_pre_inst_reach_state             false
% 3.81/0.98  --bmc1_out_unsat_core                   false
% 3.81/0.98  --bmc1_aig_witness_out                  false
% 3.81/0.98  --bmc1_verbose                          false
% 3.81/0.98  --bmc1_dump_clauses_tptp                false
% 3.81/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.81/0.98  --bmc1_dump_file                        -
% 3.81/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.81/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.81/0.98  --bmc1_ucm_extend_mode                  1
% 3.81/0.98  --bmc1_ucm_init_mode                    2
% 3.81/0.98  --bmc1_ucm_cone_mode                    none
% 3.81/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.81/0.98  --bmc1_ucm_relax_model                  4
% 3.81/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.81/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/0.98  --bmc1_ucm_layered_model                none
% 3.81/0.98  --bmc1_ucm_max_lemma_size               10
% 3.81/0.98  
% 3.81/0.98  ------ AIG Options
% 3.81/0.98  
% 3.81/0.98  --aig_mode                              false
% 3.81/0.98  
% 3.81/0.98  ------ Instantiation Options
% 3.81/0.98  
% 3.81/0.98  --instantiation_flag                    true
% 3.81/0.98  --inst_sos_flag                         true
% 3.81/0.98  --inst_sos_phase                        true
% 3.81/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/0.98  --inst_lit_sel_side                     none
% 3.81/0.98  --inst_solver_per_active                1400
% 3.81/0.98  --inst_solver_calls_frac                1.
% 3.81/0.98  --inst_passive_queue_type               priority_queues
% 3.81/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/0.98  --inst_passive_queues_freq              [25;2]
% 3.81/0.98  --inst_dismatching                      true
% 3.81/0.98  --inst_eager_unprocessed_to_passive     true
% 3.81/0.98  --inst_prop_sim_given                   true
% 3.81/0.98  --inst_prop_sim_new                     false
% 3.81/0.98  --inst_subs_new                         false
% 3.81/0.98  --inst_eq_res_simp                      false
% 3.81/0.98  --inst_subs_given                       false
% 3.81/0.98  --inst_orphan_elimination               true
% 3.81/0.98  --inst_learning_loop_flag               true
% 3.81/0.98  --inst_learning_start                   3000
% 3.81/0.98  --inst_learning_factor                  2
% 3.81/0.98  --inst_start_prop_sim_after_learn       3
% 3.81/0.98  --inst_sel_renew                        solver
% 3.81/0.98  --inst_lit_activity_flag                true
% 3.81/0.98  --inst_restr_to_given                   false
% 3.81/0.98  --inst_activity_threshold               500
% 3.81/0.98  --inst_out_proof                        true
% 3.81/0.98  
% 3.81/0.98  ------ Resolution Options
% 3.81/0.98  
% 3.81/0.98  --resolution_flag                       false
% 3.81/0.98  --res_lit_sel                           adaptive
% 3.81/0.98  --res_lit_sel_side                      none
% 3.81/0.98  --res_ordering                          kbo
% 3.81/0.98  --res_to_prop_solver                    active
% 3.81/0.98  --res_prop_simpl_new                    false
% 3.81/0.98  --res_prop_simpl_given                  true
% 3.81/0.98  --res_passive_queue_type                priority_queues
% 3.81/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/0.98  --res_passive_queues_freq               [15;5]
% 3.81/0.98  --res_forward_subs                      full
% 3.81/0.98  --res_backward_subs                     full
% 3.81/0.98  --res_forward_subs_resolution           true
% 3.81/0.98  --res_backward_subs_resolution          true
% 3.81/0.98  --res_orphan_elimination                true
% 3.81/0.98  --res_time_limit                        2.
% 3.81/0.98  --res_out_proof                         true
% 3.81/0.98  
% 3.81/0.98  ------ Superposition Options
% 3.81/0.98  
% 3.81/0.98  --superposition_flag                    true
% 3.81/0.98  --sup_passive_queue_type                priority_queues
% 3.81/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.81/0.98  --demod_completeness_check              fast
% 3.81/0.98  --demod_use_ground                      true
% 3.81/0.98  --sup_to_prop_solver                    passive
% 3.81/0.98  --sup_prop_simpl_new                    true
% 3.81/0.98  --sup_prop_simpl_given                  true
% 3.81/0.98  --sup_fun_splitting                     true
% 3.81/0.98  --sup_smt_interval                      50000
% 3.81/0.98  
% 3.81/0.98  ------ Superposition Simplification Setup
% 3.81/0.98  
% 3.81/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.81/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.81/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.81/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.81/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.81/0.98  --sup_immed_triv                        [TrivRules]
% 3.81/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.98  --sup_immed_bw_main                     []
% 3.81/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.81/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.98  --sup_input_bw                          []
% 3.81/0.98  
% 3.81/0.98  ------ Combination Options
% 3.81/0.98  
% 3.81/0.98  --comb_res_mult                         3
% 3.81/0.98  --comb_sup_mult                         2
% 3.81/0.98  --comb_inst_mult                        10
% 3.81/0.98  
% 3.81/0.98  ------ Debug Options
% 3.81/0.98  
% 3.81/0.98  --dbg_backtrace                         false
% 3.81/0.98  --dbg_dump_prop_clauses                 false
% 3.81/0.98  --dbg_dump_prop_clauses_file            -
% 3.81/0.98  --dbg_out_stat                          false
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ Proving...
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  % SZS status Theorem for theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  fof(f11,conjecture,(
% 3.81/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f12,negated_conjecture,(
% 3.81/0.98    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 3.81/0.98    inference(negated_conjecture,[],[f11])).
% 3.81/0.98  
% 3.81/0.98  fof(f25,plain,(
% 3.81/0.98    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) != k2_relat_1(X0)) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f12])).
% 3.81/0.98  
% 3.81/0.98  fof(f26,plain,(
% 3.81/0.98    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) != k2_relat_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.81/0.98    inference(flattening,[],[f25])).
% 3.81/0.98  
% 3.81/0.98  fof(f27,plain,(
% 3.81/0.98    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) != k2_relat_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f28,plain,(
% 3.81/0.98    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 3.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.81/0.98  
% 3.81/0.98  fof(f43,plain,(
% 3.81/0.98    v1_relat_1(sK0)),
% 3.81/0.98    inference(cnf_transformation,[],[f28])).
% 3.81/0.98  
% 3.81/0.98  fof(f44,plain,(
% 3.81/0.98    v1_funct_1(sK0)),
% 3.81/0.98    inference(cnf_transformation,[],[f28])).
% 3.81/0.98  
% 3.81/0.98  fof(f8,axiom,(
% 3.81/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f21,plain,(
% 3.81/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f8])).
% 3.81/0.98  
% 3.81/0.98  fof(f22,plain,(
% 3.81/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.81/0.98    inference(flattening,[],[f21])).
% 3.81/0.98  
% 3.81/0.98  fof(f37,plain,(
% 3.81/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f22])).
% 3.81/0.98  
% 3.81/0.98  fof(f9,axiom,(
% 3.81/0.98    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f39,plain,(
% 3.81/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.81/0.98    inference(cnf_transformation,[],[f9])).
% 3.81/0.98  
% 3.81/0.98  fof(f5,axiom,(
% 3.81/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f33,plain,(
% 3.81/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.81/0.98    inference(cnf_transformation,[],[f5])).
% 3.81/0.98  
% 3.81/0.98  fof(f3,axiom,(
% 3.81/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f15,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.81/0.98    inference(ennf_transformation,[],[f3])).
% 3.81/0.98  
% 3.81/0.98  fof(f16,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.81/0.98    inference(flattening,[],[f15])).
% 3.81/0.98  
% 3.81/0.98  fof(f31,plain,(
% 3.81/0.98    ( ! [X2,X0,X1] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f16])).
% 3.81/0.98  
% 3.81/0.98  fof(f10,axiom,(
% 3.81/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f23,plain,(
% 3.81/0.98    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f10])).
% 3.81/0.98  
% 3.81/0.98  fof(f24,plain,(
% 3.81/0.98    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.81/0.98    inference(flattening,[],[f23])).
% 3.81/0.98  
% 3.81/0.98  fof(f41,plain,(
% 3.81/0.98    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f24])).
% 3.81/0.98  
% 3.81/0.98  fof(f45,plain,(
% 3.81/0.98    v2_funct_1(sK0)),
% 3.81/0.98    inference(cnf_transformation,[],[f28])).
% 3.81/0.98  
% 3.81/0.98  fof(f6,axiom,(
% 3.81/0.98    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f19,plain,(
% 3.81/0.98    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.81/0.98    inference(ennf_transformation,[],[f6])).
% 3.81/0.98  
% 3.81/0.98  fof(f35,plain,(
% 3.81/0.98    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f19])).
% 3.81/0.98  
% 3.81/0.98  fof(f42,plain,(
% 3.81/0.98    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f24])).
% 3.81/0.98  
% 3.81/0.98  fof(f34,plain,(
% 3.81/0.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.81/0.98    inference(cnf_transformation,[],[f5])).
% 3.81/0.98  
% 3.81/0.98  fof(f4,axiom,(
% 3.81/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f17,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.81/0.98    inference(ennf_transformation,[],[f4])).
% 3.81/0.98  
% 3.81/0.98  fof(f18,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.81/0.98    inference(flattening,[],[f17])).
% 3.81/0.98  
% 3.81/0.98  fof(f32,plain,(
% 3.81/0.98    ( ! [X2,X0,X1] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f18])).
% 3.81/0.98  
% 3.81/0.98  fof(f7,axiom,(
% 3.81/0.98    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f20,plain,(
% 3.81/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.81/0.98    inference(ennf_transformation,[],[f7])).
% 3.81/0.98  
% 3.81/0.98  fof(f36,plain,(
% 3.81/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f20])).
% 3.81/0.98  
% 3.81/0.98  fof(f2,axiom,(
% 3.81/0.98    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f14,plain,(
% 3.81/0.98    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.81/0.98    inference(ennf_transformation,[],[f2])).
% 3.81/0.98  
% 3.81/0.98  fof(f30,plain,(
% 3.81/0.98    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f14])).
% 3.81/0.98  
% 3.81/0.98  fof(f1,axiom,(
% 3.81/0.98    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f13,plain,(
% 3.81/0.98    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.81/0.98    inference(ennf_transformation,[],[f1])).
% 3.81/0.98  
% 3.81/0.98  fof(f29,plain,(
% 3.81/0.98    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f13])).
% 3.81/0.98  
% 3.81/0.98  fof(f46,plain,(
% 3.81/0.98    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)),
% 3.81/0.98    inference(cnf_transformation,[],[f28])).
% 3.81/0.98  
% 3.81/0.98  cnf(c_17,negated_conjecture,
% 3.81/0.98      ( v1_relat_1(sK0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_496,plain,
% 3.81/0.98      ( v1_relat_1(sK0) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_16,negated_conjecture,
% 3.81/0.98      ( v1_funct_1(sK0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_497,plain,
% 3.81/0.98      ( v1_funct_1(sK0) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_9,plain,
% 3.81/0.98      ( ~ v1_funct_1(X0)
% 3.81/0.98      | ~ v1_relat_1(X0)
% 3.81/0.98      | v1_relat_1(k2_funct_1(X0)) ),
% 3.81/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_500,plain,
% 3.81/0.98      ( v1_funct_1(X0) != iProver_top
% 3.81/0.98      | v1_relat_1(X0) != iProver_top
% 3.81/0.98      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11,plain,
% 3.81/0.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.81/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_498,plain,
% 3.81/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5,plain,
% 3.81/0.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.81/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2,plain,
% 3.81/0.98      ( ~ v1_relat_1(X0)
% 3.81/0.98      | ~ v1_relat_1(X1)
% 3.81/0.98      | ~ v1_relat_1(X2)
% 3.81/0.98      | k1_relat_1(X1) != k1_relat_1(X0)
% 3.81/0.98      | k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(k5_relat_1(X2,X0)) ),
% 3.81/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_505,plain,
% 3.81/0.98      ( k1_relat_1(X0) != k1_relat_1(X1)
% 3.81/0.98      | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
% 3.81/0.98      | v1_relat_1(X1) != iProver_top
% 3.81/0.98      | v1_relat_1(X0) != iProver_top
% 3.81/0.98      | v1_relat_1(X2) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1400,plain,
% 3.81/0.98      ( k1_relat_1(X0) != X1
% 3.81/0.98      | k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X2,X0))
% 3.81/0.98      | v1_relat_1(X0) != iProver_top
% 3.81/0.98      | v1_relat_1(X2) != iProver_top
% 3.81/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_5,c_505]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2007,plain,
% 3.81/0.98      ( k1_relat_1(k5_relat_1(X0,k6_relat_1(k1_relat_1(X1)))) = k1_relat_1(k5_relat_1(X0,X1))
% 3.81/0.98      | v1_relat_1(X0) != iProver_top
% 3.81/0.98      | v1_relat_1(X1) != iProver_top
% 3.81/0.98      | v1_relat_1(k6_relat_1(k1_relat_1(X1))) != iProver_top ),
% 3.81/0.98      inference(equality_resolution,[status(thm)],[c_1400]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_6144,plain,
% 3.81/0.98      ( k1_relat_1(k5_relat_1(X0,k6_relat_1(k1_relat_1(X1)))) = k1_relat_1(k5_relat_1(X0,X1))
% 3.81/0.98      | v1_relat_1(X0) != iProver_top
% 3.81/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_498,c_2007]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_6153,plain,
% 3.81/0.98      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),k6_relat_1(k1_relat_1(X1)))) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X1))
% 3.81/0.98      | v1_funct_1(X0) != iProver_top
% 3.81/0.98      | v1_relat_1(X0) != iProver_top
% 3.81/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_500,c_6144]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_12951,plain,
% 3.81/0.98      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0)))) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
% 3.81/0.98      | v1_relat_1(X0) != iProver_top
% 3.81/0.98      | v1_relat_1(sK0) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_497,c_6153]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_18,plain,
% 3.81/0.98      ( v1_relat_1(sK0) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_13156,plain,
% 3.81/0.98      ( v1_relat_1(X0) != iProver_top
% 3.81/0.98      | k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0)))) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_12951,c_18]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_13157,plain,
% 3.81/0.98      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(X0)))) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
% 3.81/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.81/0.98      inference(renaming,[status(thm)],[c_13156]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_13162,plain,
% 3.81/0.98      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_496,c_13157]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_13,plain,
% 3.81/0.98      ( ~ v2_funct_1(X0)
% 3.81/0.98      | ~ v1_funct_1(X0)
% 3.81/0.98      | ~ v1_relat_1(X0)
% 3.81/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_15,negated_conjecture,
% 3.81/0.98      ( v2_funct_1(sK0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_180,plain,
% 3.81/0.98      ( ~ v1_funct_1(X0)
% 3.81/0.98      | ~ v1_relat_1(X0)
% 3.81/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.81/0.98      | sK0 != X0 ),
% 3.81/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_15]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_181,plain,
% 3.81/0.98      ( ~ v1_funct_1(sK0)
% 3.81/0.98      | ~ v1_relat_1(sK0)
% 3.81/0.98      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 3.81/0.98      inference(unflattening,[status(thm)],[c_180]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_22,plain,
% 3.81/0.98      ( ~ v2_funct_1(sK0)
% 3.81/0.98      | ~ v1_funct_1(sK0)
% 3.81/0.98      | ~ v1_relat_1(sK0)
% 3.81/0.98      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_183,plain,
% 3.81/0.98      ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_181,c_17,c_16,c_15,c_22]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_6,plain,
% 3.81/0.98      ( ~ v1_relat_1(X0)
% 3.81/0.98      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 3.81/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_503,plain,
% 3.81/0.98      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 3.81/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1198,plain,
% 3.81/0.98      ( k5_relat_1(k2_funct_1(X0),k6_relat_1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
% 3.81/0.98      | v1_funct_1(X0) != iProver_top
% 3.81/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_500,c_503]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2907,plain,
% 3.81/0.98      ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) = k2_funct_1(sK0)
% 3.81/0.98      | v1_relat_1(sK0) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_497,c_1198]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_12,plain,
% 3.81/0.98      ( ~ v2_funct_1(X0)
% 3.81/0.98      | ~ v1_funct_1(X0)
% 3.81/0.98      | ~ v1_relat_1(X0)
% 3.81/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_188,plain,
% 3.81/0.98      ( ~ v1_funct_1(X0)
% 3.81/0.98      | ~ v1_relat_1(X0)
% 3.81/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.81/0.98      | sK0 != X0 ),
% 3.81/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_189,plain,
% 3.81/0.98      ( ~ v1_funct_1(sK0)
% 3.81/0.98      | ~ v1_relat_1(sK0)
% 3.81/0.98      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 3.81/0.98      inference(unflattening,[status(thm)],[c_188]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_25,plain,
% 3.81/0.98      ( ~ v2_funct_1(sK0)
% 3.81/0.98      | ~ v1_funct_1(sK0)
% 3.81/0.98      | ~ v1_relat_1(sK0)
% 3.81/0.98      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_191,plain,
% 3.81/0.98      ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_189,c_17,c_16,c_15,c_25]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2908,plain,
% 3.81/0.98      ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k2_funct_1(sK0)
% 3.81/0.98      | v1_relat_1(sK0) != iProver_top ),
% 3.81/0.98      inference(light_normalisation,[status(thm)],[c_2907,c_191]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_3088,plain,
% 3.81/0.98      ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k2_funct_1(sK0) ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_2908,c_18]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_13163,plain,
% 3.81/0.98      ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0) ),
% 3.81/0.98      inference(light_normalisation,[status(thm)],[c_13162,c_183,c_3088]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4,plain,
% 3.81/0.98      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.81/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_3,plain,
% 3.81/0.98      ( ~ v1_relat_1(X0)
% 3.81/0.98      | ~ v1_relat_1(X1)
% 3.81/0.98      | ~ v1_relat_1(X2)
% 3.81/0.98      | k2_relat_1(X1) != k2_relat_1(X0)
% 3.81/0.98      | k2_relat_1(k5_relat_1(X1,X2)) = k2_relat_1(k5_relat_1(X0,X2)) ),
% 3.81/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_504,plain,
% 3.81/0.98      ( k2_relat_1(X0) != k2_relat_1(X1)
% 3.81/0.98      | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
% 3.81/0.98      | v1_relat_1(X1) != iProver_top
% 3.81/0.98      | v1_relat_1(X0) != iProver_top
% 3.81/0.98      | v1_relat_1(X2) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1281,plain,
% 3.81/0.98      ( k2_relat_1(X0) != X1
% 3.81/0.98      | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
% 3.81/0.98      | v1_relat_1(X0) != iProver_top
% 3.81/0.98      | v1_relat_1(X2) != iProver_top
% 3.81/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_4,c_504]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1411,plain,
% 3.81/0.98      ( k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
% 3.81/0.98      | k1_relat_1(sK0) != X0
% 3.81/0.98      | v1_relat_1(X1) != iProver_top
% 3.81/0.98      | v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 3.81/0.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_191,c_1281]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_27,plain,
% 3.81/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1282,plain,
% 3.81/0.98      ( k2_relat_1(X0) != k1_relat_1(sK0)
% 3.81/0.98      | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1)) = k2_relat_1(k5_relat_1(X0,X1))
% 3.81/0.98      | v1_relat_1(X0) != iProver_top
% 3.81/0.98      | v1_relat_1(X1) != iProver_top
% 3.81/0.98      | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_191,c_504]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_19,plain,
% 3.81/0.98      ( v1_funct_1(sK0) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_33,plain,
% 3.81/0.98      ( v1_funct_1(X0) != iProver_top
% 3.81/0.98      | v1_relat_1(X0) != iProver_top
% 3.81/0.98      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_35,plain,
% 3.81/0.98      ( v1_funct_1(sK0) != iProver_top
% 3.81/0.98      | v1_relat_1(k2_funct_1(sK0)) = iProver_top
% 3.81/0.98      | v1_relat_1(sK0) != iProver_top ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_33]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1503,plain,
% 3.81/0.98      ( v1_relat_1(X1) != iProver_top
% 3.81/0.98      | v1_relat_1(X0) != iProver_top
% 3.81/0.98      | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1)) = k2_relat_1(k5_relat_1(X0,X1))
% 3.81/0.98      | k2_relat_1(X0) != k1_relat_1(sK0) ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_1282,c_18,c_19,c_35]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1504,plain,
% 3.81/0.98      ( k2_relat_1(X0) != k1_relat_1(sK0)
% 3.81/0.98      | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1)) = k2_relat_1(k5_relat_1(X0,X1))
% 3.81/0.98      | v1_relat_1(X0) != iProver_top
% 3.81/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.81/0.98      inference(renaming,[status(thm)],[c_1503]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1509,plain,
% 3.81/0.98      ( k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
% 3.81/0.98      | k1_relat_1(sK0) != X0
% 3.81/0.98      | v1_relat_1(X1) != iProver_top
% 3.81/0.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_4,c_1504]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1626,plain,
% 3.81/0.98      ( k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
% 3.81/0.98      | k1_relat_1(sK0) != X0
% 3.81/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_1411,c_27,c_1509]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1632,plain,
% 3.81/0.98      ( k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
% 3.81/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.81/0.98      inference(equality_resolution,[status(thm)],[c_1626]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1639,plain,
% 3.81/0.98      ( k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_496,c_1632]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_7,plain,
% 3.81/0.98      ( ~ v1_relat_1(X0)
% 3.81/0.98      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.81/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_502,plain,
% 3.81/0.98      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 3.81/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_961,plain,
% 3.81/0.98      ( k5_relat_1(k6_relat_1(X0),sK0) = k7_relat_1(sK0,X0) ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_496,c_502]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1,plain,
% 3.81/0.98      ( ~ v1_relat_1(X0)
% 3.81/0.98      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.81/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_506,plain,
% 3.81/0.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.81/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1108,plain,
% 3.81/0.98      ( k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_496,c_506]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1640,plain,
% 3.81/0.98      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
% 3.81/0.98      inference(demodulation,[status(thm)],[c_1639,c_961,c_1108]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_0,plain,
% 3.81/0.98      ( ~ v1_relat_1(X0)
% 3.81/0.98      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f29]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_507,plain,
% 3.81/0.98      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.81/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_840,plain,
% 3.81/0.98      ( k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(sK0) ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_496,c_507]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1641,plain,
% 3.81/0.98      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0) ),
% 3.81/0.98      inference(light_normalisation,[status(thm)],[c_1640,c_840]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_287,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_523,plain,
% 3.81/0.98      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != X0
% 3.81/0.98      | k2_relat_1(sK0) != X0
% 3.81/0.98      | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_287]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_527,plain,
% 3.81/0.98      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(X0)
% 3.81/0.98      | k2_relat_1(sK0) != k2_relat_1(X0)
% 3.81/0.98      | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_523]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_528,plain,
% 3.81/0.98      ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0)
% 3.81/0.98      | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
% 3.81/0.98      | k2_relat_1(sK0) != k2_relat_1(sK0) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_527]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_286,plain,( X0 = X0 ),theory(equality) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_305,plain,
% 3.81/0.98      ( sK0 = sK0 ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_286]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_290,plain,
% 3.81/0.98      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 3.81/0.98      theory(equality) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_298,plain,
% 3.81/0.98      ( k2_relat_1(sK0) = k2_relat_1(sK0) | sK0 != sK0 ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_290]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_14,negated_conjecture,
% 3.81/0.98      ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
% 3.81/0.98      | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) != k2_relat_1(sK0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(contradiction,plain,
% 3.81/0.98      ( $false ),
% 3.81/0.98      inference(minisat,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_13163,c_1641,c_528,c_305,c_298,c_14]) ).
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  ------                               Statistics
% 3.81/0.98  
% 3.81/0.98  ------ General
% 3.81/0.98  
% 3.81/0.98  abstr_ref_over_cycles:                  0
% 3.81/0.98  abstr_ref_under_cycles:                 0
% 3.81/0.98  gc_basic_clause_elim:                   0
% 3.81/0.98  forced_gc_time:                         0
% 3.81/0.98  parsing_time:                           0.008
% 3.81/0.98  unif_index_cands_time:                  0.
% 3.81/0.98  unif_index_add_time:                    0.
% 3.81/0.98  orderings_time:                         0.
% 3.81/0.98  out_proof_time:                         0.008
% 3.81/0.98  total_time:                             0.412
% 3.81/0.98  num_of_symbols:                         42
% 3.81/0.98  num_of_terms:                           10240
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing
% 3.81/0.98  
% 3.81/0.98  num_of_splits:                          0
% 3.81/0.98  num_of_split_atoms:                     0
% 3.81/0.98  num_of_reused_defs:                     0
% 3.81/0.98  num_eq_ax_congr_red:                    9
% 3.81/0.98  num_of_sem_filtered_clauses:            1
% 3.81/0.98  num_of_subtypes:                        0
% 3.81/0.98  monotx_restored_types:                  0
% 3.81/0.98  sat_num_of_epr_types:                   0
% 3.81/0.98  sat_num_of_non_cyclic_types:            0
% 3.81/0.98  sat_guarded_non_collapsed_types:        0
% 3.81/0.98  num_pure_diseq_elim:                    0
% 3.81/0.98  simp_replaced_by:                       0
% 3.81/0.98  res_preprocessed:                       90
% 3.81/0.98  prep_upred:                             0
% 3.81/0.98  prep_unflattend:                        2
% 3.81/0.98  smt_new_axioms:                         0
% 3.81/0.98  pred_elim_cands:                        2
% 3.81/0.98  pred_elim:                              1
% 3.81/0.98  pred_elim_cl:                           1
% 3.81/0.98  pred_elim_cycles:                       3
% 3.81/0.98  merged_defs:                            0
% 3.81/0.98  merged_defs_ncl:                        0
% 3.81/0.98  bin_hyper_res:                          0
% 3.81/0.98  prep_cycles:                            4
% 3.81/0.98  pred_elim_time:                         0.001
% 3.81/0.98  splitting_time:                         0.
% 3.81/0.98  sem_filter_time:                        0.
% 3.81/0.98  monotx_time:                            0.
% 3.81/0.98  subtype_inf_time:                       0.
% 3.81/0.98  
% 3.81/0.98  ------ Problem properties
% 3.81/0.98  
% 3.81/0.98  clauses:                                17
% 3.81/0.98  conjectures:                            3
% 3.81/0.98  epr:                                    2
% 3.81/0.98  horn:                                   17
% 3.81/0.98  ground:                                 5
% 3.81/0.98  unary:                                  8
% 3.81/0.98  binary:                                 5
% 3.81/0.98  lits:                                   34
% 3.81/0.98  lits_eq:                                14
% 3.81/0.98  fd_pure:                                0
% 3.81/0.98  fd_pseudo:                              0
% 3.81/0.98  fd_cond:                                0
% 3.81/0.98  fd_pseudo_cond:                         0
% 3.81/0.98  ac_symbols:                             0
% 3.81/0.98  
% 3.81/0.98  ------ Propositional Solver
% 3.81/0.98  
% 3.81/0.98  prop_solver_calls:                      34
% 3.81/0.98  prop_fast_solver_calls:                 934
% 3.81/0.98  smt_solver_calls:                       0
% 3.81/0.98  smt_fast_solver_calls:                  0
% 3.81/0.98  prop_num_of_clauses:                    4184
% 3.81/0.98  prop_preprocess_simplified:             10683
% 3.81/0.98  prop_fo_subsumed:                       38
% 3.81/0.98  prop_solver_time:                       0.
% 3.81/0.98  smt_solver_time:                        0.
% 3.81/0.98  smt_fast_solver_time:                   0.
% 3.81/0.98  prop_fast_solver_time:                  0.
% 3.81/0.98  prop_unsat_core_time:                   0.
% 3.81/0.98  
% 3.81/0.98  ------ QBF
% 3.81/0.98  
% 3.81/0.98  qbf_q_res:                              0
% 3.81/0.98  qbf_num_tautologies:                    0
% 3.81/0.98  qbf_prep_cycles:                        0
% 3.81/0.98  
% 3.81/0.98  ------ BMC1
% 3.81/0.98  
% 3.81/0.98  bmc1_current_bound:                     -1
% 3.81/0.98  bmc1_last_solved_bound:                 -1
% 3.81/0.98  bmc1_unsat_core_size:                   -1
% 3.81/0.98  bmc1_unsat_core_parents_size:           -1
% 3.81/0.98  bmc1_merge_next_fun:                    0
% 3.81/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.81/0.98  
% 3.81/0.98  ------ Instantiation
% 3.81/0.98  
% 3.81/0.98  inst_num_of_clauses:                    2206
% 3.81/0.98  inst_num_in_passive:                    1376
% 3.81/0.98  inst_num_in_active:                     723
% 3.81/0.98  inst_num_in_unprocessed:                108
% 3.81/0.98  inst_num_of_loops:                      760
% 3.81/0.98  inst_num_of_learning_restarts:          0
% 3.81/0.98  inst_num_moves_active_passive:          33
% 3.81/0.98  inst_lit_activity:                      0
% 3.81/0.98  inst_lit_activity_moves:                0
% 3.81/0.98  inst_num_tautologies:                   0
% 3.81/0.98  inst_num_prop_implied:                  0
% 3.81/0.98  inst_num_existing_simplified:           0
% 3.81/0.98  inst_num_eq_res_simplified:             0
% 3.81/0.98  inst_num_child_elim:                    0
% 3.81/0.98  inst_num_of_dismatching_blockings:      3233
% 3.81/0.98  inst_num_of_non_proper_insts:           3378
% 3.81/0.98  inst_num_of_duplicates:                 0
% 3.81/0.98  inst_inst_num_from_inst_to_res:         0
% 3.81/0.98  inst_dismatching_checking_time:         0.
% 3.81/0.98  
% 3.81/0.98  ------ Resolution
% 3.81/0.98  
% 3.81/0.98  res_num_of_clauses:                     0
% 3.81/0.98  res_num_in_passive:                     0
% 3.81/0.98  res_num_in_active:                      0
% 3.81/0.98  res_num_of_loops:                       94
% 3.81/0.98  res_forward_subset_subsumed:            348
% 3.81/0.98  res_backward_subset_subsumed:           2
% 3.81/0.98  res_forward_subsumed:                   0
% 3.81/0.98  res_backward_subsumed:                  0
% 3.81/0.98  res_forward_subsumption_resolution:     0
% 3.81/0.98  res_backward_subsumption_resolution:    0
% 3.81/0.98  res_clause_to_clause_subsumption:       800
% 3.81/0.98  res_orphan_elimination:                 0
% 3.81/0.98  res_tautology_del:                      536
% 3.81/0.98  res_num_eq_res_simplified:              0
% 3.81/0.98  res_num_sel_changes:                    0
% 3.81/0.98  res_moves_from_active_to_pass:          0
% 3.81/0.98  
% 3.81/0.98  ------ Superposition
% 3.81/0.98  
% 3.81/0.98  sup_time_total:                         0.
% 3.81/0.98  sup_time_generating:                    0.
% 3.81/0.98  sup_time_sim_full:                      0.
% 3.81/0.98  sup_time_sim_immed:                     0.
% 3.81/0.98  
% 3.81/0.98  sup_num_of_clauses:                     305
% 3.81/0.98  sup_num_in_active:                      145
% 3.81/0.98  sup_num_in_passive:                     160
% 3.81/0.98  sup_num_of_loops:                       150
% 3.81/0.98  sup_fw_superposition:                   206
% 3.81/0.98  sup_bw_superposition:                   153
% 3.81/0.98  sup_immediate_simplified:               56
% 3.81/0.98  sup_given_eliminated:                   0
% 3.81/0.98  comparisons_done:                       0
% 3.81/0.98  comparisons_avoided:                    0
% 3.81/0.98  
% 3.81/0.98  ------ Simplifications
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  sim_fw_subset_subsumed:                 6
% 3.81/0.98  sim_bw_subset_subsumed:                 11
% 3.81/0.98  sim_fw_subsumed:                        4
% 3.81/0.98  sim_bw_subsumed:                        0
% 3.81/0.98  sim_fw_subsumption_res:                 0
% 3.81/0.98  sim_bw_subsumption_res:                 0
% 3.81/0.98  sim_tautology_del:                      0
% 3.81/0.98  sim_eq_tautology_del:                   22
% 3.81/0.98  sim_eq_res_simp:                        1
% 3.81/0.98  sim_fw_demodulated:                     21
% 3.81/0.98  sim_bw_demodulated:                     1
% 3.81/0.98  sim_light_normalised:                   27
% 3.81/0.98  sim_joinable_taut:                      0
% 3.81/0.98  sim_joinable_simp:                      0
% 3.81/0.98  sim_ac_normalised:                      0
% 3.81/0.98  sim_smt_subsumption:                    0
% 3.81/0.98  
%------------------------------------------------------------------------------
