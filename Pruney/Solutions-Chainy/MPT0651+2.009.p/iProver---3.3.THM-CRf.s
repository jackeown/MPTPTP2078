%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:27 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 394 expanded)
%              Number of clauses        :   78 ( 125 expanded)
%              Number of leaves         :   14 (  77 expanded)
%              Depth                    :   20
%              Number of atoms          :  364 (1528 expanded)
%              Number of equality atoms :  205 ( 628 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f31,plain,
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

fof(f32,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f31])).

fof(f51,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f48,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_655,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_657,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_654,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k2_relat_1(X1) != k2_relat_1(X0)
    | k2_relat_1(k5_relat_1(X1,X2)) = k2_relat_1(k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_661,plain,
    ( k2_relat_1(X0) != k2_relat_1(X1)
    | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1925,plain,
    ( k2_relat_1(X0) != X1
    | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_661])).

cnf(c_14,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_656,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2702,plain,
    ( k2_relat_1(X0) != X1
    | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1925,c_656])).

cnf(c_2710,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(X0)),X1)) = k2_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2702])).

cnf(c_12884,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) = k2_relat_1(k5_relat_1(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_2710])).

cnf(c_12907,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(X0))) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(X0)))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_657,c_12884])).

cnf(c_13124,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0))) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_12907])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_659,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1301,plain,
    ( k5_relat_1(k6_relat_1(X0),k2_funct_1(X1)) = k7_relat_1(k2_funct_1(X1),X0)
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_657,c_659])).

cnf(c_4315,plain,
    ( k5_relat_1(k6_relat_1(X0),k2_funct_1(sK0)) = k7_relat_1(k2_funct_1(sK0),X0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_1301])).

cnf(c_21,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4587,plain,
    ( k5_relat_1(k6_relat_1(X0),k2_funct_1(sK0)) = k7_relat_1(k2_funct_1(sK0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4315,c_21])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_663,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1463,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(X0),X1)) = k9_relat_1(k2_funct_1(X0),X1)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_657,c_663])).

cnf(c_5346,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0)) = k9_relat_1(k2_funct_1(sK0),X0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_1463])).

cnf(c_5512,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0)) = k9_relat_1(k2_funct_1(sK0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5346,c_21])).

cnf(c_13127,plain,
    ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))
    | v1_relat_1(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13124,c_4587,c_5512])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_664,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1093,plain,
    ( k9_relat_1(k2_funct_1(X0),k1_relat_1(k2_funct_1(X0))) = k2_relat_1(k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_657,c_664])).

cnf(c_2678,plain,
    ( k9_relat_1(k2_funct_1(sK0),k1_relat_1(k2_funct_1(sK0))) = k2_relat_1(k2_funct_1(sK0))
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_1093])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_18,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_242,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_243,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_25,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_245,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_243,c_20,c_19,c_18,c_25])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_250,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_251,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_250])).

cnf(c_28,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_253,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_251,c_20,c_19,c_18,c_28])).

cnf(c_2681,plain,
    ( k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) = k1_relat_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2678,c_245,c_253])).

cnf(c_3119,plain,
    ( k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2681,c_21])).

cnf(c_13128,plain,
    ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13127,c_3119])).

cnf(c_8,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_relat_1(X1) != k1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(k5_relat_1(X2,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_662,plain,
    ( k1_relat_1(X0) != k1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1991,plain,
    ( k1_relat_1(X0) != k2_relat_1(sK0)
    | k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0))) = k1_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_245,c_662])).

cnf(c_22,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_36,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_38,plain,
    ( v1_funct_1(sK0) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_2270,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0))) = k1_relat_1(k5_relat_1(X1,X0))
    | k1_relat_1(X0) != k2_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1991,c_21,c_22,c_38])).

cnf(c_2271,plain,
    ( k1_relat_1(X0) != k2_relat_1(sK0)
    | k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0))) = k1_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2270])).

cnf(c_2280,plain,
    ( k2_relat_1(sK0) != X0
    | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_2271])).

cnf(c_30,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2519,plain,
    ( v1_relat_1(X1) != iProver_top
    | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))
    | k2_relat_1(sK0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2280,c_30])).

cnf(c_2520,plain,
    ( k2_relat_1(sK0) != X0
    | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2519])).

cnf(c_2528,plain,
    ( k1_relat_1(k5_relat_1(X0,k6_relat_1(k2_relat_1(sK0)))) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2520])).

cnf(c_5186,plain,
    ( k1_relat_1(k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(superposition,[status(thm)],[c_654,c_2528])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_665,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_660,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1712,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_665,c_660])).

cnf(c_4450,plain,
    ( k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) = sK0 ),
    inference(superposition,[status(thm)],[c_654,c_1712])).

cnf(c_5188,plain,
    ( k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_5186,c_4450])).

cnf(c_17,negated_conjecture,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5791,plain,
    ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) != k1_relat_1(sK0)
    | k1_relat_1(sK0) != k1_relat_1(sK0) ),
    inference(demodulation,[status(thm)],[c_5188,c_17])).

cnf(c_376,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_384,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_376])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_67,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_63,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13128,c_5791,c_384,c_67,c_63,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:48:47 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.52/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/0.98  
% 3.52/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/0.98  
% 3.52/0.98  ------  iProver source info
% 3.52/0.98  
% 3.52/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.52/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/0.98  git: non_committed_changes: false
% 3.52/0.98  git: last_make_outside_of_git: false
% 3.52/0.98  
% 3.52/0.98  ------ 
% 3.52/0.98  
% 3.52/0.98  ------ Input Options
% 3.52/0.98  
% 3.52/0.98  --out_options                           all
% 3.52/0.98  --tptp_safe_out                         true
% 3.52/0.98  --problem_path                          ""
% 3.52/0.98  --include_path                          ""
% 3.52/0.98  --clausifier                            res/vclausify_rel
% 3.52/0.98  --clausifier_options                    --mode clausify
% 3.52/0.98  --stdin                                 false
% 3.52/0.98  --stats_out                             all
% 3.52/0.98  
% 3.52/0.98  ------ General Options
% 3.52/0.98  
% 3.52/0.98  --fof                                   false
% 3.52/0.98  --time_out_real                         305.
% 3.52/0.98  --time_out_virtual                      -1.
% 3.52/0.98  --symbol_type_check                     false
% 3.52/0.98  --clausify_out                          false
% 3.52/0.98  --sig_cnt_out                           false
% 3.52/0.99  --trig_cnt_out                          false
% 3.52/0.99  --trig_cnt_out_tolerance                1.
% 3.52/0.99  --trig_cnt_out_sk_spl                   false
% 3.52/0.99  --abstr_cl_out                          false
% 3.52/0.99  
% 3.52/0.99  ------ Global Options
% 3.52/0.99  
% 3.52/0.99  --schedule                              default
% 3.52/0.99  --add_important_lit                     false
% 3.52/0.99  --prop_solver_per_cl                    1000
% 3.52/0.99  --min_unsat_core                        false
% 3.52/0.99  --soft_assumptions                      false
% 3.52/0.99  --soft_lemma_size                       3
% 3.52/0.99  --prop_impl_unit_size                   0
% 3.52/0.99  --prop_impl_unit                        []
% 3.52/0.99  --share_sel_clauses                     true
% 3.52/0.99  --reset_solvers                         false
% 3.52/0.99  --bc_imp_inh                            [conj_cone]
% 3.52/0.99  --conj_cone_tolerance                   3.
% 3.52/0.99  --extra_neg_conj                        none
% 3.52/0.99  --large_theory_mode                     true
% 3.52/0.99  --prolific_symb_bound                   200
% 3.52/0.99  --lt_threshold                          2000
% 3.52/0.99  --clause_weak_htbl                      true
% 3.52/0.99  --gc_record_bc_elim                     false
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing Options
% 3.52/0.99  
% 3.52/0.99  --preprocessing_flag                    true
% 3.52/0.99  --time_out_prep_mult                    0.1
% 3.52/0.99  --splitting_mode                        input
% 3.52/0.99  --splitting_grd                         true
% 3.52/0.99  --splitting_cvd                         false
% 3.52/0.99  --splitting_cvd_svl                     false
% 3.52/0.99  --splitting_nvd                         32
% 3.52/0.99  --sub_typing                            true
% 3.52/0.99  --prep_gs_sim                           true
% 3.52/0.99  --prep_unflatten                        true
% 3.52/0.99  --prep_res_sim                          true
% 3.52/0.99  --prep_upred                            true
% 3.52/0.99  --prep_sem_filter                       exhaustive
% 3.52/0.99  --prep_sem_filter_out                   false
% 3.52/0.99  --pred_elim                             true
% 3.52/0.99  --res_sim_input                         true
% 3.52/0.99  --eq_ax_congr_red                       true
% 3.52/0.99  --pure_diseq_elim                       true
% 3.52/0.99  --brand_transform                       false
% 3.52/0.99  --non_eq_to_eq                          false
% 3.52/0.99  --prep_def_merge                        true
% 3.52/0.99  --prep_def_merge_prop_impl              false
% 3.52/0.99  --prep_def_merge_mbd                    true
% 3.52/0.99  --prep_def_merge_tr_red                 false
% 3.52/0.99  --prep_def_merge_tr_cl                  false
% 3.52/0.99  --smt_preprocessing                     true
% 3.52/0.99  --smt_ac_axioms                         fast
% 3.52/0.99  --preprocessed_out                      false
% 3.52/0.99  --preprocessed_stats                    false
% 3.52/0.99  
% 3.52/0.99  ------ Abstraction refinement Options
% 3.52/0.99  
% 3.52/0.99  --abstr_ref                             []
% 3.52/0.99  --abstr_ref_prep                        false
% 3.52/0.99  --abstr_ref_until_sat                   false
% 3.52/0.99  --abstr_ref_sig_restrict                funpre
% 3.52/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/0.99  --abstr_ref_under                       []
% 3.52/0.99  
% 3.52/0.99  ------ SAT Options
% 3.52/0.99  
% 3.52/0.99  --sat_mode                              false
% 3.52/0.99  --sat_fm_restart_options                ""
% 3.52/0.99  --sat_gr_def                            false
% 3.52/0.99  --sat_epr_types                         true
% 3.52/0.99  --sat_non_cyclic_types                  false
% 3.52/0.99  --sat_finite_models                     false
% 3.52/0.99  --sat_fm_lemmas                         false
% 3.52/0.99  --sat_fm_prep                           false
% 3.52/0.99  --sat_fm_uc_incr                        true
% 3.52/0.99  --sat_out_model                         small
% 3.52/0.99  --sat_out_clauses                       false
% 3.52/0.99  
% 3.52/0.99  ------ QBF Options
% 3.52/0.99  
% 3.52/0.99  --qbf_mode                              false
% 3.52/0.99  --qbf_elim_univ                         false
% 3.52/0.99  --qbf_dom_inst                          none
% 3.52/0.99  --qbf_dom_pre_inst                      false
% 3.52/0.99  --qbf_sk_in                             false
% 3.52/0.99  --qbf_pred_elim                         true
% 3.52/0.99  --qbf_split                             512
% 3.52/0.99  
% 3.52/0.99  ------ BMC1 Options
% 3.52/0.99  
% 3.52/0.99  --bmc1_incremental                      false
% 3.52/0.99  --bmc1_axioms                           reachable_all
% 3.52/0.99  --bmc1_min_bound                        0
% 3.52/0.99  --bmc1_max_bound                        -1
% 3.52/0.99  --bmc1_max_bound_default                -1
% 3.52/0.99  --bmc1_symbol_reachability              true
% 3.52/0.99  --bmc1_property_lemmas                  false
% 3.52/0.99  --bmc1_k_induction                      false
% 3.52/0.99  --bmc1_non_equiv_states                 false
% 3.52/0.99  --bmc1_deadlock                         false
% 3.52/0.99  --bmc1_ucm                              false
% 3.52/0.99  --bmc1_add_unsat_core                   none
% 3.52/0.99  --bmc1_unsat_core_children              false
% 3.52/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/0.99  --bmc1_out_stat                         full
% 3.52/0.99  --bmc1_ground_init                      false
% 3.52/0.99  --bmc1_pre_inst_next_state              false
% 3.52/0.99  --bmc1_pre_inst_state                   false
% 3.52/0.99  --bmc1_pre_inst_reach_state             false
% 3.52/0.99  --bmc1_out_unsat_core                   false
% 3.52/0.99  --bmc1_aig_witness_out                  false
% 3.52/0.99  --bmc1_verbose                          false
% 3.52/0.99  --bmc1_dump_clauses_tptp                false
% 3.52/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.52/0.99  --bmc1_dump_file                        -
% 3.52/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.52/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.52/0.99  --bmc1_ucm_extend_mode                  1
% 3.52/0.99  --bmc1_ucm_init_mode                    2
% 3.52/0.99  --bmc1_ucm_cone_mode                    none
% 3.52/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.52/0.99  --bmc1_ucm_relax_model                  4
% 3.52/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.52/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/0.99  --bmc1_ucm_layered_model                none
% 3.52/0.99  --bmc1_ucm_max_lemma_size               10
% 3.52/0.99  
% 3.52/0.99  ------ AIG Options
% 3.52/0.99  
% 3.52/0.99  --aig_mode                              false
% 3.52/0.99  
% 3.52/0.99  ------ Instantiation Options
% 3.52/0.99  
% 3.52/0.99  --instantiation_flag                    true
% 3.52/0.99  --inst_sos_flag                         false
% 3.52/0.99  --inst_sos_phase                        true
% 3.52/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/0.99  --inst_lit_sel_side                     num_symb
% 3.52/0.99  --inst_solver_per_active                1400
% 3.52/0.99  --inst_solver_calls_frac                1.
% 3.52/0.99  --inst_passive_queue_type               priority_queues
% 3.52/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/0.99  --inst_passive_queues_freq              [25;2]
% 3.52/0.99  --inst_dismatching                      true
% 3.52/0.99  --inst_eager_unprocessed_to_passive     true
% 3.52/0.99  --inst_prop_sim_given                   true
% 3.52/0.99  --inst_prop_sim_new                     false
% 3.52/0.99  --inst_subs_new                         false
% 3.52/0.99  --inst_eq_res_simp                      false
% 3.52/0.99  --inst_subs_given                       false
% 3.52/0.99  --inst_orphan_elimination               true
% 3.52/0.99  --inst_learning_loop_flag               true
% 3.52/0.99  --inst_learning_start                   3000
% 3.52/0.99  --inst_learning_factor                  2
% 3.52/0.99  --inst_start_prop_sim_after_learn       3
% 3.52/0.99  --inst_sel_renew                        solver
% 3.52/0.99  --inst_lit_activity_flag                true
% 3.52/0.99  --inst_restr_to_given                   false
% 3.52/0.99  --inst_activity_threshold               500
% 3.52/0.99  --inst_out_proof                        true
% 3.52/0.99  
% 3.52/0.99  ------ Resolution Options
% 3.52/0.99  
% 3.52/0.99  --resolution_flag                       true
% 3.52/0.99  --res_lit_sel                           adaptive
% 3.52/0.99  --res_lit_sel_side                      none
% 3.52/0.99  --res_ordering                          kbo
% 3.52/0.99  --res_to_prop_solver                    active
% 3.52/0.99  --res_prop_simpl_new                    false
% 3.52/0.99  --res_prop_simpl_given                  true
% 3.52/0.99  --res_passive_queue_type                priority_queues
% 3.52/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/0.99  --res_passive_queues_freq               [15;5]
% 3.52/0.99  --res_forward_subs                      full
% 3.52/0.99  --res_backward_subs                     full
% 3.52/0.99  --res_forward_subs_resolution           true
% 3.52/0.99  --res_backward_subs_resolution          true
% 3.52/0.99  --res_orphan_elimination                true
% 3.52/0.99  --res_time_limit                        2.
% 3.52/0.99  --res_out_proof                         true
% 3.52/0.99  
% 3.52/0.99  ------ Superposition Options
% 3.52/0.99  
% 3.52/0.99  --superposition_flag                    true
% 3.52/0.99  --sup_passive_queue_type                priority_queues
% 3.52/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.52/0.99  --demod_completeness_check              fast
% 3.52/0.99  --demod_use_ground                      true
% 3.52/0.99  --sup_to_prop_solver                    passive
% 3.52/0.99  --sup_prop_simpl_new                    true
% 3.52/0.99  --sup_prop_simpl_given                  true
% 3.52/0.99  --sup_fun_splitting                     false
% 3.52/0.99  --sup_smt_interval                      50000
% 3.52/0.99  
% 3.52/0.99  ------ Superposition Simplification Setup
% 3.52/0.99  
% 3.52/0.99  --sup_indices_passive                   []
% 3.52/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.99  --sup_full_bw                           [BwDemod]
% 3.52/0.99  --sup_immed_triv                        [TrivRules]
% 3.52/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.99  --sup_immed_bw_main                     []
% 3.52/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/0.99  
% 3.52/0.99  ------ Combination Options
% 3.52/0.99  
% 3.52/0.99  --comb_res_mult                         3
% 3.52/0.99  --comb_sup_mult                         2
% 3.52/0.99  --comb_inst_mult                        10
% 3.52/0.99  
% 3.52/0.99  ------ Debug Options
% 3.52/0.99  
% 3.52/0.99  --dbg_backtrace                         false
% 3.52/0.99  --dbg_dump_prop_clauses                 false
% 3.52/0.99  --dbg_dump_prop_clauses_file            -
% 3.52/0.99  --dbg_out_stat                          false
% 3.52/0.99  ------ Parsing...
% 3.52/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/0.99  ------ Proving...
% 3.52/0.99  ------ Problem Properties 
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  clauses                                 20
% 3.52/0.99  conjectures                             3
% 3.52/0.99  EPR                                     4
% 3.52/0.99  Horn                                    20
% 3.52/0.99  unary                                   8
% 3.52/0.99  binary                                  6
% 3.52/0.99  lits                                    42
% 3.52/0.99  lits eq                                 17
% 3.52/0.99  fd_pure                                 0
% 3.52/0.99  fd_pseudo                               0
% 3.52/0.99  fd_cond                                 0
% 3.52/0.99  fd_pseudo_cond                          1
% 3.52/0.99  AC symbols                              0
% 3.52/0.99  
% 3.52/0.99  ------ Schedule dynamic 5 is on 
% 3.52/0.99  
% 3.52/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ 
% 3.52/0.99  Current options:
% 3.52/0.99  ------ 
% 3.52/0.99  
% 3.52/0.99  ------ Input Options
% 3.52/0.99  
% 3.52/0.99  --out_options                           all
% 3.52/0.99  --tptp_safe_out                         true
% 3.52/0.99  --problem_path                          ""
% 3.52/0.99  --include_path                          ""
% 3.52/0.99  --clausifier                            res/vclausify_rel
% 3.52/0.99  --clausifier_options                    --mode clausify
% 3.52/0.99  --stdin                                 false
% 3.52/0.99  --stats_out                             all
% 3.52/0.99  
% 3.52/0.99  ------ General Options
% 3.52/0.99  
% 3.52/0.99  --fof                                   false
% 3.52/0.99  --time_out_real                         305.
% 3.52/0.99  --time_out_virtual                      -1.
% 3.52/0.99  --symbol_type_check                     false
% 3.52/0.99  --clausify_out                          false
% 3.52/0.99  --sig_cnt_out                           false
% 3.52/0.99  --trig_cnt_out                          false
% 3.52/0.99  --trig_cnt_out_tolerance                1.
% 3.52/0.99  --trig_cnt_out_sk_spl                   false
% 3.52/0.99  --abstr_cl_out                          false
% 3.52/0.99  
% 3.52/0.99  ------ Global Options
% 3.52/0.99  
% 3.52/0.99  --schedule                              default
% 3.52/0.99  --add_important_lit                     false
% 3.52/0.99  --prop_solver_per_cl                    1000
% 3.52/0.99  --min_unsat_core                        false
% 3.52/0.99  --soft_assumptions                      false
% 3.52/0.99  --soft_lemma_size                       3
% 3.52/0.99  --prop_impl_unit_size                   0
% 3.52/0.99  --prop_impl_unit                        []
% 3.52/0.99  --share_sel_clauses                     true
% 3.52/0.99  --reset_solvers                         false
% 3.52/0.99  --bc_imp_inh                            [conj_cone]
% 3.52/0.99  --conj_cone_tolerance                   3.
% 3.52/0.99  --extra_neg_conj                        none
% 3.52/0.99  --large_theory_mode                     true
% 3.52/0.99  --prolific_symb_bound                   200
% 3.52/0.99  --lt_threshold                          2000
% 3.52/0.99  --clause_weak_htbl                      true
% 3.52/0.99  --gc_record_bc_elim                     false
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing Options
% 3.52/0.99  
% 3.52/0.99  --preprocessing_flag                    true
% 3.52/0.99  --time_out_prep_mult                    0.1
% 3.52/0.99  --splitting_mode                        input
% 3.52/0.99  --splitting_grd                         true
% 3.52/0.99  --splitting_cvd                         false
% 3.52/0.99  --splitting_cvd_svl                     false
% 3.52/0.99  --splitting_nvd                         32
% 3.52/0.99  --sub_typing                            true
% 3.52/0.99  --prep_gs_sim                           true
% 3.52/0.99  --prep_unflatten                        true
% 3.52/0.99  --prep_res_sim                          true
% 3.52/0.99  --prep_upred                            true
% 3.52/0.99  --prep_sem_filter                       exhaustive
% 3.52/0.99  --prep_sem_filter_out                   false
% 3.52/0.99  --pred_elim                             true
% 3.52/0.99  --res_sim_input                         true
% 3.52/0.99  --eq_ax_congr_red                       true
% 3.52/0.99  --pure_diseq_elim                       true
% 3.52/0.99  --brand_transform                       false
% 3.52/0.99  --non_eq_to_eq                          false
% 3.52/0.99  --prep_def_merge                        true
% 3.52/0.99  --prep_def_merge_prop_impl              false
% 3.52/0.99  --prep_def_merge_mbd                    true
% 3.52/0.99  --prep_def_merge_tr_red                 false
% 3.52/0.99  --prep_def_merge_tr_cl                  false
% 3.52/0.99  --smt_preprocessing                     true
% 3.52/0.99  --smt_ac_axioms                         fast
% 3.52/0.99  --preprocessed_out                      false
% 3.52/0.99  --preprocessed_stats                    false
% 3.52/0.99  
% 3.52/0.99  ------ Abstraction refinement Options
% 3.52/0.99  
% 3.52/0.99  --abstr_ref                             []
% 3.52/0.99  --abstr_ref_prep                        false
% 3.52/0.99  --abstr_ref_until_sat                   false
% 3.52/0.99  --abstr_ref_sig_restrict                funpre
% 3.52/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/0.99  --abstr_ref_under                       []
% 3.52/0.99  
% 3.52/0.99  ------ SAT Options
% 3.52/0.99  
% 3.52/0.99  --sat_mode                              false
% 3.52/0.99  --sat_fm_restart_options                ""
% 3.52/0.99  --sat_gr_def                            false
% 3.52/0.99  --sat_epr_types                         true
% 3.52/0.99  --sat_non_cyclic_types                  false
% 3.52/0.99  --sat_finite_models                     false
% 3.52/0.99  --sat_fm_lemmas                         false
% 3.52/0.99  --sat_fm_prep                           false
% 3.52/0.99  --sat_fm_uc_incr                        true
% 3.52/0.99  --sat_out_model                         small
% 3.52/0.99  --sat_out_clauses                       false
% 3.52/0.99  
% 3.52/0.99  ------ QBF Options
% 3.52/0.99  
% 3.52/0.99  --qbf_mode                              false
% 3.52/0.99  --qbf_elim_univ                         false
% 3.52/0.99  --qbf_dom_inst                          none
% 3.52/0.99  --qbf_dom_pre_inst                      false
% 3.52/0.99  --qbf_sk_in                             false
% 3.52/0.99  --qbf_pred_elim                         true
% 3.52/0.99  --qbf_split                             512
% 3.52/0.99  
% 3.52/0.99  ------ BMC1 Options
% 3.52/0.99  
% 3.52/0.99  --bmc1_incremental                      false
% 3.52/0.99  --bmc1_axioms                           reachable_all
% 3.52/0.99  --bmc1_min_bound                        0
% 3.52/0.99  --bmc1_max_bound                        -1
% 3.52/0.99  --bmc1_max_bound_default                -1
% 3.52/0.99  --bmc1_symbol_reachability              true
% 3.52/0.99  --bmc1_property_lemmas                  false
% 3.52/0.99  --bmc1_k_induction                      false
% 3.52/0.99  --bmc1_non_equiv_states                 false
% 3.52/0.99  --bmc1_deadlock                         false
% 3.52/0.99  --bmc1_ucm                              false
% 3.52/0.99  --bmc1_add_unsat_core                   none
% 3.52/0.99  --bmc1_unsat_core_children              false
% 3.52/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/0.99  --bmc1_out_stat                         full
% 3.52/0.99  --bmc1_ground_init                      false
% 3.52/0.99  --bmc1_pre_inst_next_state              false
% 3.52/0.99  --bmc1_pre_inst_state                   false
% 3.52/0.99  --bmc1_pre_inst_reach_state             false
% 3.52/0.99  --bmc1_out_unsat_core                   false
% 3.52/0.99  --bmc1_aig_witness_out                  false
% 3.52/0.99  --bmc1_verbose                          false
% 3.52/0.99  --bmc1_dump_clauses_tptp                false
% 3.52/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.52/0.99  --bmc1_dump_file                        -
% 3.52/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.52/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.52/0.99  --bmc1_ucm_extend_mode                  1
% 3.52/0.99  --bmc1_ucm_init_mode                    2
% 3.52/0.99  --bmc1_ucm_cone_mode                    none
% 3.52/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.52/0.99  --bmc1_ucm_relax_model                  4
% 3.52/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.52/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/0.99  --bmc1_ucm_layered_model                none
% 3.52/0.99  --bmc1_ucm_max_lemma_size               10
% 3.52/0.99  
% 3.52/0.99  ------ AIG Options
% 3.52/0.99  
% 3.52/0.99  --aig_mode                              false
% 3.52/0.99  
% 3.52/0.99  ------ Instantiation Options
% 3.52/0.99  
% 3.52/0.99  --instantiation_flag                    true
% 3.52/0.99  --inst_sos_flag                         false
% 3.52/0.99  --inst_sos_phase                        true
% 3.52/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/0.99  --inst_lit_sel_side                     none
% 3.52/0.99  --inst_solver_per_active                1400
% 3.52/0.99  --inst_solver_calls_frac                1.
% 3.52/0.99  --inst_passive_queue_type               priority_queues
% 3.52/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/0.99  --inst_passive_queues_freq              [25;2]
% 3.52/0.99  --inst_dismatching                      true
% 3.52/0.99  --inst_eager_unprocessed_to_passive     true
% 3.52/0.99  --inst_prop_sim_given                   true
% 3.52/0.99  --inst_prop_sim_new                     false
% 3.52/0.99  --inst_subs_new                         false
% 3.52/0.99  --inst_eq_res_simp                      false
% 3.52/0.99  --inst_subs_given                       false
% 3.52/0.99  --inst_orphan_elimination               true
% 3.52/0.99  --inst_learning_loop_flag               true
% 3.52/0.99  --inst_learning_start                   3000
% 3.52/0.99  --inst_learning_factor                  2
% 3.52/0.99  --inst_start_prop_sim_after_learn       3
% 3.52/0.99  --inst_sel_renew                        solver
% 3.52/0.99  --inst_lit_activity_flag                true
% 3.52/0.99  --inst_restr_to_given                   false
% 3.52/0.99  --inst_activity_threshold               500
% 3.52/0.99  --inst_out_proof                        true
% 3.52/0.99  
% 3.52/0.99  ------ Resolution Options
% 3.52/0.99  
% 3.52/0.99  --resolution_flag                       false
% 3.52/0.99  --res_lit_sel                           adaptive
% 3.52/0.99  --res_lit_sel_side                      none
% 3.52/0.99  --res_ordering                          kbo
% 3.52/0.99  --res_to_prop_solver                    active
% 3.52/0.99  --res_prop_simpl_new                    false
% 3.52/0.99  --res_prop_simpl_given                  true
% 3.52/0.99  --res_passive_queue_type                priority_queues
% 3.52/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/0.99  --res_passive_queues_freq               [15;5]
% 3.52/0.99  --res_forward_subs                      full
% 3.52/0.99  --res_backward_subs                     full
% 3.52/0.99  --res_forward_subs_resolution           true
% 3.52/0.99  --res_backward_subs_resolution          true
% 3.52/0.99  --res_orphan_elimination                true
% 3.52/0.99  --res_time_limit                        2.
% 3.52/0.99  --res_out_proof                         true
% 3.52/0.99  
% 3.52/0.99  ------ Superposition Options
% 3.52/0.99  
% 3.52/0.99  --superposition_flag                    true
% 3.52/0.99  --sup_passive_queue_type                priority_queues
% 3.52/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.52/0.99  --demod_completeness_check              fast
% 3.52/0.99  --demod_use_ground                      true
% 3.52/0.99  --sup_to_prop_solver                    passive
% 3.52/0.99  --sup_prop_simpl_new                    true
% 3.52/0.99  --sup_prop_simpl_given                  true
% 3.52/0.99  --sup_fun_splitting                     false
% 3.52/0.99  --sup_smt_interval                      50000
% 3.52/0.99  
% 3.52/0.99  ------ Superposition Simplification Setup
% 3.52/0.99  
% 3.52/0.99  --sup_indices_passive                   []
% 3.52/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.99  --sup_full_bw                           [BwDemod]
% 3.52/0.99  --sup_immed_triv                        [TrivRules]
% 3.52/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.99  --sup_immed_bw_main                     []
% 3.52/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/0.99  
% 3.52/0.99  ------ Combination Options
% 3.52/0.99  
% 3.52/0.99  --comb_res_mult                         3
% 3.52/0.99  --comb_sup_mult                         2
% 3.52/0.99  --comb_inst_mult                        10
% 3.52/0.99  
% 3.52/0.99  ------ Debug Options
% 3.52/0.99  
% 3.52/0.99  --dbg_backtrace                         false
% 3.52/0.99  --dbg_dump_prop_clauses                 false
% 3.52/0.99  --dbg_dump_prop_clauses_file            -
% 3.52/0.99  --dbg_out_stat                          false
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ Proving...
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  % SZS status Theorem for theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  fof(f12,conjecture,(
% 3.52/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f13,negated_conjecture,(
% 3.52/0.99    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 3.52/0.99    inference(negated_conjecture,[],[f12])).
% 3.52/0.99  
% 3.52/0.99  fof(f27,plain,(
% 3.52/0.99    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.52/0.99    inference(ennf_transformation,[],[f13])).
% 3.52/0.99  
% 3.52/0.99  fof(f28,plain,(
% 3.52/0.99    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.52/0.99    inference(flattening,[],[f27])).
% 3.52/0.99  
% 3.52/0.99  fof(f31,plain,(
% 3.52/0.99    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 3.52/0.99    introduced(choice_axiom,[])).
% 3.52/0.99  
% 3.52/0.99  fof(f32,plain,(
% 3.52/0.99    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 3.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f31])).
% 3.52/0.99  
% 3.52/0.99  fof(f51,plain,(
% 3.52/0.99    v1_funct_1(sK0)),
% 3.52/0.99    inference(cnf_transformation,[],[f32])).
% 3.52/0.99  
% 3.52/0.99  fof(f9,axiom,(
% 3.52/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f23,plain,(
% 3.52/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.52/0.99    inference(ennf_transformation,[],[f9])).
% 3.52/0.99  
% 3.52/0.99  fof(f24,plain,(
% 3.52/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/0.99    inference(flattening,[],[f23])).
% 3.52/0.99  
% 3.52/0.99  fof(f44,plain,(
% 3.52/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f24])).
% 3.52/0.99  
% 3.52/0.99  fof(f50,plain,(
% 3.52/0.99    v1_relat_1(sK0)),
% 3.52/0.99    inference(cnf_transformation,[],[f32])).
% 3.52/0.99  
% 3.52/0.99  fof(f6,axiom,(
% 3.52/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f41,plain,(
% 3.52/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.52/0.99    inference(cnf_transformation,[],[f6])).
% 3.52/0.99  
% 3.52/0.99  fof(f5,axiom,(
% 3.52/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f18,plain,(
% 3.52/0.99    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.52/0.99    inference(ennf_transformation,[],[f5])).
% 3.52/0.99  
% 3.52/0.99  fof(f19,plain,(
% 3.52/0.99    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.52/0.99    inference(flattening,[],[f18])).
% 3.52/0.99  
% 3.52/0.99  fof(f39,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f19])).
% 3.52/0.99  
% 3.52/0.99  fof(f10,axiom,(
% 3.52/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f46,plain,(
% 3.52/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.52/0.99    inference(cnf_transformation,[],[f10])).
% 3.52/0.99  
% 3.52/0.99  fof(f8,axiom,(
% 3.52/0.99    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f22,plain,(
% 3.52/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.52/0.99    inference(ennf_transformation,[],[f8])).
% 3.52/0.99  
% 3.52/0.99  fof(f43,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f22])).
% 3.52/0.99  
% 3.52/0.99  fof(f3,axiom,(
% 3.52/0.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f15,plain,(
% 3.52/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.52/0.99    inference(ennf_transformation,[],[f3])).
% 3.52/0.99  
% 3.52/0.99  fof(f37,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f15])).
% 3.52/0.99  
% 3.52/0.99  fof(f2,axiom,(
% 3.52/0.99    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f14,plain,(
% 3.52/0.99    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.52/0.99    inference(ennf_transformation,[],[f2])).
% 3.52/0.99  
% 3.52/0.99  fof(f36,plain,(
% 3.52/0.99    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f14])).
% 3.52/0.99  
% 3.52/0.99  fof(f11,axiom,(
% 3.52/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f25,plain,(
% 3.52/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.52/0.99    inference(ennf_transformation,[],[f11])).
% 3.52/0.99  
% 3.52/0.99  fof(f26,plain,(
% 3.52/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/0.99    inference(flattening,[],[f25])).
% 3.52/0.99  
% 3.52/0.99  fof(f48,plain,(
% 3.52/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f26])).
% 3.52/0.99  
% 3.52/0.99  fof(f52,plain,(
% 3.52/0.99    v2_funct_1(sK0)),
% 3.52/0.99    inference(cnf_transformation,[],[f32])).
% 3.52/0.99  
% 3.52/0.99  fof(f49,plain,(
% 3.52/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f26])).
% 3.52/0.99  
% 3.52/0.99  fof(f40,plain,(
% 3.52/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.52/0.99    inference(cnf_transformation,[],[f6])).
% 3.52/0.99  
% 3.52/0.99  fof(f4,axiom,(
% 3.52/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f16,plain,(
% 3.52/0.99    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.52/0.99    inference(ennf_transformation,[],[f4])).
% 3.52/0.99  
% 3.52/0.99  fof(f17,plain,(
% 3.52/0.99    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.52/0.99    inference(flattening,[],[f16])).
% 3.52/0.99  
% 3.52/0.99  fof(f38,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f17])).
% 3.52/0.99  
% 3.52/0.99  fof(f1,axiom,(
% 3.52/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f29,plain,(
% 3.52/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.52/0.99    inference(nnf_transformation,[],[f1])).
% 3.52/0.99  
% 3.52/0.99  fof(f30,plain,(
% 3.52/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.52/0.99    inference(flattening,[],[f29])).
% 3.52/0.99  
% 3.52/0.99  fof(f34,plain,(
% 3.52/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.52/0.99    inference(cnf_transformation,[],[f30])).
% 3.52/0.99  
% 3.52/0.99  fof(f54,plain,(
% 3.52/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.52/0.99    inference(equality_resolution,[],[f34])).
% 3.52/0.99  
% 3.52/0.99  fof(f7,axiom,(
% 3.52/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f20,plain,(
% 3.52/0.99    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.52/0.99    inference(ennf_transformation,[],[f7])).
% 3.52/0.99  
% 3.52/0.99  fof(f21,plain,(
% 3.52/0.99    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.52/0.99    inference(flattening,[],[f20])).
% 3.52/0.99  
% 3.52/0.99  fof(f42,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f21])).
% 3.52/0.99  
% 3.52/0.99  fof(f53,plain,(
% 3.52/0.99    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 3.52/0.99    inference(cnf_transformation,[],[f32])).
% 3.52/0.99  
% 3.52/0.99  fof(f35,plain,(
% 3.52/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f30])).
% 3.52/0.99  
% 3.52/0.99  fof(f33,plain,(
% 3.52/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.52/0.99    inference(cnf_transformation,[],[f30])).
% 3.52/0.99  
% 3.52/0.99  fof(f55,plain,(
% 3.52/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.52/0.99    inference(equality_resolution,[],[f33])).
% 3.52/0.99  
% 3.52/0.99  cnf(c_19,negated_conjecture,
% 3.52/0.99      ( v1_funct_1(sK0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_655,plain,
% 3.52/0.99      ( v1_funct_1(sK0) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_12,plain,
% 3.52/0.99      ( ~ v1_funct_1(X0)
% 3.52/0.99      | ~ v1_relat_1(X0)
% 3.52/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 3.52/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_657,plain,
% 3.52/0.99      ( v1_funct_1(X0) != iProver_top
% 3.52/0.99      | v1_relat_1(X0) != iProver_top
% 3.52/0.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_20,negated_conjecture,
% 3.52/0.99      ( v1_relat_1(sK0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_654,plain,
% 3.52/0.99      ( v1_relat_1(sK0) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_7,plain,
% 3.52/0.99      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.52/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_6,plain,
% 3.52/0.99      ( ~ v1_relat_1(X0)
% 3.52/0.99      | ~ v1_relat_1(X1)
% 3.52/0.99      | ~ v1_relat_1(X2)
% 3.52/0.99      | k2_relat_1(X1) != k2_relat_1(X0)
% 3.52/0.99      | k2_relat_1(k5_relat_1(X1,X2)) = k2_relat_1(k5_relat_1(X0,X2)) ),
% 3.52/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_661,plain,
% 3.52/0.99      ( k2_relat_1(X0) != k2_relat_1(X1)
% 3.52/0.99      | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
% 3.52/0.99      | v1_relat_1(X1) != iProver_top
% 3.52/0.99      | v1_relat_1(X0) != iProver_top
% 3.52/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1925,plain,
% 3.52/0.99      ( k2_relat_1(X0) != X1
% 3.52/0.99      | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
% 3.52/0.99      | v1_relat_1(X0) != iProver_top
% 3.52/0.99      | v1_relat_1(X2) != iProver_top
% 3.52/0.99      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_7,c_661]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_14,plain,
% 3.52/0.99      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.52/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_656,plain,
% 3.52/0.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2702,plain,
% 3.52/0.99      ( k2_relat_1(X0) != X1
% 3.52/0.99      | k2_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k5_relat_1(X0,X2))
% 3.52/0.99      | v1_relat_1(X0) != iProver_top
% 3.52/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.52/0.99      inference(forward_subsumption_resolution,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_1925,c_656]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2710,plain,
% 3.52/0.99      ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(X0)),X1)) = k2_relat_1(k5_relat_1(X0,X1))
% 3.52/0.99      | v1_relat_1(X0) != iProver_top
% 3.52/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.52/0.99      inference(equality_resolution,[status(thm)],[c_2702]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_12884,plain,
% 3.52/0.99      ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)) = k2_relat_1(k5_relat_1(sK0,X0))
% 3.52/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_654,c_2710]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_12907,plain,
% 3.52/0.99      ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(X0))) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(X0)))
% 3.52/0.99      | v1_funct_1(X0) != iProver_top
% 3.52/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_657,c_12884]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_13124,plain,
% 3.52/0.99      ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0))) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
% 3.52/0.99      | v1_relat_1(sK0) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_655,c_12907]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_10,plain,
% 3.52/0.99      ( ~ v1_relat_1(X0)
% 3.52/0.99      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_659,plain,
% 3.52/0.99      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 3.52/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1301,plain,
% 3.52/0.99      ( k5_relat_1(k6_relat_1(X0),k2_funct_1(X1)) = k7_relat_1(k2_funct_1(X1),X0)
% 3.52/0.99      | v1_funct_1(X1) != iProver_top
% 3.52/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_657,c_659]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_4315,plain,
% 3.52/0.99      ( k5_relat_1(k6_relat_1(X0),k2_funct_1(sK0)) = k7_relat_1(k2_funct_1(sK0),X0)
% 3.52/0.99      | v1_relat_1(sK0) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_655,c_1301]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_21,plain,
% 3.52/0.99      ( v1_relat_1(sK0) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_4587,plain,
% 3.52/0.99      ( k5_relat_1(k6_relat_1(X0),k2_funct_1(sK0)) = k7_relat_1(k2_funct_1(sK0),X0) ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_4315,c_21]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_4,plain,
% 3.52/0.99      ( ~ v1_relat_1(X0)
% 3.52/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_663,plain,
% 3.52/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.52/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1463,plain,
% 3.52/0.99      ( k2_relat_1(k7_relat_1(k2_funct_1(X0),X1)) = k9_relat_1(k2_funct_1(X0),X1)
% 3.52/0.99      | v1_funct_1(X0) != iProver_top
% 3.52/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_657,c_663]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_5346,plain,
% 3.52/0.99      ( k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0)) = k9_relat_1(k2_funct_1(sK0),X0)
% 3.52/0.99      | v1_relat_1(sK0) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_655,c_1463]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_5512,plain,
% 3.52/0.99      ( k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0)) = k9_relat_1(k2_funct_1(sK0),X0) ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_5346,c_21]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_13127,plain,
% 3.52/0.99      ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))
% 3.52/0.99      | v1_relat_1(sK0) != iProver_top ),
% 3.52/0.99      inference(demodulation,[status(thm)],[c_13124,c_4587,c_5512]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3,plain,
% 3.52/0.99      ( ~ v1_relat_1(X0)
% 3.52/0.99      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_664,plain,
% 3.52/0.99      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.52/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1093,plain,
% 3.52/0.99      ( k9_relat_1(k2_funct_1(X0),k1_relat_1(k2_funct_1(X0))) = k2_relat_1(k2_funct_1(X0))
% 3.52/0.99      | v1_funct_1(X0) != iProver_top
% 3.52/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_657,c_664]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2678,plain,
% 3.52/0.99      ( k9_relat_1(k2_funct_1(sK0),k1_relat_1(k2_funct_1(sK0))) = k2_relat_1(k2_funct_1(sK0))
% 3.52/0.99      | v1_relat_1(sK0) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_655,c_1093]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_16,plain,
% 3.52/0.99      ( ~ v2_funct_1(X0)
% 3.52/0.99      | ~ v1_funct_1(X0)
% 3.52/0.99      | ~ v1_relat_1(X0)
% 3.52/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_18,negated_conjecture,
% 3.52/0.99      ( v2_funct_1(sK0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_242,plain,
% 3.52/0.99      ( ~ v1_funct_1(X0)
% 3.52/0.99      | ~ v1_relat_1(X0)
% 3.52/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.52/0.99      | sK0 != X0 ),
% 3.52/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_243,plain,
% 3.52/0.99      ( ~ v1_funct_1(sK0)
% 3.52/0.99      | ~ v1_relat_1(sK0)
% 3.52/0.99      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 3.52/0.99      inference(unflattening,[status(thm)],[c_242]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_25,plain,
% 3.52/0.99      ( ~ v2_funct_1(sK0)
% 3.52/0.99      | ~ v1_funct_1(sK0)
% 3.52/0.99      | ~ v1_relat_1(sK0)
% 3.52/0.99      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_245,plain,
% 3.52/0.99      ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_243,c_20,c_19,c_18,c_25]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_15,plain,
% 3.52/0.99      ( ~ v2_funct_1(X0)
% 3.52/0.99      | ~ v1_funct_1(X0)
% 3.52/0.99      | ~ v1_relat_1(X0)
% 3.52/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_250,plain,
% 3.52/0.99      ( ~ v1_funct_1(X0)
% 3.52/0.99      | ~ v1_relat_1(X0)
% 3.52/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.52/0.99      | sK0 != X0 ),
% 3.52/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_251,plain,
% 3.52/0.99      ( ~ v1_funct_1(sK0)
% 3.52/0.99      | ~ v1_relat_1(sK0)
% 3.52/0.99      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 3.52/0.99      inference(unflattening,[status(thm)],[c_250]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_28,plain,
% 3.52/0.99      ( ~ v2_funct_1(sK0)
% 3.52/0.99      | ~ v1_funct_1(sK0)
% 3.52/0.99      | ~ v1_relat_1(sK0)
% 3.52/0.99      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_253,plain,
% 3.52/0.99      ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_251,c_20,c_19,c_18,c_28]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2681,plain,
% 3.52/0.99      ( k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) = k1_relat_1(sK0)
% 3.52/0.99      | v1_relat_1(sK0) != iProver_top ),
% 3.52/0.99      inference(light_normalisation,[status(thm)],[c_2678,c_245,c_253]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3119,plain,
% 3.52/0.99      ( k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) = k1_relat_1(sK0) ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_2681,c_21]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_13128,plain,
% 3.52/0.99      ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(sK0)
% 3.52/0.99      | v1_relat_1(sK0) != iProver_top ),
% 3.52/0.99      inference(light_normalisation,[status(thm)],[c_13127,c_3119]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_8,plain,
% 3.52/0.99      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.52/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_5,plain,
% 3.52/0.99      ( ~ v1_relat_1(X0)
% 3.52/0.99      | ~ v1_relat_1(X1)
% 3.52/0.99      | ~ v1_relat_1(X2)
% 3.52/0.99      | k1_relat_1(X1) != k1_relat_1(X0)
% 3.52/0.99      | k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(k5_relat_1(X2,X0)) ),
% 3.52/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_662,plain,
% 3.52/0.99      ( k1_relat_1(X0) != k1_relat_1(X1)
% 3.52/0.99      | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
% 3.52/0.99      | v1_relat_1(X1) != iProver_top
% 3.52/0.99      | v1_relat_1(X0) != iProver_top
% 3.52/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1991,plain,
% 3.52/0.99      ( k1_relat_1(X0) != k2_relat_1(sK0)
% 3.52/0.99      | k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0))) = k1_relat_1(k5_relat_1(X1,X0))
% 3.52/0.99      | v1_relat_1(X0) != iProver_top
% 3.52/0.99      | v1_relat_1(X1) != iProver_top
% 3.52/0.99      | v1_relat_1(k2_funct_1(sK0)) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_245,c_662]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_22,plain,
% 3.52/0.99      ( v1_funct_1(sK0) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_36,plain,
% 3.52/0.99      ( v1_funct_1(X0) != iProver_top
% 3.52/0.99      | v1_relat_1(X0) != iProver_top
% 3.52/0.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_38,plain,
% 3.52/0.99      ( v1_funct_1(sK0) != iProver_top
% 3.52/0.99      | v1_relat_1(k2_funct_1(sK0)) = iProver_top
% 3.52/0.99      | v1_relat_1(sK0) != iProver_top ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_36]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2270,plain,
% 3.52/0.99      ( v1_relat_1(X1) != iProver_top
% 3.52/0.99      | v1_relat_1(X0) != iProver_top
% 3.52/0.99      | k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0))) = k1_relat_1(k5_relat_1(X1,X0))
% 3.52/0.99      | k1_relat_1(X0) != k2_relat_1(sK0) ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_1991,c_21,c_22,c_38]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2271,plain,
% 3.52/0.99      ( k1_relat_1(X0) != k2_relat_1(sK0)
% 3.52/0.99      | k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0))) = k1_relat_1(k5_relat_1(X1,X0))
% 3.52/0.99      | v1_relat_1(X0) != iProver_top
% 3.52/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.52/0.99      inference(renaming,[status(thm)],[c_2270]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2280,plain,
% 3.52/0.99      ( k2_relat_1(sK0) != X0
% 3.52/0.99      | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))
% 3.52/0.99      | v1_relat_1(X1) != iProver_top
% 3.52/0.99      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_8,c_2271]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_30,plain,
% 3.52/0.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2519,plain,
% 3.52/0.99      ( v1_relat_1(X1) != iProver_top
% 3.52/0.99      | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))
% 3.52/0.99      | k2_relat_1(sK0) != X0 ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_2280,c_30]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2520,plain,
% 3.52/0.99      ( k2_relat_1(sK0) != X0
% 3.52/0.99      | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k1_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))
% 3.52/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.52/0.99      inference(renaming,[status(thm)],[c_2519]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2528,plain,
% 3.52/0.99      ( k1_relat_1(k5_relat_1(X0,k6_relat_1(k2_relat_1(sK0)))) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
% 3.52/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.52/0.99      inference(equality_resolution,[status(thm)],[c_2520]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_5186,plain,
% 3.52/0.99      ( k1_relat_1(k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_654,c_2528]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1,plain,
% 3.52/0.99      ( r1_tarski(X0,X0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_665,plain,
% 3.52/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_9,plain,
% 3.52/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.52/0.99      | ~ v1_relat_1(X0)
% 3.52/0.99      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 3.52/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_660,plain,
% 3.52/0.99      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 3.52/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.52/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1712,plain,
% 3.52/0.99      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 3.52/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_665,c_660]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_4450,plain,
% 3.52/0.99      ( k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) = sK0 ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_654,c_1712]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_5188,plain,
% 3.52/0.99      ( k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k1_relat_1(sK0) ),
% 3.52/0.99      inference(light_normalisation,[status(thm)],[c_5186,c_4450]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_17,negated_conjecture,
% 3.52/0.99      ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
% 3.52/0.99      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
% 3.52/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_5791,plain,
% 3.52/0.99      ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) != k1_relat_1(sK0)
% 3.52/0.99      | k1_relat_1(sK0) != k1_relat_1(sK0) ),
% 3.52/0.99      inference(demodulation,[status(thm)],[c_5188,c_17]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_376,plain,
% 3.52/0.99      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 3.52/0.99      theory(equality) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_384,plain,
% 3.52/0.99      ( k1_relat_1(sK0) = k1_relat_1(sK0) | sK0 != sK0 ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_376]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_0,plain,
% 3.52/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.52/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_67,plain,
% 3.52/0.99      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2,plain,
% 3.52/0.99      ( r1_tarski(X0,X0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_63,plain,
% 3.52/0.99      ( r1_tarski(sK0,sK0) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(contradiction,plain,
% 3.52/0.99      ( $false ),
% 3.52/0.99      inference(minisat,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_13128,c_5791,c_384,c_67,c_63,c_21]) ).
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  ------                               Statistics
% 3.52/0.99  
% 3.52/0.99  ------ General
% 3.52/0.99  
% 3.52/0.99  abstr_ref_over_cycles:                  0
% 3.52/0.99  abstr_ref_under_cycles:                 0
% 3.52/0.99  gc_basic_clause_elim:                   0
% 3.52/0.99  forced_gc_time:                         0
% 3.52/0.99  parsing_time:                           0.008
% 3.52/0.99  unif_index_cands_time:                  0.
% 3.52/0.99  unif_index_add_time:                    0.
% 3.52/0.99  orderings_time:                         0.
% 3.52/0.99  out_proof_time:                         0.009
% 3.52/0.99  total_time:                             0.331
% 3.52/0.99  num_of_symbols:                         43
% 3.52/0.99  num_of_terms:                           9211
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing
% 3.52/0.99  
% 3.52/0.99  num_of_splits:                          0
% 3.52/0.99  num_of_split_atoms:                     0
% 3.52/0.99  num_of_reused_defs:                     0
% 3.52/0.99  num_eq_ax_congr_red:                    15
% 3.52/0.99  num_of_sem_filtered_clauses:            1
% 3.52/0.99  num_of_subtypes:                        0
% 3.52/0.99  monotx_restored_types:                  0
% 3.52/0.99  sat_num_of_epr_types:                   0
% 3.52/0.99  sat_num_of_non_cyclic_types:            0
% 3.52/0.99  sat_guarded_non_collapsed_types:        0
% 3.52/0.99  num_pure_diseq_elim:                    0
% 3.52/0.99  simp_replaced_by:                       0
% 3.52/0.99  res_preprocessed:                       101
% 3.52/0.99  prep_upred:                             0
% 3.52/0.99  prep_unflattend:                        4
% 3.52/0.99  smt_new_axioms:                         0
% 3.52/0.99  pred_elim_cands:                        3
% 3.52/0.99  pred_elim:                              1
% 3.52/0.99  pred_elim_cl:                           0
% 3.52/0.99  pred_elim_cycles:                       3
% 3.52/0.99  merged_defs:                            0
% 3.52/0.99  merged_defs_ncl:                        0
% 3.52/0.99  bin_hyper_res:                          0
% 3.52/0.99  prep_cycles:                            4
% 3.52/0.99  pred_elim_time:                         0.001
% 3.52/0.99  splitting_time:                         0.
% 3.52/0.99  sem_filter_time:                        0.
% 3.52/0.99  monotx_time:                            0.
% 3.52/0.99  subtype_inf_time:                       0.
% 3.52/0.99  
% 3.52/0.99  ------ Problem properties
% 3.52/0.99  
% 3.52/0.99  clauses:                                20
% 3.52/0.99  conjectures:                            3
% 3.52/0.99  epr:                                    4
% 3.52/0.99  horn:                                   20
% 3.52/0.99  ground:                                 5
% 3.52/0.99  unary:                                  8
% 3.52/0.99  binary:                                 6
% 3.52/0.99  lits:                                   42
% 3.52/0.99  lits_eq:                                17
% 3.52/0.99  fd_pure:                                0
% 3.52/0.99  fd_pseudo:                              0
% 3.52/0.99  fd_cond:                                0
% 3.52/0.99  fd_pseudo_cond:                         1
% 3.52/0.99  ac_symbols:                             0
% 3.52/0.99  
% 3.52/0.99  ------ Propositional Solver
% 3.52/0.99  
% 3.52/0.99  prop_solver_calls:                      29
% 3.52/0.99  prop_fast_solver_calls:                 910
% 3.52/0.99  smt_solver_calls:                       0
% 3.52/0.99  smt_fast_solver_calls:                  0
% 3.52/0.99  prop_num_of_clauses:                    4015
% 3.52/0.99  prop_preprocess_simplified:             9974
% 3.52/0.99  prop_fo_subsumed:                       26
% 3.52/0.99  prop_solver_time:                       0.
% 3.52/0.99  smt_solver_time:                        0.
% 3.52/0.99  smt_fast_solver_time:                   0.
% 3.52/0.99  prop_fast_solver_time:                  0.
% 3.52/0.99  prop_unsat_core_time:                   0.
% 3.52/0.99  
% 3.52/0.99  ------ QBF
% 3.52/0.99  
% 3.52/0.99  qbf_q_res:                              0
% 3.52/0.99  qbf_num_tautologies:                    0
% 3.52/0.99  qbf_prep_cycles:                        0
% 3.52/0.99  
% 3.52/0.99  ------ BMC1
% 3.52/0.99  
% 3.52/0.99  bmc1_current_bound:                     -1
% 3.52/0.99  bmc1_last_solved_bound:                 -1
% 3.52/0.99  bmc1_unsat_core_size:                   -1
% 3.52/0.99  bmc1_unsat_core_parents_size:           -1
% 3.52/0.99  bmc1_merge_next_fun:                    0
% 3.52/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.52/0.99  
% 3.52/0.99  ------ Instantiation
% 3.52/0.99  
% 3.52/0.99  inst_num_of_clauses:                    1561
% 3.52/0.99  inst_num_in_passive:                    455
% 3.52/0.99  inst_num_in_active:                     613
% 3.52/0.99  inst_num_in_unprocessed:                494
% 3.52/0.99  inst_num_of_loops:                      630
% 3.52/0.99  inst_num_of_learning_restarts:          0
% 3.52/0.99  inst_num_moves_active_passive:          13
% 3.52/0.99  inst_lit_activity:                      0
% 3.52/0.99  inst_lit_activity_moves:                0
% 3.52/0.99  inst_num_tautologies:                   0
% 3.52/0.99  inst_num_prop_implied:                  0
% 3.52/0.99  inst_num_existing_simplified:           0
% 3.52/0.99  inst_num_eq_res_simplified:             0
% 3.52/0.99  inst_num_child_elim:                    0
% 3.52/0.99  inst_num_of_dismatching_blockings:      1949
% 3.52/0.99  inst_num_of_non_proper_insts:           2584
% 3.52/0.99  inst_num_of_duplicates:                 0
% 3.52/0.99  inst_inst_num_from_inst_to_res:         0
% 3.52/0.99  inst_dismatching_checking_time:         0.
% 3.52/0.99  
% 3.52/0.99  ------ Resolution
% 3.52/0.99  
% 3.52/0.99  res_num_of_clauses:                     0
% 3.52/0.99  res_num_in_passive:                     0
% 3.52/0.99  res_num_in_active:                      0
% 3.52/0.99  res_num_of_loops:                       105
% 3.52/0.99  res_forward_subset_subsumed:            387
% 3.52/0.99  res_backward_subset_subsumed:           4
% 3.52/0.99  res_forward_subsumed:                   0
% 3.52/0.99  res_backward_subsumed:                  0
% 3.52/0.99  res_forward_subsumption_resolution:     0
% 3.52/0.99  res_backward_subsumption_resolution:    0
% 3.52/0.99  res_clause_to_clause_subsumption:       577
% 3.52/0.99  res_orphan_elimination:                 0
% 3.52/0.99  res_tautology_del:                      282
% 3.52/0.99  res_num_eq_res_simplified:              0
% 3.52/0.99  res_num_sel_changes:                    0
% 3.52/0.99  res_moves_from_active_to_pass:          0
% 3.52/0.99  
% 3.52/0.99  ------ Superposition
% 3.52/0.99  
% 3.52/0.99  sup_time_total:                         0.
% 3.52/0.99  sup_time_generating:                    0.
% 3.52/0.99  sup_time_sim_full:                      0.
% 3.52/0.99  sup_time_sim_immed:                     0.
% 3.52/0.99  
% 3.52/0.99  sup_num_of_clauses:                     199
% 3.52/0.99  sup_num_in_active:                      124
% 3.52/0.99  sup_num_in_passive:                     75
% 3.52/0.99  sup_num_of_loops:                       124
% 3.52/0.99  sup_fw_superposition:                   164
% 3.52/0.99  sup_bw_superposition:                   52
% 3.52/0.99  sup_immediate_simplified:               32
% 3.52/0.99  sup_given_eliminated:                   0
% 3.52/0.99  comparisons_done:                       0
% 3.52/0.99  comparisons_avoided:                    0
% 3.52/0.99  
% 3.52/0.99  ------ Simplifications
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  sim_fw_subset_subsumed:                 13
% 3.52/0.99  sim_bw_subset_subsumed:                 0
% 3.52/0.99  sim_fw_subsumed:                        1
% 3.52/0.99  sim_bw_subsumed:                        0
% 3.52/0.99  sim_fw_subsumption_res:                 7
% 3.52/0.99  sim_bw_subsumption_res:                 0
% 3.52/0.99  sim_tautology_del:                      0
% 3.52/0.99  sim_eq_tautology_del:                   14
% 3.52/0.99  sim_eq_res_simp:                        1
% 3.52/0.99  sim_fw_demodulated:                     10
% 3.52/0.99  sim_bw_demodulated:                     1
% 3.52/0.99  sim_light_normalised:                   14
% 3.52/0.99  sim_joinable_taut:                      0
% 3.52/0.99  sim_joinable_simp:                      0
% 3.52/0.99  sim_ac_normalised:                      0
% 3.52/0.99  sim_smt_subsumption:                    0
% 3.52/0.99  
%------------------------------------------------------------------------------
