%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:39 EST 2020

% Result     : Theorem 16.05s
% Output     : CNFRefutation 16.05s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 621 expanded)
%              Number of clauses        :   60 ( 241 expanded)
%              Number of leaves         :   11 ( 119 expanded)
%              Depth                    :   19
%              Number of atoms          :  247 (1988 expanded)
%              Number of equality atoms :  100 ( 595 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f25])).

fof(f42,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_543,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_188,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
    | k6_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_189,plain,
    ( ~ r1_tarski(X0,k2_relat_1(k6_relat_1(X1)))
    | ~ v1_relat_1(k6_relat_1(X1))
    | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_9,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_199,plain,
    ( ~ r1_tarski(X0,k2_relat_1(k6_relat_1(X1)))
    | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_189,c_9])).

cnf(c_540,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1
    | r1_tarski(X1,k2_relat_1(k6_relat_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_199])).

cnf(c_5,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_585,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_540,c_5])).

cnf(c_1774,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_543,c_585])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_542,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_546,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1058,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_542,c_546])).

cnf(c_545,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k5_relat_1(X1,X0),X2) = k9_relat_1(X0,k9_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_548,plain,
    ( k9_relat_1(k5_relat_1(X0,X1),X2) = k9_relat_1(X1,k9_relat_1(X0,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2048,plain,
    ( k9_relat_1(X0,k9_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_545,c_548])).

cnf(c_27864,plain,
    ( k9_relat_1(k5_relat_1(k6_relat_1(X0),sK1),X1) = k9_relat_1(sK1,k9_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_542,c_2048])).

cnf(c_28528,plain,
    ( k9_relat_1(sK1,k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1058,c_27864])).

cnf(c_28561,plain,
    ( k9_relat_1(sK1,k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)) = k9_relat_1(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_1774,c_28528])).

cnf(c_11,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_171,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_172,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_171])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_176,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_172,c_17,c_16])).

cnf(c_541,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_176])).

cnf(c_29389,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_28561,c_541])).

cnf(c_12,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,X2),k9_relat_1(X2,X1)))
    | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_544,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,X2),k9_relat_1(X2,X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X2)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1066,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK1))),k1_relat_1(sK1)) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1058,c_544])).

cnf(c_1067,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1066,c_5])).

cnf(c_18,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1188,plain,
    ( v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1067,c_18])).

cnf(c_1189,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1188])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_549,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1197,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1189,c_545,c_549])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_550,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1959,plain,
    ( k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) = k10_relat_1(sK1,k9_relat_1(sK1,X0))
    | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_550])).

cnf(c_29757,plain,
    ( k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_29389,c_1959])).

cnf(c_37816,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k9_relat_1(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_29757,c_28561])).

cnf(c_4,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_547,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1772,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(X0)),k10_relat_1(k6_relat_1(k1_relat_1(X0)),k10_relat_1(X0,X1))) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_547,c_585])).

cnf(c_4005,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(sK1,X0))) = k10_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_542,c_1772])).

cnf(c_28564,plain,
    ( k9_relat_1(sK1,k10_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(sK1,X0))) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_4005,c_28528])).

cnf(c_29918,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))),k10_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(sK1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_28564,c_541])).

cnf(c_30317,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_29918,c_1959])).

cnf(c_44528,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) = k10_relat_1(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_30317,c_4005])).

cnf(c_45357,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_37816,c_44528])).

cnf(c_37837,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = sK0 ),
    inference(demodulation,[status(thm)],[c_29757,c_1774])).

cnf(c_45548,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_45357,c_37837])).

cnf(c_13,negated_conjecture,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_45548,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 16.05/2.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.05/2.51  
% 16.05/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 16.05/2.51  
% 16.05/2.51  ------  iProver source info
% 16.05/2.51  
% 16.05/2.51  git: date: 2020-06-30 10:37:57 +0100
% 16.05/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 16.05/2.51  git: non_committed_changes: false
% 16.05/2.51  git: last_make_outside_of_git: false
% 16.05/2.51  
% 16.05/2.51  ------ 
% 16.05/2.51  
% 16.05/2.51  ------ Input Options
% 16.05/2.51  
% 16.05/2.51  --out_options                           all
% 16.05/2.51  --tptp_safe_out                         true
% 16.05/2.51  --problem_path                          ""
% 16.05/2.51  --include_path                          ""
% 16.05/2.51  --clausifier                            res/vclausify_rel
% 16.05/2.51  --clausifier_options                    --mode clausify
% 16.05/2.51  --stdin                                 false
% 16.05/2.51  --stats_out                             all
% 16.05/2.51  
% 16.05/2.51  ------ General Options
% 16.05/2.51  
% 16.05/2.51  --fof                                   false
% 16.05/2.51  --time_out_real                         305.
% 16.05/2.51  --time_out_virtual                      -1.
% 16.05/2.51  --symbol_type_check                     false
% 16.05/2.51  --clausify_out                          false
% 16.05/2.51  --sig_cnt_out                           false
% 16.05/2.51  --trig_cnt_out                          false
% 16.05/2.51  --trig_cnt_out_tolerance                1.
% 16.05/2.51  --trig_cnt_out_sk_spl                   false
% 16.05/2.51  --abstr_cl_out                          false
% 16.05/2.51  
% 16.05/2.51  ------ Global Options
% 16.05/2.51  
% 16.05/2.51  --schedule                              default
% 16.05/2.51  --add_important_lit                     false
% 16.05/2.51  --prop_solver_per_cl                    1000
% 16.05/2.51  --min_unsat_core                        false
% 16.05/2.51  --soft_assumptions                      false
% 16.05/2.51  --soft_lemma_size                       3
% 16.05/2.51  --prop_impl_unit_size                   0
% 16.05/2.51  --prop_impl_unit                        []
% 16.05/2.51  --share_sel_clauses                     true
% 16.05/2.51  --reset_solvers                         false
% 16.05/2.51  --bc_imp_inh                            [conj_cone]
% 16.05/2.51  --conj_cone_tolerance                   3.
% 16.05/2.51  --extra_neg_conj                        none
% 16.05/2.51  --large_theory_mode                     true
% 16.05/2.51  --prolific_symb_bound                   200
% 16.05/2.51  --lt_threshold                          2000
% 16.05/2.51  --clause_weak_htbl                      true
% 16.05/2.51  --gc_record_bc_elim                     false
% 16.05/2.51  
% 16.05/2.51  ------ Preprocessing Options
% 16.05/2.51  
% 16.05/2.51  --preprocessing_flag                    true
% 16.05/2.51  --time_out_prep_mult                    0.1
% 16.05/2.51  --splitting_mode                        input
% 16.05/2.51  --splitting_grd                         true
% 16.05/2.51  --splitting_cvd                         false
% 16.05/2.51  --splitting_cvd_svl                     false
% 16.05/2.51  --splitting_nvd                         32
% 16.05/2.51  --sub_typing                            true
% 16.05/2.51  --prep_gs_sim                           true
% 16.05/2.51  --prep_unflatten                        true
% 16.05/2.51  --prep_res_sim                          true
% 16.05/2.51  --prep_upred                            true
% 16.05/2.51  --prep_sem_filter                       exhaustive
% 16.05/2.51  --prep_sem_filter_out                   false
% 16.05/2.51  --pred_elim                             true
% 16.05/2.51  --res_sim_input                         true
% 16.05/2.51  --eq_ax_congr_red                       true
% 16.05/2.51  --pure_diseq_elim                       true
% 16.05/2.51  --brand_transform                       false
% 16.05/2.51  --non_eq_to_eq                          false
% 16.05/2.51  --prep_def_merge                        true
% 16.05/2.51  --prep_def_merge_prop_impl              false
% 16.05/2.51  --prep_def_merge_mbd                    true
% 16.05/2.51  --prep_def_merge_tr_red                 false
% 16.05/2.51  --prep_def_merge_tr_cl                  false
% 16.05/2.51  --smt_preprocessing                     true
% 16.05/2.51  --smt_ac_axioms                         fast
% 16.05/2.51  --preprocessed_out                      false
% 16.05/2.51  --preprocessed_stats                    false
% 16.05/2.51  
% 16.05/2.51  ------ Abstraction refinement Options
% 16.05/2.51  
% 16.05/2.51  --abstr_ref                             []
% 16.05/2.51  --abstr_ref_prep                        false
% 16.05/2.51  --abstr_ref_until_sat                   false
% 16.05/2.51  --abstr_ref_sig_restrict                funpre
% 16.05/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 16.05/2.51  --abstr_ref_under                       []
% 16.05/2.51  
% 16.05/2.51  ------ SAT Options
% 16.05/2.51  
% 16.05/2.51  --sat_mode                              false
% 16.05/2.51  --sat_fm_restart_options                ""
% 16.05/2.51  --sat_gr_def                            false
% 16.05/2.51  --sat_epr_types                         true
% 16.05/2.51  --sat_non_cyclic_types                  false
% 16.05/2.51  --sat_finite_models                     false
% 16.05/2.51  --sat_fm_lemmas                         false
% 16.05/2.51  --sat_fm_prep                           false
% 16.05/2.51  --sat_fm_uc_incr                        true
% 16.05/2.51  --sat_out_model                         small
% 16.05/2.51  --sat_out_clauses                       false
% 16.05/2.51  
% 16.05/2.51  ------ QBF Options
% 16.05/2.51  
% 16.05/2.51  --qbf_mode                              false
% 16.05/2.51  --qbf_elim_univ                         false
% 16.05/2.51  --qbf_dom_inst                          none
% 16.05/2.51  --qbf_dom_pre_inst                      false
% 16.05/2.51  --qbf_sk_in                             false
% 16.05/2.51  --qbf_pred_elim                         true
% 16.05/2.51  --qbf_split                             512
% 16.05/2.51  
% 16.05/2.51  ------ BMC1 Options
% 16.05/2.51  
% 16.05/2.51  --bmc1_incremental                      false
% 16.05/2.51  --bmc1_axioms                           reachable_all
% 16.05/2.51  --bmc1_min_bound                        0
% 16.05/2.51  --bmc1_max_bound                        -1
% 16.05/2.51  --bmc1_max_bound_default                -1
% 16.05/2.51  --bmc1_symbol_reachability              true
% 16.05/2.51  --bmc1_property_lemmas                  false
% 16.05/2.51  --bmc1_k_induction                      false
% 16.05/2.51  --bmc1_non_equiv_states                 false
% 16.05/2.51  --bmc1_deadlock                         false
% 16.05/2.51  --bmc1_ucm                              false
% 16.05/2.51  --bmc1_add_unsat_core                   none
% 16.05/2.51  --bmc1_unsat_core_children              false
% 16.05/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 16.05/2.51  --bmc1_out_stat                         full
% 16.05/2.51  --bmc1_ground_init                      false
% 16.05/2.51  --bmc1_pre_inst_next_state              false
% 16.05/2.51  --bmc1_pre_inst_state                   false
% 16.05/2.51  --bmc1_pre_inst_reach_state             false
% 16.05/2.51  --bmc1_out_unsat_core                   false
% 16.05/2.51  --bmc1_aig_witness_out                  false
% 16.05/2.51  --bmc1_verbose                          false
% 16.05/2.51  --bmc1_dump_clauses_tptp                false
% 16.05/2.51  --bmc1_dump_unsat_core_tptp             false
% 16.05/2.51  --bmc1_dump_file                        -
% 16.05/2.51  --bmc1_ucm_expand_uc_limit              128
% 16.05/2.51  --bmc1_ucm_n_expand_iterations          6
% 16.05/2.51  --bmc1_ucm_extend_mode                  1
% 16.05/2.51  --bmc1_ucm_init_mode                    2
% 16.05/2.51  --bmc1_ucm_cone_mode                    none
% 16.05/2.51  --bmc1_ucm_reduced_relation_type        0
% 16.05/2.51  --bmc1_ucm_relax_model                  4
% 16.05/2.51  --bmc1_ucm_full_tr_after_sat            true
% 16.05/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 16.05/2.51  --bmc1_ucm_layered_model                none
% 16.05/2.51  --bmc1_ucm_max_lemma_size               10
% 16.05/2.51  
% 16.05/2.51  ------ AIG Options
% 16.05/2.51  
% 16.05/2.51  --aig_mode                              false
% 16.05/2.51  
% 16.05/2.51  ------ Instantiation Options
% 16.05/2.51  
% 16.05/2.51  --instantiation_flag                    true
% 16.05/2.51  --inst_sos_flag                         false
% 16.05/2.51  --inst_sos_phase                        true
% 16.05/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 16.05/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 16.05/2.51  --inst_lit_sel_side                     num_symb
% 16.05/2.51  --inst_solver_per_active                1400
% 16.05/2.51  --inst_solver_calls_frac                1.
% 16.05/2.51  --inst_passive_queue_type               priority_queues
% 16.05/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 16.05/2.51  --inst_passive_queues_freq              [25;2]
% 16.05/2.51  --inst_dismatching                      true
% 16.05/2.51  --inst_eager_unprocessed_to_passive     true
% 16.05/2.51  --inst_prop_sim_given                   true
% 16.05/2.51  --inst_prop_sim_new                     false
% 16.05/2.51  --inst_subs_new                         false
% 16.05/2.51  --inst_eq_res_simp                      false
% 16.05/2.51  --inst_subs_given                       false
% 16.05/2.51  --inst_orphan_elimination               true
% 16.05/2.51  --inst_learning_loop_flag               true
% 16.05/2.51  --inst_learning_start                   3000
% 16.05/2.51  --inst_learning_factor                  2
% 16.05/2.51  --inst_start_prop_sim_after_learn       3
% 16.05/2.51  --inst_sel_renew                        solver
% 16.05/2.51  --inst_lit_activity_flag                true
% 16.05/2.51  --inst_restr_to_given                   false
% 16.05/2.51  --inst_activity_threshold               500
% 16.05/2.51  --inst_out_proof                        true
% 16.05/2.51  
% 16.05/2.51  ------ Resolution Options
% 16.05/2.51  
% 16.05/2.51  --resolution_flag                       true
% 16.05/2.51  --res_lit_sel                           adaptive
% 16.05/2.51  --res_lit_sel_side                      none
% 16.05/2.51  --res_ordering                          kbo
% 16.05/2.51  --res_to_prop_solver                    active
% 16.05/2.51  --res_prop_simpl_new                    false
% 16.05/2.51  --res_prop_simpl_given                  true
% 16.05/2.51  --res_passive_queue_type                priority_queues
% 16.05/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 16.05/2.51  --res_passive_queues_freq               [15;5]
% 16.05/2.51  --res_forward_subs                      full
% 16.05/2.51  --res_backward_subs                     full
% 16.05/2.51  --res_forward_subs_resolution           true
% 16.05/2.51  --res_backward_subs_resolution          true
% 16.05/2.51  --res_orphan_elimination                true
% 16.05/2.51  --res_time_limit                        2.
% 16.05/2.51  --res_out_proof                         true
% 16.05/2.51  
% 16.05/2.51  ------ Superposition Options
% 16.05/2.51  
% 16.05/2.51  --superposition_flag                    true
% 16.05/2.51  --sup_passive_queue_type                priority_queues
% 16.05/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 16.05/2.51  --sup_passive_queues_freq               [8;1;4]
% 16.05/2.51  --demod_completeness_check              fast
% 16.05/2.51  --demod_use_ground                      true
% 16.05/2.51  --sup_to_prop_solver                    passive
% 16.05/2.51  --sup_prop_simpl_new                    true
% 16.05/2.51  --sup_prop_simpl_given                  true
% 16.05/2.51  --sup_fun_splitting                     false
% 16.05/2.51  --sup_smt_interval                      50000
% 16.05/2.51  
% 16.05/2.51  ------ Superposition Simplification Setup
% 16.05/2.51  
% 16.05/2.51  --sup_indices_passive                   []
% 16.05/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 16.05/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 16.05/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 16.05/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 16.05/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 16.05/2.51  --sup_full_bw                           [BwDemod]
% 16.05/2.51  --sup_immed_triv                        [TrivRules]
% 16.05/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 16.05/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 16.05/2.51  --sup_immed_bw_main                     []
% 16.05/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 16.05/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 16.05/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 16.05/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 16.05/2.51  
% 16.05/2.51  ------ Combination Options
% 16.05/2.51  
% 16.05/2.51  --comb_res_mult                         3
% 16.05/2.51  --comb_sup_mult                         2
% 16.05/2.51  --comb_inst_mult                        10
% 16.05/2.51  
% 16.05/2.51  ------ Debug Options
% 16.05/2.51  
% 16.05/2.51  --dbg_backtrace                         false
% 16.05/2.51  --dbg_dump_prop_clauses                 false
% 16.05/2.51  --dbg_dump_prop_clauses_file            -
% 16.05/2.51  --dbg_out_stat                          false
% 16.05/2.51  ------ Parsing...
% 16.05/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 16.05/2.51  
% 16.05/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 16.05/2.51  
% 16.05/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 16.05/2.51  
% 16.05/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 16.05/2.51  ------ Proving...
% 16.05/2.51  ------ Problem Properties 
% 16.05/2.51  
% 16.05/2.51  
% 16.05/2.51  clauses                                 15
% 16.05/2.51  conjectures                             3
% 16.05/2.51  EPR                                     3
% 16.05/2.51  Horn                                    15
% 16.05/2.51  unary                                   8
% 16.05/2.51  binary                                  4
% 16.05/2.51  lits                                    26
% 16.05/2.51  lits eq                                 8
% 16.05/2.51  fd_pure                                 0
% 16.05/2.51  fd_pseudo                               0
% 16.05/2.51  fd_cond                                 0
% 16.05/2.51  fd_pseudo_cond                          1
% 16.05/2.51  AC symbols                              0
% 16.05/2.51  
% 16.05/2.51  ------ Schedule dynamic 5 is on 
% 16.05/2.51  
% 16.05/2.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 16.05/2.51  
% 16.05/2.51  
% 16.05/2.51  ------ 
% 16.05/2.51  Current options:
% 16.05/2.51  ------ 
% 16.05/2.51  
% 16.05/2.51  ------ Input Options
% 16.05/2.51  
% 16.05/2.51  --out_options                           all
% 16.05/2.51  --tptp_safe_out                         true
% 16.05/2.51  --problem_path                          ""
% 16.05/2.51  --include_path                          ""
% 16.05/2.51  --clausifier                            res/vclausify_rel
% 16.05/2.51  --clausifier_options                    --mode clausify
% 16.05/2.51  --stdin                                 false
% 16.05/2.51  --stats_out                             all
% 16.05/2.51  
% 16.05/2.51  ------ General Options
% 16.05/2.51  
% 16.05/2.51  --fof                                   false
% 16.05/2.51  --time_out_real                         305.
% 16.05/2.51  --time_out_virtual                      -1.
% 16.05/2.51  --symbol_type_check                     false
% 16.05/2.51  --clausify_out                          false
% 16.05/2.51  --sig_cnt_out                           false
% 16.05/2.51  --trig_cnt_out                          false
% 16.05/2.51  --trig_cnt_out_tolerance                1.
% 16.05/2.51  --trig_cnt_out_sk_spl                   false
% 16.05/2.51  --abstr_cl_out                          false
% 16.05/2.51  
% 16.05/2.51  ------ Global Options
% 16.05/2.51  
% 16.05/2.51  --schedule                              default
% 16.05/2.51  --add_important_lit                     false
% 16.05/2.51  --prop_solver_per_cl                    1000
% 16.05/2.51  --min_unsat_core                        false
% 16.05/2.51  --soft_assumptions                      false
% 16.05/2.51  --soft_lemma_size                       3
% 16.05/2.51  --prop_impl_unit_size                   0
% 16.05/2.51  --prop_impl_unit                        []
% 16.05/2.51  --share_sel_clauses                     true
% 16.05/2.51  --reset_solvers                         false
% 16.05/2.51  --bc_imp_inh                            [conj_cone]
% 16.05/2.51  --conj_cone_tolerance                   3.
% 16.05/2.51  --extra_neg_conj                        none
% 16.05/2.51  --large_theory_mode                     true
% 16.05/2.51  --prolific_symb_bound                   200
% 16.05/2.51  --lt_threshold                          2000
% 16.05/2.51  --clause_weak_htbl                      true
% 16.05/2.51  --gc_record_bc_elim                     false
% 16.05/2.51  
% 16.05/2.51  ------ Preprocessing Options
% 16.05/2.51  
% 16.05/2.51  --preprocessing_flag                    true
% 16.05/2.51  --time_out_prep_mult                    0.1
% 16.05/2.51  --splitting_mode                        input
% 16.05/2.51  --splitting_grd                         true
% 16.05/2.51  --splitting_cvd                         false
% 16.05/2.51  --splitting_cvd_svl                     false
% 16.05/2.51  --splitting_nvd                         32
% 16.05/2.51  --sub_typing                            true
% 16.05/2.51  --prep_gs_sim                           true
% 16.05/2.51  --prep_unflatten                        true
% 16.05/2.51  --prep_res_sim                          true
% 16.05/2.51  --prep_upred                            true
% 16.05/2.51  --prep_sem_filter                       exhaustive
% 16.05/2.51  --prep_sem_filter_out                   false
% 16.05/2.51  --pred_elim                             true
% 16.05/2.51  --res_sim_input                         true
% 16.05/2.51  --eq_ax_congr_red                       true
% 16.05/2.51  --pure_diseq_elim                       true
% 16.05/2.51  --brand_transform                       false
% 16.05/2.51  --non_eq_to_eq                          false
% 16.05/2.51  --prep_def_merge                        true
% 16.05/2.51  --prep_def_merge_prop_impl              false
% 16.05/2.51  --prep_def_merge_mbd                    true
% 16.05/2.51  --prep_def_merge_tr_red                 false
% 16.05/2.51  --prep_def_merge_tr_cl                  false
% 16.05/2.51  --smt_preprocessing                     true
% 16.05/2.51  --smt_ac_axioms                         fast
% 16.05/2.51  --preprocessed_out                      false
% 16.05/2.51  --preprocessed_stats                    false
% 16.05/2.51  
% 16.05/2.51  ------ Abstraction refinement Options
% 16.05/2.51  
% 16.05/2.51  --abstr_ref                             []
% 16.05/2.51  --abstr_ref_prep                        false
% 16.05/2.51  --abstr_ref_until_sat                   false
% 16.05/2.51  --abstr_ref_sig_restrict                funpre
% 16.05/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 16.05/2.51  --abstr_ref_under                       []
% 16.05/2.51  
% 16.05/2.51  ------ SAT Options
% 16.05/2.51  
% 16.05/2.51  --sat_mode                              false
% 16.05/2.51  --sat_fm_restart_options                ""
% 16.05/2.51  --sat_gr_def                            false
% 16.05/2.51  --sat_epr_types                         true
% 16.05/2.51  --sat_non_cyclic_types                  false
% 16.05/2.51  --sat_finite_models                     false
% 16.05/2.51  --sat_fm_lemmas                         false
% 16.05/2.51  --sat_fm_prep                           false
% 16.05/2.51  --sat_fm_uc_incr                        true
% 16.05/2.51  --sat_out_model                         small
% 16.05/2.51  --sat_out_clauses                       false
% 16.05/2.51  
% 16.05/2.51  ------ QBF Options
% 16.05/2.51  
% 16.05/2.51  --qbf_mode                              false
% 16.05/2.51  --qbf_elim_univ                         false
% 16.05/2.51  --qbf_dom_inst                          none
% 16.05/2.51  --qbf_dom_pre_inst                      false
% 16.05/2.51  --qbf_sk_in                             false
% 16.05/2.51  --qbf_pred_elim                         true
% 16.05/2.51  --qbf_split                             512
% 16.05/2.51  
% 16.05/2.51  ------ BMC1 Options
% 16.05/2.51  
% 16.05/2.51  --bmc1_incremental                      false
% 16.05/2.51  --bmc1_axioms                           reachable_all
% 16.05/2.51  --bmc1_min_bound                        0
% 16.05/2.51  --bmc1_max_bound                        -1
% 16.05/2.51  --bmc1_max_bound_default                -1
% 16.05/2.51  --bmc1_symbol_reachability              true
% 16.05/2.51  --bmc1_property_lemmas                  false
% 16.05/2.51  --bmc1_k_induction                      false
% 16.05/2.51  --bmc1_non_equiv_states                 false
% 16.05/2.51  --bmc1_deadlock                         false
% 16.05/2.51  --bmc1_ucm                              false
% 16.05/2.51  --bmc1_add_unsat_core                   none
% 16.05/2.51  --bmc1_unsat_core_children              false
% 16.05/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 16.05/2.51  --bmc1_out_stat                         full
% 16.05/2.51  --bmc1_ground_init                      false
% 16.05/2.51  --bmc1_pre_inst_next_state              false
% 16.05/2.51  --bmc1_pre_inst_state                   false
% 16.05/2.51  --bmc1_pre_inst_reach_state             false
% 16.05/2.51  --bmc1_out_unsat_core                   false
% 16.05/2.51  --bmc1_aig_witness_out                  false
% 16.05/2.51  --bmc1_verbose                          false
% 16.05/2.51  --bmc1_dump_clauses_tptp                false
% 16.05/2.51  --bmc1_dump_unsat_core_tptp             false
% 16.05/2.51  --bmc1_dump_file                        -
% 16.05/2.51  --bmc1_ucm_expand_uc_limit              128
% 16.05/2.51  --bmc1_ucm_n_expand_iterations          6
% 16.05/2.51  --bmc1_ucm_extend_mode                  1
% 16.05/2.51  --bmc1_ucm_init_mode                    2
% 16.05/2.51  --bmc1_ucm_cone_mode                    none
% 16.05/2.51  --bmc1_ucm_reduced_relation_type        0
% 16.05/2.51  --bmc1_ucm_relax_model                  4
% 16.05/2.51  --bmc1_ucm_full_tr_after_sat            true
% 16.05/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 16.05/2.51  --bmc1_ucm_layered_model                none
% 16.05/2.51  --bmc1_ucm_max_lemma_size               10
% 16.05/2.51  
% 16.05/2.51  ------ AIG Options
% 16.05/2.51  
% 16.05/2.51  --aig_mode                              false
% 16.05/2.51  
% 16.05/2.51  ------ Instantiation Options
% 16.05/2.51  
% 16.05/2.51  --instantiation_flag                    true
% 16.05/2.51  --inst_sos_flag                         false
% 16.05/2.51  --inst_sos_phase                        true
% 16.05/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 16.05/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 16.05/2.51  --inst_lit_sel_side                     none
% 16.05/2.51  --inst_solver_per_active                1400
% 16.05/2.51  --inst_solver_calls_frac                1.
% 16.05/2.51  --inst_passive_queue_type               priority_queues
% 16.05/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 16.05/2.51  --inst_passive_queues_freq              [25;2]
% 16.05/2.51  --inst_dismatching                      true
% 16.05/2.51  --inst_eager_unprocessed_to_passive     true
% 16.05/2.51  --inst_prop_sim_given                   true
% 16.05/2.51  --inst_prop_sim_new                     false
% 16.05/2.51  --inst_subs_new                         false
% 16.05/2.51  --inst_eq_res_simp                      false
% 16.05/2.51  --inst_subs_given                       false
% 16.05/2.51  --inst_orphan_elimination               true
% 16.05/2.51  --inst_learning_loop_flag               true
% 16.05/2.51  --inst_learning_start                   3000
% 16.05/2.51  --inst_learning_factor                  2
% 16.05/2.51  --inst_start_prop_sim_after_learn       3
% 16.05/2.51  --inst_sel_renew                        solver
% 16.05/2.51  --inst_lit_activity_flag                true
% 16.05/2.51  --inst_restr_to_given                   false
% 16.05/2.51  --inst_activity_threshold               500
% 16.05/2.51  --inst_out_proof                        true
% 16.05/2.51  
% 16.05/2.51  ------ Resolution Options
% 16.05/2.51  
% 16.05/2.51  --resolution_flag                       false
% 16.05/2.51  --res_lit_sel                           adaptive
% 16.05/2.51  --res_lit_sel_side                      none
% 16.05/2.51  --res_ordering                          kbo
% 16.05/2.51  --res_to_prop_solver                    active
% 16.05/2.51  --res_prop_simpl_new                    false
% 16.05/2.51  --res_prop_simpl_given                  true
% 16.05/2.51  --res_passive_queue_type                priority_queues
% 16.05/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 16.05/2.51  --res_passive_queues_freq               [15;5]
% 16.05/2.51  --res_forward_subs                      full
% 16.05/2.51  --res_backward_subs                     full
% 16.05/2.51  --res_forward_subs_resolution           true
% 16.05/2.51  --res_backward_subs_resolution          true
% 16.05/2.51  --res_orphan_elimination                true
% 16.05/2.51  --res_time_limit                        2.
% 16.05/2.51  --res_out_proof                         true
% 16.05/2.51  
% 16.05/2.51  ------ Superposition Options
% 16.05/2.51  
% 16.05/2.51  --superposition_flag                    true
% 16.05/2.51  --sup_passive_queue_type                priority_queues
% 16.05/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 16.05/2.51  --sup_passive_queues_freq               [8;1;4]
% 16.05/2.51  --demod_completeness_check              fast
% 16.05/2.51  --demod_use_ground                      true
% 16.05/2.51  --sup_to_prop_solver                    passive
% 16.05/2.51  --sup_prop_simpl_new                    true
% 16.05/2.51  --sup_prop_simpl_given                  true
% 16.05/2.51  --sup_fun_splitting                     false
% 16.05/2.51  --sup_smt_interval                      50000
% 16.05/2.51  
% 16.05/2.51  ------ Superposition Simplification Setup
% 16.05/2.51  
% 16.05/2.51  --sup_indices_passive                   []
% 16.05/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 16.05/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 16.05/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 16.05/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 16.05/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 16.05/2.51  --sup_full_bw                           [BwDemod]
% 16.05/2.51  --sup_immed_triv                        [TrivRules]
% 16.05/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 16.05/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 16.05/2.51  --sup_immed_bw_main                     []
% 16.05/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 16.05/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 16.05/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 16.05/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 16.05/2.51  
% 16.05/2.51  ------ Combination Options
% 16.05/2.51  
% 16.05/2.51  --comb_res_mult                         3
% 16.05/2.51  --comb_sup_mult                         2
% 16.05/2.51  --comb_inst_mult                        10
% 16.05/2.51  
% 16.05/2.51  ------ Debug Options
% 16.05/2.51  
% 16.05/2.51  --dbg_backtrace                         false
% 16.05/2.51  --dbg_dump_prop_clauses                 false
% 16.05/2.51  --dbg_dump_prop_clauses_file            -
% 16.05/2.51  --dbg_out_stat                          false
% 16.05/2.51  
% 16.05/2.51  
% 16.05/2.51  
% 16.05/2.51  
% 16.05/2.51  ------ Proving...
% 16.05/2.51  
% 16.05/2.51  
% 16.05/2.51  % SZS status Theorem for theBenchmark.p
% 16.05/2.51  
% 16.05/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 16.05/2.51  
% 16.05/2.51  fof(f10,conjecture,(
% 16.05/2.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 16.05/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.05/2.51  
% 16.05/2.51  fof(f11,negated_conjecture,(
% 16.05/2.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 16.05/2.51    inference(negated_conjecture,[],[f10])).
% 16.05/2.51  
% 16.05/2.51  fof(f21,plain,(
% 16.05/2.51    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 16.05/2.51    inference(ennf_transformation,[],[f11])).
% 16.05/2.51  
% 16.05/2.51  fof(f22,plain,(
% 16.05/2.51    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 16.05/2.51    inference(flattening,[],[f21])).
% 16.05/2.51  
% 16.05/2.51  fof(f25,plain,(
% 16.05/2.51    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 16.05/2.51    introduced(choice_axiom,[])).
% 16.05/2.51  
% 16.05/2.51  fof(f26,plain,(
% 16.05/2.51    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 16.05/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f25])).
% 16.05/2.51  
% 16.05/2.51  fof(f42,plain,(
% 16.05/2.51    r1_tarski(sK0,k1_relat_1(sK1))),
% 16.05/2.51    inference(cnf_transformation,[],[f26])).
% 16.05/2.51  
% 16.05/2.51  fof(f6,axiom,(
% 16.05/2.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 16.05/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.05/2.51  
% 16.05/2.51  fof(f36,plain,(
% 16.05/2.51    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 16.05/2.51    inference(cnf_transformation,[],[f6])).
% 16.05/2.51  
% 16.05/2.51  fof(f7,axiom,(
% 16.05/2.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 16.05/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.05/2.51  
% 16.05/2.51  fof(f15,plain,(
% 16.05/2.51    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 16.05/2.51    inference(ennf_transformation,[],[f7])).
% 16.05/2.51  
% 16.05/2.51  fof(f16,plain,(
% 16.05/2.51    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 16.05/2.51    inference(flattening,[],[f15])).
% 16.05/2.51  
% 16.05/2.51  fof(f37,plain,(
% 16.05/2.51    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 16.05/2.51    inference(cnf_transformation,[],[f16])).
% 16.05/2.51  
% 16.05/2.51  fof(f35,plain,(
% 16.05/2.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 16.05/2.51    inference(cnf_transformation,[],[f6])).
% 16.05/2.51  
% 16.05/2.51  fof(f4,axiom,(
% 16.05/2.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 16.05/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.05/2.51  
% 16.05/2.51  fof(f33,plain,(
% 16.05/2.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 16.05/2.51    inference(cnf_transformation,[],[f4])).
% 16.05/2.51  
% 16.05/2.51  fof(f40,plain,(
% 16.05/2.51    v1_relat_1(sK1)),
% 16.05/2.51    inference(cnf_transformation,[],[f26])).
% 16.05/2.51  
% 16.05/2.51  fof(f5,axiom,(
% 16.05/2.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 16.05/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.05/2.51  
% 16.05/2.51  fof(f14,plain,(
% 16.05/2.51    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 16.05/2.51    inference(ennf_transformation,[],[f5])).
% 16.05/2.51  
% 16.05/2.51  fof(f34,plain,(
% 16.05/2.51    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 16.05/2.51    inference(cnf_transformation,[],[f14])).
% 16.05/2.51  
% 16.05/2.51  fof(f2,axiom,(
% 16.05/2.51    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0)))),
% 16.05/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.05/2.51  
% 16.05/2.51  fof(f12,plain,(
% 16.05/2.51    ! [X0,X1] : (! [X2] : (k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 16.05/2.51    inference(ennf_transformation,[],[f2])).
% 16.05/2.51  
% 16.05/2.51  fof(f30,plain,(
% 16.05/2.51    ( ! [X2,X0,X1] : (k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 16.05/2.51    inference(cnf_transformation,[],[f12])).
% 16.05/2.51  
% 16.05/2.51  fof(f8,axiom,(
% 16.05/2.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 16.05/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.05/2.51  
% 16.05/2.51  fof(f17,plain,(
% 16.05/2.51    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 16.05/2.51    inference(ennf_transformation,[],[f8])).
% 16.05/2.51  
% 16.05/2.51  fof(f18,plain,(
% 16.05/2.51    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 16.05/2.51    inference(flattening,[],[f17])).
% 16.05/2.51  
% 16.05/2.51  fof(f38,plain,(
% 16.05/2.51    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 16.05/2.51    inference(cnf_transformation,[],[f18])).
% 16.05/2.51  
% 16.05/2.51  fof(f43,plain,(
% 16.05/2.51    v2_funct_1(sK1)),
% 16.05/2.51    inference(cnf_transformation,[],[f26])).
% 16.05/2.51  
% 16.05/2.51  fof(f41,plain,(
% 16.05/2.51    v1_funct_1(sK1)),
% 16.05/2.51    inference(cnf_transformation,[],[f26])).
% 16.05/2.51  
% 16.05/2.51  fof(f9,axiom,(
% 16.05/2.51    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))))))),
% 16.05/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.05/2.51  
% 16.05/2.51  fof(f19,plain,(
% 16.05/2.51    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 16.05/2.51    inference(ennf_transformation,[],[f9])).
% 16.05/2.51  
% 16.05/2.51  fof(f20,plain,(
% 16.05/2.51    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 16.05/2.51    inference(flattening,[],[f19])).
% 16.05/2.51  
% 16.05/2.51  fof(f39,plain,(
% 16.05/2.51    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 16.05/2.51    inference(cnf_transformation,[],[f20])).
% 16.05/2.51  
% 16.05/2.51  fof(f1,axiom,(
% 16.05/2.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 16.05/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.05/2.51  
% 16.05/2.51  fof(f23,plain,(
% 16.05/2.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 16.05/2.51    inference(nnf_transformation,[],[f1])).
% 16.05/2.51  
% 16.05/2.51  fof(f24,plain,(
% 16.05/2.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 16.05/2.51    inference(flattening,[],[f23])).
% 16.05/2.51  
% 16.05/2.51  fof(f28,plain,(
% 16.05/2.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 16.05/2.51    inference(cnf_transformation,[],[f24])).
% 16.05/2.51  
% 16.05/2.51  fof(f45,plain,(
% 16.05/2.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 16.05/2.51    inference(equality_resolution,[],[f28])).
% 16.05/2.51  
% 16.05/2.51  fof(f29,plain,(
% 16.05/2.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 16.05/2.51    inference(cnf_transformation,[],[f24])).
% 16.05/2.51  
% 16.05/2.51  fof(f3,axiom,(
% 16.05/2.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 16.05/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 16.05/2.51  
% 16.05/2.51  fof(f13,plain,(
% 16.05/2.51    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 16.05/2.51    inference(ennf_transformation,[],[f3])).
% 16.05/2.51  
% 16.05/2.51  fof(f31,plain,(
% 16.05/2.51    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 16.05/2.51    inference(cnf_transformation,[],[f13])).
% 16.05/2.51  
% 16.05/2.51  fof(f44,plain,(
% 16.05/2.51    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0),
% 16.05/2.51    inference(cnf_transformation,[],[f26])).
% 16.05/2.51  
% 16.05/2.51  cnf(c_15,negated_conjecture,
% 16.05/2.51      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 16.05/2.51      inference(cnf_transformation,[],[f42]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_543,plain,
% 16.05/2.51      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 16.05/2.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_8,plain,
% 16.05/2.51      ( v1_funct_1(k6_relat_1(X0)) ),
% 16.05/2.51      inference(cnf_transformation,[],[f36]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_10,plain,
% 16.05/2.51      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 16.05/2.51      | ~ v1_funct_1(X1)
% 16.05/2.51      | ~ v1_relat_1(X1)
% 16.05/2.51      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 16.05/2.51      inference(cnf_transformation,[],[f37]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_188,plain,
% 16.05/2.51      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 16.05/2.51      | ~ v1_relat_1(X1)
% 16.05/2.51      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
% 16.05/2.51      | k6_relat_1(X2) != X1 ),
% 16.05/2.51      inference(resolution_lifted,[status(thm)],[c_8,c_10]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_189,plain,
% 16.05/2.51      ( ~ r1_tarski(X0,k2_relat_1(k6_relat_1(X1)))
% 16.05/2.51      | ~ v1_relat_1(k6_relat_1(X1))
% 16.05/2.51      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 ),
% 16.05/2.51      inference(unflattening,[status(thm)],[c_188]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_9,plain,
% 16.05/2.51      ( v1_relat_1(k6_relat_1(X0)) ),
% 16.05/2.51      inference(cnf_transformation,[],[f35]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_199,plain,
% 16.05/2.51      ( ~ r1_tarski(X0,k2_relat_1(k6_relat_1(X1)))
% 16.05/2.51      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 ),
% 16.05/2.51      inference(forward_subsumption_resolution,[status(thm)],[c_189,c_9]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_540,plain,
% 16.05/2.51      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1
% 16.05/2.51      | r1_tarski(X1,k2_relat_1(k6_relat_1(X0))) != iProver_top ),
% 16.05/2.51      inference(predicate_to_equality,[status(thm)],[c_199]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_5,plain,
% 16.05/2.51      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 16.05/2.51      inference(cnf_transformation,[],[f33]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_585,plain,
% 16.05/2.51      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1
% 16.05/2.51      | r1_tarski(X1,X0) != iProver_top ),
% 16.05/2.51      inference(light_normalisation,[status(thm)],[c_540,c_5]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_1774,plain,
% 16.05/2.51      ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)) = sK0 ),
% 16.05/2.51      inference(superposition,[status(thm)],[c_543,c_585]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_17,negated_conjecture,
% 16.05/2.51      ( v1_relat_1(sK1) ),
% 16.05/2.51      inference(cnf_transformation,[],[f40]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_542,plain,
% 16.05/2.51      ( v1_relat_1(sK1) = iProver_top ),
% 16.05/2.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_7,plain,
% 16.05/2.51      ( ~ v1_relat_1(X0)
% 16.05/2.51      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
% 16.05/2.51      inference(cnf_transformation,[],[f34]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_546,plain,
% 16.05/2.51      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 16.05/2.51      | v1_relat_1(X0) != iProver_top ),
% 16.05/2.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_1058,plain,
% 16.05/2.51      ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = sK1 ),
% 16.05/2.51      inference(superposition,[status(thm)],[c_542,c_546]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_545,plain,
% 16.05/2.51      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 16.05/2.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_3,plain,
% 16.05/2.51      ( ~ v1_relat_1(X0)
% 16.05/2.51      | ~ v1_relat_1(X1)
% 16.05/2.51      | k9_relat_1(k5_relat_1(X1,X0),X2) = k9_relat_1(X0,k9_relat_1(X1,X2)) ),
% 16.05/2.51      inference(cnf_transformation,[],[f30]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_548,plain,
% 16.05/2.51      ( k9_relat_1(k5_relat_1(X0,X1),X2) = k9_relat_1(X1,k9_relat_1(X0,X2))
% 16.05/2.51      | v1_relat_1(X1) != iProver_top
% 16.05/2.51      | v1_relat_1(X0) != iProver_top ),
% 16.05/2.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_2048,plain,
% 16.05/2.51      ( k9_relat_1(X0,k9_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2)
% 16.05/2.51      | v1_relat_1(X0) != iProver_top ),
% 16.05/2.51      inference(superposition,[status(thm)],[c_545,c_548]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_27864,plain,
% 16.05/2.51      ( k9_relat_1(k5_relat_1(k6_relat_1(X0),sK1),X1) = k9_relat_1(sK1,k9_relat_1(k6_relat_1(X0),X1)) ),
% 16.05/2.51      inference(superposition,[status(thm)],[c_542,c_2048]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_28528,plain,
% 16.05/2.51      ( k9_relat_1(sK1,k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)) = k9_relat_1(sK1,X0) ),
% 16.05/2.51      inference(superposition,[status(thm)],[c_1058,c_27864]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_28561,plain,
% 16.05/2.51      ( k9_relat_1(sK1,k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)) = k9_relat_1(sK1,sK0) ),
% 16.05/2.51      inference(superposition,[status(thm)],[c_1774,c_28528]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_11,plain,
% 16.05/2.51      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 16.05/2.51      | ~ v2_funct_1(X0)
% 16.05/2.51      | ~ v1_funct_1(X0)
% 16.05/2.51      | ~ v1_relat_1(X0) ),
% 16.05/2.51      inference(cnf_transformation,[],[f38]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_14,negated_conjecture,
% 16.05/2.51      ( v2_funct_1(sK1) ),
% 16.05/2.51      inference(cnf_transformation,[],[f43]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_171,plain,
% 16.05/2.51      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 16.05/2.51      | ~ v1_funct_1(X0)
% 16.05/2.51      | ~ v1_relat_1(X0)
% 16.05/2.51      | sK1 != X0 ),
% 16.05/2.51      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_172,plain,
% 16.05/2.51      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
% 16.05/2.51      | ~ v1_funct_1(sK1)
% 16.05/2.51      | ~ v1_relat_1(sK1) ),
% 16.05/2.51      inference(unflattening,[status(thm)],[c_171]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_16,negated_conjecture,
% 16.05/2.51      ( v1_funct_1(sK1) ),
% 16.05/2.51      inference(cnf_transformation,[],[f41]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_176,plain,
% 16.05/2.51      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
% 16.05/2.51      inference(global_propositional_subsumption,
% 16.05/2.51                [status(thm)],
% 16.05/2.51                [c_172,c_17,c_16]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_541,plain,
% 16.05/2.51      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = iProver_top ),
% 16.05/2.51      inference(predicate_to_equality,[status(thm)],[c_176]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_29389,plain,
% 16.05/2.51      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)) = iProver_top ),
% 16.05/2.51      inference(superposition,[status(thm)],[c_28561,c_541]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_12,plain,
% 16.05/2.51      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,X2),k9_relat_1(X2,X1)))
% 16.05/2.51      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X2))
% 16.05/2.51      | ~ v1_relat_1(X2)
% 16.05/2.51      | ~ v1_relat_1(X0) ),
% 16.05/2.51      inference(cnf_transformation,[],[f39]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_544,plain,
% 16.05/2.51      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,X2),k9_relat_1(X2,X1))) = iProver_top
% 16.05/2.51      | r1_tarski(k2_relat_1(X0),k1_relat_1(X2)) != iProver_top
% 16.05/2.51      | v1_relat_1(X2) != iProver_top
% 16.05/2.51      | v1_relat_1(X0) != iProver_top ),
% 16.05/2.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_1066,plain,
% 16.05/2.51      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
% 16.05/2.51      | r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK1))),k1_relat_1(sK1)) != iProver_top
% 16.05/2.51      | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
% 16.05/2.51      | v1_relat_1(sK1) != iProver_top ),
% 16.05/2.51      inference(superposition,[status(thm)],[c_1058,c_544]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_1067,plain,
% 16.05/2.51      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
% 16.05/2.51      | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
% 16.05/2.51      | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
% 16.05/2.51      | v1_relat_1(sK1) != iProver_top ),
% 16.05/2.51      inference(demodulation,[status(thm)],[c_1066,c_5]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_18,plain,
% 16.05/2.51      ( v1_relat_1(sK1) = iProver_top ),
% 16.05/2.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_1188,plain,
% 16.05/2.51      ( v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
% 16.05/2.51      | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
% 16.05/2.51      | r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
% 16.05/2.51      inference(global_propositional_subsumption,
% 16.05/2.51                [status(thm)],
% 16.05/2.51                [c_1067,c_18]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_1189,plain,
% 16.05/2.51      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
% 16.05/2.51      | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
% 16.05/2.51      | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top ),
% 16.05/2.51      inference(renaming,[status(thm)],[c_1188]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_1,plain,
% 16.05/2.51      ( r1_tarski(X0,X0) ),
% 16.05/2.51      inference(cnf_transformation,[],[f45]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_549,plain,
% 16.05/2.51      ( r1_tarski(X0,X0) = iProver_top ),
% 16.05/2.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_1197,plain,
% 16.05/2.51      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
% 16.05/2.51      inference(forward_subsumption_resolution,
% 16.05/2.51                [status(thm)],
% 16.05/2.51                [c_1189,c_545,c_549]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_0,plain,
% 16.05/2.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 16.05/2.51      inference(cnf_transformation,[],[f29]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_550,plain,
% 16.05/2.51      ( X0 = X1
% 16.05/2.51      | r1_tarski(X0,X1) != iProver_top
% 16.05/2.51      | r1_tarski(X1,X0) != iProver_top ),
% 16.05/2.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_1959,plain,
% 16.05/2.51      ( k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) = k10_relat_1(sK1,k9_relat_1(sK1,X0))
% 16.05/2.51      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)) != iProver_top ),
% 16.05/2.51      inference(superposition,[status(thm)],[c_1197,c_550]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_29757,plain,
% 16.05/2.51      ( k10_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
% 16.05/2.51      inference(superposition,[status(thm)],[c_29389,c_1959]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_37816,plain,
% 16.05/2.51      ( k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k9_relat_1(sK1,sK0) ),
% 16.05/2.51      inference(demodulation,[status(thm)],[c_29757,c_28561]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_4,plain,
% 16.05/2.51      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 16.05/2.51      inference(cnf_transformation,[],[f31]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_547,plain,
% 16.05/2.51      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 16.05/2.51      | v1_relat_1(X0) != iProver_top ),
% 16.05/2.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_1772,plain,
% 16.05/2.51      ( k9_relat_1(k6_relat_1(k1_relat_1(X0)),k10_relat_1(k6_relat_1(k1_relat_1(X0)),k10_relat_1(X0,X1))) = k10_relat_1(X0,X1)
% 16.05/2.51      | v1_relat_1(X0) != iProver_top ),
% 16.05/2.51      inference(superposition,[status(thm)],[c_547,c_585]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_4005,plain,
% 16.05/2.51      ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(sK1,X0))) = k10_relat_1(sK1,X0) ),
% 16.05/2.51      inference(superposition,[status(thm)],[c_542,c_1772]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_28564,plain,
% 16.05/2.51      ( k9_relat_1(sK1,k10_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(sK1,X0))) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
% 16.05/2.51      inference(superposition,[status(thm)],[c_4005,c_28528]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_29918,plain,
% 16.05/2.51      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))),k10_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(sK1,X0))) = iProver_top ),
% 16.05/2.51      inference(superposition,[status(thm)],[c_28564,c_541]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_30317,plain,
% 16.05/2.51      ( k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(sK1,X0)) ),
% 16.05/2.51      inference(superposition,[status(thm)],[c_29918,c_1959]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_44528,plain,
% 16.05/2.51      ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) = k10_relat_1(sK1,X0) ),
% 16.05/2.51      inference(demodulation,[status(thm)],[c_30317,c_4005]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_45357,plain,
% 16.05/2.51      ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
% 16.05/2.51      inference(superposition,[status(thm)],[c_37816,c_44528]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_37837,plain,
% 16.05/2.51      ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = sK0 ),
% 16.05/2.51      inference(demodulation,[status(thm)],[c_29757,c_1774]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_45548,plain,
% 16.05/2.51      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
% 16.05/2.51      inference(light_normalisation,[status(thm)],[c_45357,c_37837]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(c_13,negated_conjecture,
% 16.05/2.51      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
% 16.05/2.51      inference(cnf_transformation,[],[f44]) ).
% 16.05/2.51  
% 16.05/2.51  cnf(contradiction,plain,
% 16.05/2.51      ( $false ),
% 16.05/2.51      inference(minisat,[status(thm)],[c_45548,c_13]) ).
% 16.05/2.51  
% 16.05/2.51  
% 16.05/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 16.05/2.51  
% 16.05/2.51  ------                               Statistics
% 16.05/2.51  
% 16.05/2.51  ------ General
% 16.05/2.51  
% 16.05/2.51  abstr_ref_over_cycles:                  0
% 16.05/2.51  abstr_ref_under_cycles:                 0
% 16.05/2.51  gc_basic_clause_elim:                   0
% 16.05/2.51  forced_gc_time:                         0
% 16.05/2.51  parsing_time:                           0.011
% 16.05/2.51  unif_index_cands_time:                  0.
% 16.05/2.51  unif_index_add_time:                    0.
% 16.05/2.51  orderings_time:                         0.
% 16.05/2.51  out_proof_time:                         0.009
% 16.05/2.51  total_time:                             1.909
% 16.05/2.51  num_of_symbols:                         43
% 16.05/2.51  num_of_terms:                           46431
% 16.05/2.51  
% 16.05/2.51  ------ Preprocessing
% 16.05/2.51  
% 16.05/2.51  num_of_splits:                          0
% 16.05/2.51  num_of_split_atoms:                     0
% 16.05/2.51  num_of_reused_defs:                     0
% 16.05/2.51  num_eq_ax_congr_red:                    3
% 16.05/2.51  num_of_sem_filtered_clauses:            1
% 16.05/2.51  num_of_subtypes:                        0
% 16.05/2.51  monotx_restored_types:                  0
% 16.05/2.51  sat_num_of_epr_types:                   0
% 16.05/2.51  sat_num_of_non_cyclic_types:            0
% 16.05/2.51  sat_guarded_non_collapsed_types:        0
% 16.05/2.51  num_pure_diseq_elim:                    0
% 16.05/2.51  simp_replaced_by:                       0
% 16.05/2.51  res_preprocessed:                       83
% 16.05/2.51  prep_upred:                             0
% 16.05/2.51  prep_unflattend:                        3
% 16.05/2.51  smt_new_axioms:                         0
% 16.05/2.51  pred_elim_cands:                        2
% 16.05/2.51  pred_elim:                              2
% 16.05/2.51  pred_elim_cl:                           2
% 16.05/2.51  pred_elim_cycles:                       4
% 16.05/2.51  merged_defs:                            0
% 16.05/2.51  merged_defs_ncl:                        0
% 16.05/2.51  bin_hyper_res:                          0
% 16.05/2.51  prep_cycles:                            4
% 16.05/2.51  pred_elim_time:                         0.002
% 16.05/2.51  splitting_time:                         0.
% 16.05/2.51  sem_filter_time:                        0.
% 16.05/2.51  monotx_time:                            0.001
% 16.05/2.51  subtype_inf_time:                       0.
% 16.05/2.51  
% 16.05/2.51  ------ Problem properties
% 16.05/2.51  
% 16.05/2.51  clauses:                                15
% 16.05/2.51  conjectures:                            3
% 16.05/2.51  epr:                                    3
% 16.05/2.51  horn:                                   15
% 16.05/2.51  ground:                                 3
% 16.05/2.51  unary:                                  8
% 16.05/2.51  binary:                                 4
% 16.05/2.51  lits:                                   26
% 16.05/2.51  lits_eq:                                8
% 16.05/2.51  fd_pure:                                0
% 16.05/2.51  fd_pseudo:                              0
% 16.05/2.51  fd_cond:                                0
% 16.05/2.51  fd_pseudo_cond:                         1
% 16.05/2.51  ac_symbols:                             0
% 16.05/2.51  
% 16.05/2.51  ------ Propositional Solver
% 16.05/2.51  
% 16.05/2.51  prop_solver_calls:                      32
% 16.05/2.51  prop_fast_solver_calls:                 1242
% 16.05/2.51  smt_solver_calls:                       0
% 16.05/2.51  smt_fast_solver_calls:                  0
% 16.05/2.51  prop_num_of_clauses:                    14662
% 16.05/2.51  prop_preprocess_simplified:             24420
% 16.05/2.51  prop_fo_subsumed:                       49
% 16.05/2.51  prop_solver_time:                       0.
% 16.05/2.51  smt_solver_time:                        0.
% 16.05/2.51  smt_fast_solver_time:                   0.
% 16.05/2.51  prop_fast_solver_time:                  0.
% 16.05/2.51  prop_unsat_core_time:                   0.001
% 16.05/2.51  
% 16.05/2.51  ------ QBF
% 16.05/2.51  
% 16.05/2.51  qbf_q_res:                              0
% 16.05/2.51  qbf_num_tautologies:                    0
% 16.05/2.51  qbf_prep_cycles:                        0
% 16.05/2.51  
% 16.05/2.51  ------ BMC1
% 16.05/2.51  
% 16.05/2.51  bmc1_current_bound:                     -1
% 16.05/2.51  bmc1_last_solved_bound:                 -1
% 16.05/2.51  bmc1_unsat_core_size:                   -1
% 16.05/2.51  bmc1_unsat_core_parents_size:           -1
% 16.05/2.51  bmc1_merge_next_fun:                    0
% 16.05/2.51  bmc1_unsat_core_clauses_time:           0.
% 16.05/2.51  
% 16.05/2.51  ------ Instantiation
% 16.05/2.51  
% 16.05/2.51  inst_num_of_clauses:                    3963
% 16.05/2.51  inst_num_in_passive:                    2387
% 16.05/2.51  inst_num_in_active:                     1348
% 16.05/2.51  inst_num_in_unprocessed:                228
% 16.05/2.51  inst_num_of_loops:                      1370
% 16.05/2.51  inst_num_of_learning_restarts:          0
% 16.05/2.51  inst_num_moves_active_passive:          19
% 16.05/2.51  inst_lit_activity:                      0
% 16.05/2.51  inst_lit_activity_moves:                0
% 16.05/2.51  inst_num_tautologies:                   0
% 16.05/2.51  inst_num_prop_implied:                  0
% 16.05/2.51  inst_num_existing_simplified:           0
% 16.05/2.51  inst_num_eq_res_simplified:             0
% 16.05/2.51  inst_num_child_elim:                    0
% 16.05/2.51  inst_num_of_dismatching_blockings:      5098
% 16.05/2.51  inst_num_of_non_proper_insts:           5577
% 16.05/2.51  inst_num_of_duplicates:                 0
% 16.05/2.51  inst_inst_num_from_inst_to_res:         0
% 16.05/2.51  inst_dismatching_checking_time:         0.
% 16.05/2.51  
% 16.05/2.51  ------ Resolution
% 16.05/2.51  
% 16.05/2.51  res_num_of_clauses:                     0
% 16.05/2.51  res_num_in_passive:                     0
% 16.05/2.51  res_num_in_active:                      0
% 16.05/2.51  res_num_of_loops:                       87
% 16.05/2.51  res_forward_subset_subsumed:            590
% 16.05/2.51  res_backward_subset_subsumed:           6
% 16.05/2.51  res_forward_subsumed:                   0
% 16.05/2.51  res_backward_subsumed:                  0
% 16.05/2.51  res_forward_subsumption_resolution:     1
% 16.05/2.51  res_backward_subsumption_resolution:    0
% 16.05/2.51  res_clause_to_clause_subsumption:       8375
% 16.05/2.51  res_orphan_elimination:                 0
% 16.05/2.51  res_tautology_del:                      385
% 16.05/2.51  res_num_eq_res_simplified:              0
% 16.05/2.51  res_num_sel_changes:                    0
% 16.05/2.51  res_moves_from_active_to_pass:          0
% 16.05/2.51  
% 16.05/2.51  ------ Superposition
% 16.05/2.51  
% 16.05/2.51  sup_time_total:                         0.
% 16.05/2.51  sup_time_generating:                    0.
% 16.05/2.51  sup_time_sim_full:                      0.
% 16.05/2.51  sup_time_sim_immed:                     0.
% 16.05/2.51  
% 16.05/2.51  sup_num_of_clauses:                     1372
% 16.05/2.51  sup_num_in_active:                      186
% 16.05/2.51  sup_num_in_passive:                     1186
% 16.05/2.51  sup_num_of_loops:                       272
% 16.05/2.51  sup_fw_superposition:                   1798
% 16.05/2.51  sup_bw_superposition:                   1859
% 16.05/2.51  sup_immediate_simplified:               1176
% 16.05/2.51  sup_given_eliminated:                   4
% 16.05/2.51  comparisons_done:                       0
% 16.05/2.51  comparisons_avoided:                    0
% 16.05/2.51  
% 16.05/2.51  ------ Simplifications
% 16.05/2.51  
% 16.05/2.51  
% 16.05/2.51  sim_fw_subset_subsumed:                 113
% 16.05/2.51  sim_bw_subset_subsumed:                 39
% 16.05/2.51  sim_fw_subsumed:                        82
% 16.05/2.51  sim_bw_subsumed:                        7
% 16.05/2.51  sim_fw_subsumption_res:                 46
% 16.05/2.51  sim_bw_subsumption_res:                 0
% 16.05/2.51  sim_tautology_del:                      0
% 16.05/2.51  sim_eq_tautology_del:                   20
% 16.05/2.51  sim_eq_res_simp:                        0
% 16.05/2.51  sim_fw_demodulated:                     556
% 16.05/2.51  sim_bw_demodulated:                     86
% 16.05/2.51  sim_light_normalised:                   556
% 16.05/2.51  sim_joinable_taut:                      0
% 16.05/2.51  sim_joinable_simp:                      0
% 16.05/2.51  sim_ac_normalised:                      0
% 16.05/2.51  sim_smt_subsumption:                    0
% 16.05/2.51  
%------------------------------------------------------------------------------
