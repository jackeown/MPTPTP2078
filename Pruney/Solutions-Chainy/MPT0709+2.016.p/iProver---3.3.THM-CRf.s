%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:37 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 193 expanded)
%              Number of clauses        :   65 (  78 expanded)
%              Number of leaves         :   15 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  290 ( 559 expanded)
%              Number of equality atoms :  115 ( 172 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f34,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f38,plain,
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

fof(f39,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f38])).

fof(f62,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_672,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_673,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1580,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_672,c_673])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_670,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_674,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1593,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_674])).

cnf(c_38,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2010,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1593,c_38])).

cnf(c_2011,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2010])).

cnf(c_2018,plain,
    ( k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(sK1))) = k6_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_670,c_2011])).

cnf(c_6117,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) = k6_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_1580,c_2018])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_678,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1727,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_672,c_678])).

cnf(c_7256,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) = k2_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_6117,c_1727])).

cnf(c_7277,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_7256,c_5])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_669,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_675,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1352,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_669,c_675])).

cnf(c_19,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,X2),k9_relat_1(X2,X1)))
    | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_671,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,X2),k9_relat_1(X2,X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1360,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK1))),k1_relat_1(sK1)) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1352,c_671])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_15,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_235,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
    | k6_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_15])).

cnf(c_236,plain,
    ( ~ v1_funct_1(k6_relat_1(X0))
    | ~ v1_relat_1(k6_relat_1(X0))
    | k10_relat_1(k2_funct_1(k6_relat_1(X0)),X1) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_13,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_240,plain,
    ( k10_relat_1(k2_funct_1(k6_relat_1(X0)),X1) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_236,c_16,c_13])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_261,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | k6_relat_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_262,plain,
    ( ~ v1_funct_1(k6_relat_1(X0))
    | ~ v1_relat_1(k6_relat_1(X0))
    | k2_funct_1(k6_relat_1(X0)) = k4_relat_1(k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_266,plain,
    ( k2_funct_1(k6_relat_1(X0)) = k4_relat_1(k6_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_262,c_16,c_13])).

cnf(c_7,plain,
    ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_697,plain,
    ( k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_266,c_7])).

cnf(c_707,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_240,c_697])).

cnf(c_1361,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1360,c_5,c_707])).

cnf(c_25,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1129,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1134,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1129])).

cnf(c_1136,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_1416,plain,
    ( v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
    | r1_tarski(k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1361,c_25,c_1136])).

cnf(c_1417,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
    | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1416])).

cnf(c_1424,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1417,c_672])).

cnf(c_7534,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7277,c_1424])).

cnf(c_17,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_283,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_284,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_288,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_284,c_24,c_23])).

cnf(c_833,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_834,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_798,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_799,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0
    | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) != iProver_top
    | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_20,negated_conjecture,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7534,c_834,c_799,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.16/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/1.00  
% 3.16/1.00  ------  iProver source info
% 3.16/1.00  
% 3.16/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.16/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/1.00  git: non_committed_changes: false
% 3.16/1.00  git: last_make_outside_of_git: false
% 3.16/1.00  
% 3.16/1.00  ------ 
% 3.16/1.00  
% 3.16/1.00  ------ Input Options
% 3.16/1.00  
% 3.16/1.00  --out_options                           all
% 3.16/1.00  --tptp_safe_out                         true
% 3.16/1.00  --problem_path                          ""
% 3.16/1.00  --include_path                          ""
% 3.16/1.00  --clausifier                            res/vclausify_rel
% 3.16/1.00  --clausifier_options                    --mode clausify
% 3.16/1.00  --stdin                                 false
% 3.16/1.00  --stats_out                             all
% 3.16/1.00  
% 3.16/1.00  ------ General Options
% 3.16/1.00  
% 3.16/1.00  --fof                                   false
% 3.16/1.00  --time_out_real                         305.
% 3.16/1.00  --time_out_virtual                      -1.
% 3.16/1.00  --symbol_type_check                     false
% 3.16/1.00  --clausify_out                          false
% 3.16/1.00  --sig_cnt_out                           false
% 3.16/1.00  --trig_cnt_out                          false
% 3.16/1.00  --trig_cnt_out_tolerance                1.
% 3.16/1.00  --trig_cnt_out_sk_spl                   false
% 3.16/1.00  --abstr_cl_out                          false
% 3.16/1.00  
% 3.16/1.00  ------ Global Options
% 3.16/1.00  
% 3.16/1.00  --schedule                              default
% 3.16/1.00  --add_important_lit                     false
% 3.16/1.00  --prop_solver_per_cl                    1000
% 3.16/1.00  --min_unsat_core                        false
% 3.16/1.00  --soft_assumptions                      false
% 3.16/1.00  --soft_lemma_size                       3
% 3.16/1.00  --prop_impl_unit_size                   0
% 3.16/1.00  --prop_impl_unit                        []
% 3.16/1.00  --share_sel_clauses                     true
% 3.16/1.00  --reset_solvers                         false
% 3.16/1.00  --bc_imp_inh                            [conj_cone]
% 3.16/1.00  --conj_cone_tolerance                   3.
% 3.16/1.00  --extra_neg_conj                        none
% 3.16/1.00  --large_theory_mode                     true
% 3.16/1.00  --prolific_symb_bound                   200
% 3.16/1.00  --lt_threshold                          2000
% 3.16/1.00  --clause_weak_htbl                      true
% 3.16/1.00  --gc_record_bc_elim                     false
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing Options
% 3.16/1.00  
% 3.16/1.00  --preprocessing_flag                    true
% 3.16/1.00  --time_out_prep_mult                    0.1
% 3.16/1.00  --splitting_mode                        input
% 3.16/1.00  --splitting_grd                         true
% 3.16/1.00  --splitting_cvd                         false
% 3.16/1.00  --splitting_cvd_svl                     false
% 3.16/1.00  --splitting_nvd                         32
% 3.16/1.00  --sub_typing                            true
% 3.16/1.00  --prep_gs_sim                           true
% 3.16/1.00  --prep_unflatten                        true
% 3.16/1.00  --prep_res_sim                          true
% 3.16/1.00  --prep_upred                            true
% 3.16/1.00  --prep_sem_filter                       exhaustive
% 3.16/1.00  --prep_sem_filter_out                   false
% 3.16/1.00  --pred_elim                             true
% 3.16/1.00  --res_sim_input                         true
% 3.16/1.00  --eq_ax_congr_red                       true
% 3.16/1.00  --pure_diseq_elim                       true
% 3.16/1.00  --brand_transform                       false
% 3.16/1.00  --non_eq_to_eq                          false
% 3.16/1.00  --prep_def_merge                        true
% 3.16/1.00  --prep_def_merge_prop_impl              false
% 3.16/1.00  --prep_def_merge_mbd                    true
% 3.16/1.00  --prep_def_merge_tr_red                 false
% 3.16/1.00  --prep_def_merge_tr_cl                  false
% 3.16/1.00  --smt_preprocessing                     true
% 3.16/1.00  --smt_ac_axioms                         fast
% 3.16/1.00  --preprocessed_out                      false
% 3.16/1.00  --preprocessed_stats                    false
% 3.16/1.00  
% 3.16/1.00  ------ Abstraction refinement Options
% 3.16/1.00  
% 3.16/1.00  --abstr_ref                             []
% 3.16/1.00  --abstr_ref_prep                        false
% 3.16/1.00  --abstr_ref_until_sat                   false
% 3.16/1.00  --abstr_ref_sig_restrict                funpre
% 3.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/1.00  --abstr_ref_under                       []
% 3.16/1.00  
% 3.16/1.00  ------ SAT Options
% 3.16/1.00  
% 3.16/1.00  --sat_mode                              false
% 3.16/1.00  --sat_fm_restart_options                ""
% 3.16/1.00  --sat_gr_def                            false
% 3.16/1.00  --sat_epr_types                         true
% 3.16/1.00  --sat_non_cyclic_types                  false
% 3.16/1.00  --sat_finite_models                     false
% 3.16/1.00  --sat_fm_lemmas                         false
% 3.16/1.00  --sat_fm_prep                           false
% 3.16/1.00  --sat_fm_uc_incr                        true
% 3.16/1.00  --sat_out_model                         small
% 3.16/1.00  --sat_out_clauses                       false
% 3.16/1.00  
% 3.16/1.00  ------ QBF Options
% 3.16/1.00  
% 3.16/1.00  --qbf_mode                              false
% 3.16/1.00  --qbf_elim_univ                         false
% 3.16/1.00  --qbf_dom_inst                          none
% 3.16/1.00  --qbf_dom_pre_inst                      false
% 3.16/1.00  --qbf_sk_in                             false
% 3.16/1.00  --qbf_pred_elim                         true
% 3.16/1.00  --qbf_split                             512
% 3.16/1.00  
% 3.16/1.00  ------ BMC1 Options
% 3.16/1.00  
% 3.16/1.00  --bmc1_incremental                      false
% 3.16/1.00  --bmc1_axioms                           reachable_all
% 3.16/1.00  --bmc1_min_bound                        0
% 3.16/1.00  --bmc1_max_bound                        -1
% 3.16/1.00  --bmc1_max_bound_default                -1
% 3.16/1.00  --bmc1_symbol_reachability              true
% 3.16/1.00  --bmc1_property_lemmas                  false
% 3.16/1.00  --bmc1_k_induction                      false
% 3.16/1.00  --bmc1_non_equiv_states                 false
% 3.16/1.00  --bmc1_deadlock                         false
% 3.16/1.00  --bmc1_ucm                              false
% 3.16/1.00  --bmc1_add_unsat_core                   none
% 3.16/1.00  --bmc1_unsat_core_children              false
% 3.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/1.00  --bmc1_out_stat                         full
% 3.16/1.00  --bmc1_ground_init                      false
% 3.16/1.00  --bmc1_pre_inst_next_state              false
% 3.16/1.00  --bmc1_pre_inst_state                   false
% 3.16/1.00  --bmc1_pre_inst_reach_state             false
% 3.16/1.00  --bmc1_out_unsat_core                   false
% 3.16/1.00  --bmc1_aig_witness_out                  false
% 3.16/1.00  --bmc1_verbose                          false
% 3.16/1.00  --bmc1_dump_clauses_tptp                false
% 3.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.16/1.00  --bmc1_dump_file                        -
% 3.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.16/1.00  --bmc1_ucm_extend_mode                  1
% 3.16/1.00  --bmc1_ucm_init_mode                    2
% 3.16/1.00  --bmc1_ucm_cone_mode                    none
% 3.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.16/1.00  --bmc1_ucm_relax_model                  4
% 3.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/1.00  --bmc1_ucm_layered_model                none
% 3.16/1.00  --bmc1_ucm_max_lemma_size               10
% 3.16/1.00  
% 3.16/1.00  ------ AIG Options
% 3.16/1.00  
% 3.16/1.00  --aig_mode                              false
% 3.16/1.00  
% 3.16/1.00  ------ Instantiation Options
% 3.16/1.00  
% 3.16/1.00  --instantiation_flag                    true
% 3.16/1.00  --inst_sos_flag                         false
% 3.16/1.00  --inst_sos_phase                        true
% 3.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel_side                     num_symb
% 3.16/1.00  --inst_solver_per_active                1400
% 3.16/1.00  --inst_solver_calls_frac                1.
% 3.16/1.00  --inst_passive_queue_type               priority_queues
% 3.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/1.00  --inst_passive_queues_freq              [25;2]
% 3.16/1.00  --inst_dismatching                      true
% 3.16/1.00  --inst_eager_unprocessed_to_passive     true
% 3.16/1.00  --inst_prop_sim_given                   true
% 3.16/1.00  --inst_prop_sim_new                     false
% 3.16/1.00  --inst_subs_new                         false
% 3.16/1.00  --inst_eq_res_simp                      false
% 3.16/1.00  --inst_subs_given                       false
% 3.16/1.00  --inst_orphan_elimination               true
% 3.16/1.00  --inst_learning_loop_flag               true
% 3.16/1.00  --inst_learning_start                   3000
% 3.16/1.00  --inst_learning_factor                  2
% 3.16/1.00  --inst_start_prop_sim_after_learn       3
% 3.16/1.00  --inst_sel_renew                        solver
% 3.16/1.00  --inst_lit_activity_flag                true
% 3.16/1.00  --inst_restr_to_given                   false
% 3.16/1.00  --inst_activity_threshold               500
% 3.16/1.00  --inst_out_proof                        true
% 3.16/1.00  
% 3.16/1.00  ------ Resolution Options
% 3.16/1.00  
% 3.16/1.00  --resolution_flag                       true
% 3.16/1.00  --res_lit_sel                           adaptive
% 3.16/1.00  --res_lit_sel_side                      none
% 3.16/1.00  --res_ordering                          kbo
% 3.16/1.00  --res_to_prop_solver                    active
% 3.16/1.00  --res_prop_simpl_new                    false
% 3.16/1.00  --res_prop_simpl_given                  true
% 3.16/1.00  --res_passive_queue_type                priority_queues
% 3.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/1.00  --res_passive_queues_freq               [15;5]
% 3.16/1.00  --res_forward_subs                      full
% 3.16/1.00  --res_backward_subs                     full
% 3.16/1.00  --res_forward_subs_resolution           true
% 3.16/1.00  --res_backward_subs_resolution          true
% 3.16/1.00  --res_orphan_elimination                true
% 3.16/1.00  --res_time_limit                        2.
% 3.16/1.00  --res_out_proof                         true
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Options
% 3.16/1.00  
% 3.16/1.00  --superposition_flag                    true
% 3.16/1.00  --sup_passive_queue_type                priority_queues
% 3.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.16/1.00  --demod_completeness_check              fast
% 3.16/1.00  --demod_use_ground                      true
% 3.16/1.00  --sup_to_prop_solver                    passive
% 3.16/1.00  --sup_prop_simpl_new                    true
% 3.16/1.00  --sup_prop_simpl_given                  true
% 3.16/1.00  --sup_fun_splitting                     false
% 3.16/1.00  --sup_smt_interval                      50000
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Simplification Setup
% 3.16/1.00  
% 3.16/1.00  --sup_indices_passive                   []
% 3.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_full_bw                           [BwDemod]
% 3.16/1.00  --sup_immed_triv                        [TrivRules]
% 3.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_immed_bw_main                     []
% 3.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  
% 3.16/1.00  ------ Combination Options
% 3.16/1.00  
% 3.16/1.00  --comb_res_mult                         3
% 3.16/1.00  --comb_sup_mult                         2
% 3.16/1.00  --comb_inst_mult                        10
% 3.16/1.00  
% 3.16/1.00  ------ Debug Options
% 3.16/1.00  
% 3.16/1.00  --dbg_backtrace                         false
% 3.16/1.00  --dbg_dump_prop_clauses                 false
% 3.16/1.00  --dbg_dump_prop_clauses_file            -
% 3.16/1.00  --dbg_out_stat                          false
% 3.16/1.00  ------ Parsing...
% 3.16/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/1.00  ------ Proving...
% 3.16/1.00  ------ Problem Properties 
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  clauses                                 22
% 3.16/1.00  conjectures                             3
% 3.16/1.00  EPR                                     3
% 3.16/1.00  Horn                                    22
% 3.16/1.00  unary                                   14
% 3.16/1.00  binary                                  3
% 3.16/1.00  lits                                    36
% 3.16/1.00  lits eq                                 15
% 3.16/1.00  fd_pure                                 0
% 3.16/1.00  fd_pseudo                               0
% 3.16/1.00  fd_cond                                 0
% 3.16/1.00  fd_pseudo_cond                          1
% 3.16/1.00  AC symbols                              0
% 3.16/1.00  
% 3.16/1.00  ------ Schedule dynamic 5 is on 
% 3.16/1.00  
% 3.16/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  ------ 
% 3.16/1.00  Current options:
% 3.16/1.00  ------ 
% 3.16/1.00  
% 3.16/1.00  ------ Input Options
% 3.16/1.00  
% 3.16/1.00  --out_options                           all
% 3.16/1.00  --tptp_safe_out                         true
% 3.16/1.00  --problem_path                          ""
% 3.16/1.00  --include_path                          ""
% 3.16/1.00  --clausifier                            res/vclausify_rel
% 3.16/1.00  --clausifier_options                    --mode clausify
% 3.16/1.00  --stdin                                 false
% 3.16/1.00  --stats_out                             all
% 3.16/1.00  
% 3.16/1.00  ------ General Options
% 3.16/1.00  
% 3.16/1.00  --fof                                   false
% 3.16/1.00  --time_out_real                         305.
% 3.16/1.00  --time_out_virtual                      -1.
% 3.16/1.00  --symbol_type_check                     false
% 3.16/1.00  --clausify_out                          false
% 3.16/1.00  --sig_cnt_out                           false
% 3.16/1.00  --trig_cnt_out                          false
% 3.16/1.00  --trig_cnt_out_tolerance                1.
% 3.16/1.00  --trig_cnt_out_sk_spl                   false
% 3.16/1.00  --abstr_cl_out                          false
% 3.16/1.00  
% 3.16/1.00  ------ Global Options
% 3.16/1.00  
% 3.16/1.00  --schedule                              default
% 3.16/1.00  --add_important_lit                     false
% 3.16/1.00  --prop_solver_per_cl                    1000
% 3.16/1.00  --min_unsat_core                        false
% 3.16/1.00  --soft_assumptions                      false
% 3.16/1.00  --soft_lemma_size                       3
% 3.16/1.00  --prop_impl_unit_size                   0
% 3.16/1.00  --prop_impl_unit                        []
% 3.16/1.00  --share_sel_clauses                     true
% 3.16/1.00  --reset_solvers                         false
% 3.16/1.00  --bc_imp_inh                            [conj_cone]
% 3.16/1.00  --conj_cone_tolerance                   3.
% 3.16/1.00  --extra_neg_conj                        none
% 3.16/1.00  --large_theory_mode                     true
% 3.16/1.00  --prolific_symb_bound                   200
% 3.16/1.00  --lt_threshold                          2000
% 3.16/1.00  --clause_weak_htbl                      true
% 3.16/1.00  --gc_record_bc_elim                     false
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing Options
% 3.16/1.00  
% 3.16/1.00  --preprocessing_flag                    true
% 3.16/1.00  --time_out_prep_mult                    0.1
% 3.16/1.00  --splitting_mode                        input
% 3.16/1.00  --splitting_grd                         true
% 3.16/1.00  --splitting_cvd                         false
% 3.16/1.00  --splitting_cvd_svl                     false
% 3.16/1.00  --splitting_nvd                         32
% 3.16/1.00  --sub_typing                            true
% 3.16/1.00  --prep_gs_sim                           true
% 3.16/1.00  --prep_unflatten                        true
% 3.16/1.00  --prep_res_sim                          true
% 3.16/1.00  --prep_upred                            true
% 3.16/1.00  --prep_sem_filter                       exhaustive
% 3.16/1.00  --prep_sem_filter_out                   false
% 3.16/1.00  --pred_elim                             true
% 3.16/1.00  --res_sim_input                         true
% 3.16/1.00  --eq_ax_congr_red                       true
% 3.16/1.00  --pure_diseq_elim                       true
% 3.16/1.00  --brand_transform                       false
% 3.16/1.00  --non_eq_to_eq                          false
% 3.16/1.00  --prep_def_merge                        true
% 3.16/1.00  --prep_def_merge_prop_impl              false
% 3.16/1.00  --prep_def_merge_mbd                    true
% 3.16/1.00  --prep_def_merge_tr_red                 false
% 3.16/1.00  --prep_def_merge_tr_cl                  false
% 3.16/1.00  --smt_preprocessing                     true
% 3.16/1.00  --smt_ac_axioms                         fast
% 3.16/1.00  --preprocessed_out                      false
% 3.16/1.00  --preprocessed_stats                    false
% 3.16/1.00  
% 3.16/1.00  ------ Abstraction refinement Options
% 3.16/1.00  
% 3.16/1.00  --abstr_ref                             []
% 3.16/1.00  --abstr_ref_prep                        false
% 3.16/1.00  --abstr_ref_until_sat                   false
% 3.16/1.00  --abstr_ref_sig_restrict                funpre
% 3.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/1.00  --abstr_ref_under                       []
% 3.16/1.00  
% 3.16/1.00  ------ SAT Options
% 3.16/1.00  
% 3.16/1.00  --sat_mode                              false
% 3.16/1.00  --sat_fm_restart_options                ""
% 3.16/1.00  --sat_gr_def                            false
% 3.16/1.00  --sat_epr_types                         true
% 3.16/1.00  --sat_non_cyclic_types                  false
% 3.16/1.00  --sat_finite_models                     false
% 3.16/1.00  --sat_fm_lemmas                         false
% 3.16/1.00  --sat_fm_prep                           false
% 3.16/1.00  --sat_fm_uc_incr                        true
% 3.16/1.00  --sat_out_model                         small
% 3.16/1.00  --sat_out_clauses                       false
% 3.16/1.00  
% 3.16/1.00  ------ QBF Options
% 3.16/1.00  
% 3.16/1.00  --qbf_mode                              false
% 3.16/1.00  --qbf_elim_univ                         false
% 3.16/1.00  --qbf_dom_inst                          none
% 3.16/1.00  --qbf_dom_pre_inst                      false
% 3.16/1.00  --qbf_sk_in                             false
% 3.16/1.00  --qbf_pred_elim                         true
% 3.16/1.00  --qbf_split                             512
% 3.16/1.00  
% 3.16/1.00  ------ BMC1 Options
% 3.16/1.00  
% 3.16/1.00  --bmc1_incremental                      false
% 3.16/1.00  --bmc1_axioms                           reachable_all
% 3.16/1.00  --bmc1_min_bound                        0
% 3.16/1.00  --bmc1_max_bound                        -1
% 3.16/1.00  --bmc1_max_bound_default                -1
% 3.16/1.00  --bmc1_symbol_reachability              true
% 3.16/1.00  --bmc1_property_lemmas                  false
% 3.16/1.00  --bmc1_k_induction                      false
% 3.16/1.00  --bmc1_non_equiv_states                 false
% 3.16/1.00  --bmc1_deadlock                         false
% 3.16/1.00  --bmc1_ucm                              false
% 3.16/1.00  --bmc1_add_unsat_core                   none
% 3.16/1.00  --bmc1_unsat_core_children              false
% 3.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/1.00  --bmc1_out_stat                         full
% 3.16/1.00  --bmc1_ground_init                      false
% 3.16/1.00  --bmc1_pre_inst_next_state              false
% 3.16/1.00  --bmc1_pre_inst_state                   false
% 3.16/1.00  --bmc1_pre_inst_reach_state             false
% 3.16/1.00  --bmc1_out_unsat_core                   false
% 3.16/1.00  --bmc1_aig_witness_out                  false
% 3.16/1.00  --bmc1_verbose                          false
% 3.16/1.00  --bmc1_dump_clauses_tptp                false
% 3.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.16/1.00  --bmc1_dump_file                        -
% 3.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.16/1.00  --bmc1_ucm_extend_mode                  1
% 3.16/1.00  --bmc1_ucm_init_mode                    2
% 3.16/1.00  --bmc1_ucm_cone_mode                    none
% 3.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.16/1.00  --bmc1_ucm_relax_model                  4
% 3.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/1.00  --bmc1_ucm_layered_model                none
% 3.16/1.00  --bmc1_ucm_max_lemma_size               10
% 3.16/1.00  
% 3.16/1.00  ------ AIG Options
% 3.16/1.00  
% 3.16/1.00  --aig_mode                              false
% 3.16/1.00  
% 3.16/1.00  ------ Instantiation Options
% 3.16/1.00  
% 3.16/1.00  --instantiation_flag                    true
% 3.16/1.00  --inst_sos_flag                         false
% 3.16/1.00  --inst_sos_phase                        true
% 3.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel_side                     none
% 3.16/1.00  --inst_solver_per_active                1400
% 3.16/1.00  --inst_solver_calls_frac                1.
% 3.16/1.00  --inst_passive_queue_type               priority_queues
% 3.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/1.00  --inst_passive_queues_freq              [25;2]
% 3.16/1.00  --inst_dismatching                      true
% 3.16/1.00  --inst_eager_unprocessed_to_passive     true
% 3.16/1.00  --inst_prop_sim_given                   true
% 3.16/1.00  --inst_prop_sim_new                     false
% 3.16/1.00  --inst_subs_new                         false
% 3.16/1.00  --inst_eq_res_simp                      false
% 3.16/1.00  --inst_subs_given                       false
% 3.16/1.00  --inst_orphan_elimination               true
% 3.16/1.00  --inst_learning_loop_flag               true
% 3.16/1.00  --inst_learning_start                   3000
% 3.16/1.00  --inst_learning_factor                  2
% 3.16/1.00  --inst_start_prop_sim_after_learn       3
% 3.16/1.00  --inst_sel_renew                        solver
% 3.16/1.00  --inst_lit_activity_flag                true
% 3.16/1.00  --inst_restr_to_given                   false
% 3.16/1.00  --inst_activity_threshold               500
% 3.16/1.00  --inst_out_proof                        true
% 3.16/1.00  
% 3.16/1.00  ------ Resolution Options
% 3.16/1.00  
% 3.16/1.00  --resolution_flag                       false
% 3.16/1.00  --res_lit_sel                           adaptive
% 3.16/1.00  --res_lit_sel_side                      none
% 3.16/1.00  --res_ordering                          kbo
% 3.16/1.00  --res_to_prop_solver                    active
% 3.16/1.00  --res_prop_simpl_new                    false
% 3.16/1.00  --res_prop_simpl_given                  true
% 3.16/1.00  --res_passive_queue_type                priority_queues
% 3.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/1.00  --res_passive_queues_freq               [15;5]
% 3.16/1.00  --res_forward_subs                      full
% 3.16/1.00  --res_backward_subs                     full
% 3.16/1.00  --res_forward_subs_resolution           true
% 3.16/1.00  --res_backward_subs_resolution          true
% 3.16/1.00  --res_orphan_elimination                true
% 3.16/1.00  --res_time_limit                        2.
% 3.16/1.00  --res_out_proof                         true
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Options
% 3.16/1.00  
% 3.16/1.00  --superposition_flag                    true
% 3.16/1.00  --sup_passive_queue_type                priority_queues
% 3.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.16/1.00  --demod_completeness_check              fast
% 3.16/1.00  --demod_use_ground                      true
% 3.16/1.00  --sup_to_prop_solver                    passive
% 3.16/1.00  --sup_prop_simpl_new                    true
% 3.16/1.00  --sup_prop_simpl_given                  true
% 3.16/1.00  --sup_fun_splitting                     false
% 3.16/1.00  --sup_smt_interval                      50000
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Simplification Setup
% 3.16/1.00  
% 3.16/1.00  --sup_indices_passive                   []
% 3.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_full_bw                           [BwDemod]
% 3.16/1.00  --sup_immed_triv                        [TrivRules]
% 3.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_immed_bw_main                     []
% 3.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  
% 3.16/1.00  ------ Combination Options
% 3.16/1.00  
% 3.16/1.00  --comb_res_mult                         3
% 3.16/1.00  --comb_sup_mult                         2
% 3.16/1.00  --comb_inst_mult                        10
% 3.16/1.00  
% 3.16/1.00  ------ Debug Options
% 3.16/1.00  
% 3.16/1.00  --dbg_backtrace                         false
% 3.16/1.00  --dbg_dump_prop_clauses                 false
% 3.16/1.00  --dbg_dump_prop_clauses_file            -
% 3.16/1.00  --dbg_out_stat                          false
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  ------ Proving...
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  % SZS status Theorem for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  fof(f12,axiom,(
% 3.16/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f55,plain,(
% 3.16/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f12])).
% 3.16/1.00  
% 3.16/1.00  fof(f9,axiom,(
% 3.16/1.00    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f25,plain,(
% 3.16/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(ennf_transformation,[],[f9])).
% 3.16/1.00  
% 3.16/1.00  fof(f51,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f25])).
% 3.16/1.00  
% 3.16/1.00  fof(f16,conjecture,(
% 3.16/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f17,negated_conjecture,(
% 3.16/1.00    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.16/1.00    inference(negated_conjecture,[],[f16])).
% 3.16/1.00  
% 3.16/1.00  fof(f34,plain,(
% 3.16/1.00    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.16/1.00    inference(ennf_transformation,[],[f17])).
% 3.16/1.00  
% 3.16/1.00  fof(f35,plain,(
% 3.16/1.00    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.16/1.00    inference(flattening,[],[f34])).
% 3.16/1.00  
% 3.16/1.00  fof(f38,plain,(
% 3.16/1.00    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f39,plain,(
% 3.16/1.00    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 3.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f38])).
% 3.16/1.00  
% 3.16/1.00  fof(f62,plain,(
% 3.16/1.00    r1_tarski(sK0,k1_relat_1(sK1))),
% 3.16/1.00    inference(cnf_transformation,[],[f39])).
% 3.16/1.00  
% 3.16/1.00  fof(f4,axiom,(
% 3.16/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f46,plain,(
% 3.16/1.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.16/1.00    inference(cnf_transformation,[],[f4])).
% 3.16/1.00  
% 3.16/1.00  fof(f8,axiom,(
% 3.16/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f23,plain,(
% 3.16/1.00    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(ennf_transformation,[],[f8])).
% 3.16/1.00  
% 3.16/1.00  fof(f24,plain,(
% 3.16/1.00    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(flattening,[],[f23])).
% 3.16/1.00  
% 3.16/1.00  fof(f50,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f24])).
% 3.16/1.00  
% 3.16/1.00  fof(f2,axiom,(
% 3.16/1.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f18,plain,(
% 3.16/1.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(ennf_transformation,[],[f2])).
% 3.16/1.00  
% 3.16/1.00  fof(f43,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f18])).
% 3.16/1.00  
% 3.16/1.00  fof(f60,plain,(
% 3.16/1.00    v1_relat_1(sK1)),
% 3.16/1.00    inference(cnf_transformation,[],[f39])).
% 3.16/1.00  
% 3.16/1.00  fof(f7,axiom,(
% 3.16/1.00    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f22,plain,(
% 3.16/1.00    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 3.16/1.00    inference(ennf_transformation,[],[f7])).
% 3.16/1.00  
% 3.16/1.00  fof(f49,plain,(
% 3.16/1.00    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f22])).
% 3.16/1.00  
% 3.16/1.00  fof(f15,axiom,(
% 3.16/1.00    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f32,plain,(
% 3.16/1.00    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(ennf_transformation,[],[f15])).
% 3.16/1.00  
% 3.16/1.00  fof(f33,plain,(
% 3.16/1.00    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(flattening,[],[f32])).
% 3.16/1.00  
% 3.16/1.00  fof(f59,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f33])).
% 3.16/1.00  
% 3.16/1.00  fof(f14,axiom,(
% 3.16/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f30,plain,(
% 3.16/1.00    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.16/1.00    inference(ennf_transformation,[],[f14])).
% 3.16/1.00  
% 3.16/1.00  fof(f31,plain,(
% 3.16/1.00    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(flattening,[],[f30])).
% 3.16/1.00  
% 3.16/1.00  fof(f58,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f31])).
% 3.16/1.00  
% 3.16/1.00  fof(f56,plain,(
% 3.16/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f12])).
% 3.16/1.00  
% 3.16/1.00  fof(f11,axiom,(
% 3.16/1.00    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f54,plain,(
% 3.16/1.00    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f11])).
% 3.16/1.00  
% 3.16/1.00  fof(f10,axiom,(
% 3.16/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f26,plain,(
% 3.16/1.00    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.16/1.00    inference(ennf_transformation,[],[f10])).
% 3.16/1.00  
% 3.16/1.00  fof(f27,plain,(
% 3.16/1.00    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.16/1.00    inference(flattening,[],[f26])).
% 3.16/1.00  
% 3.16/1.00  fof(f52,plain,(
% 3.16/1.00    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f27])).
% 3.16/1.00  
% 3.16/1.00  fof(f5,axiom,(
% 3.16/1.00    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f47,plain,(
% 3.16/1.00    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f5])).
% 3.16/1.00  
% 3.16/1.00  fof(f1,axiom,(
% 3.16/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f36,plain,(
% 3.16/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.16/1.00    inference(nnf_transformation,[],[f1])).
% 3.16/1.00  
% 3.16/1.00  fof(f37,plain,(
% 3.16/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.16/1.00    inference(flattening,[],[f36])).
% 3.16/1.00  
% 3.16/1.00  fof(f40,plain,(
% 3.16/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.16/1.00    inference(cnf_transformation,[],[f37])).
% 3.16/1.00  
% 3.16/1.00  fof(f66,plain,(
% 3.16/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.16/1.00    inference(equality_resolution,[],[f40])).
% 3.16/1.00  
% 3.16/1.00  fof(f13,axiom,(
% 3.16/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f28,plain,(
% 3.16/1.00    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.16/1.00    inference(ennf_transformation,[],[f13])).
% 3.16/1.00  
% 3.16/1.00  fof(f29,plain,(
% 3.16/1.00    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(flattening,[],[f28])).
% 3.16/1.00  
% 3.16/1.00  fof(f57,plain,(
% 3.16/1.00    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f29])).
% 3.16/1.00  
% 3.16/1.00  fof(f63,plain,(
% 3.16/1.00    v2_funct_1(sK1)),
% 3.16/1.00    inference(cnf_transformation,[],[f39])).
% 3.16/1.00  
% 3.16/1.00  fof(f61,plain,(
% 3.16/1.00    v1_funct_1(sK1)),
% 3.16/1.00    inference(cnf_transformation,[],[f39])).
% 3.16/1.00  
% 3.16/1.00  fof(f42,plain,(
% 3.16/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f37])).
% 3.16/1.00  
% 3.16/1.00  fof(f64,plain,(
% 3.16/1.00    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0),
% 3.16/1.00    inference(cnf_transformation,[],[f39])).
% 3.16/1.00  
% 3.16/1.00  cnf(c_16,plain,
% 3.16/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.16/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_672,plain,
% 3.16/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_11,plain,
% 3.16/1.00      ( ~ v1_relat_1(X0)
% 3.16/1.00      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_673,plain,
% 3.16/1.00      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 3.16/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1580,plain,
% 3.16/1.00      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_672,c_673]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_22,negated_conjecture,
% 3.16/1.00      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 3.16/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_670,plain,
% 3.16/1.00      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5,plain,
% 3.16/1.00      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.16/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_10,plain,
% 3.16/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.16/1.00      | ~ v1_relat_1(X0)
% 3.16/1.00      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 3.16/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_674,plain,
% 3.16/1.00      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 3.16/1.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.16/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1593,plain,
% 3.16/1.00      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 3.16/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.16/1.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_5,c_674]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_38,plain,
% 3.16/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2010,plain,
% 3.16/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.16/1.00      | k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0) ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_1593,c_38]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2011,plain,
% 3.16/1.00      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 3.16/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.16/1.00      inference(renaming,[status(thm)],[c_2010]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2018,plain,
% 3.16/1.01      ( k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(sK1))) = k6_relat_1(sK0) ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_670,c_2011]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_6117,plain,
% 3.16/1.01      ( k7_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) = k6_relat_1(sK0) ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1580,c_2018]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3,plain,
% 3.16/1.01      ( ~ v1_relat_1(X0)
% 3.16/1.01      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.16/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_678,plain,
% 3.16/1.01      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.16/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1727,plain,
% 3.16/1.01      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_672,c_678]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_7256,plain,
% 3.16/1.01      ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) = k2_relat_1(k6_relat_1(sK0)) ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_6117,c_1727]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_7277,plain,
% 3.16/1.01      ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) = sK0 ),
% 3.16/1.01      inference(demodulation,[status(thm)],[c_7256,c_5]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_24,negated_conjecture,
% 3.16/1.01      ( v1_relat_1(sK1) ),
% 3.16/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_669,plain,
% 3.16/1.01      ( v1_relat_1(sK1) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_9,plain,
% 3.16/1.01      ( ~ v1_relat_1(X0)
% 3.16/1.01      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
% 3.16/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_675,plain,
% 3.16/1.01      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 3.16/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1352,plain,
% 3.16/1.01      ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = sK1 ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_669,c_675]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_19,plain,
% 3.16/1.01      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,X2),k9_relat_1(X2,X1)))
% 3.16/1.01      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X2))
% 3.16/1.01      | ~ v1_relat_1(X0)
% 3.16/1.01      | ~ v1_relat_1(X2) ),
% 3.16/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_671,plain,
% 3.16/1.01      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,X2),k9_relat_1(X2,X1))) = iProver_top
% 3.16/1.01      | r1_tarski(k2_relat_1(X0),k1_relat_1(X2)) != iProver_top
% 3.16/1.01      | v1_relat_1(X0) != iProver_top
% 3.16/1.01      | v1_relat_1(X2) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1360,plain,
% 3.16/1.01      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
% 3.16/1.01      | r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK1))),k1_relat_1(sK1)) != iProver_top
% 3.16/1.01      | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
% 3.16/1.01      | v1_relat_1(sK1) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1352,c_671]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_18,plain,
% 3.16/1.01      ( ~ v1_funct_1(X0)
% 3.16/1.01      | ~ v2_funct_1(X0)
% 3.16/1.01      | ~ v1_relat_1(X0)
% 3.16/1.01      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
% 3.16/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_15,plain,
% 3.16/1.01      ( v2_funct_1(k6_relat_1(X0)) ),
% 3.16/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_235,plain,
% 3.16/1.01      ( ~ v1_funct_1(X0)
% 3.16/1.01      | ~ v1_relat_1(X0)
% 3.16/1.01      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
% 3.16/1.01      | k6_relat_1(X2) != X0 ),
% 3.16/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_15]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_236,plain,
% 3.16/1.01      ( ~ v1_funct_1(k6_relat_1(X0))
% 3.16/1.01      | ~ v1_relat_1(k6_relat_1(X0))
% 3.16/1.01      | k10_relat_1(k2_funct_1(k6_relat_1(X0)),X1) = k9_relat_1(k6_relat_1(X0),X1) ),
% 3.16/1.01      inference(unflattening,[status(thm)],[c_235]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_13,plain,
% 3.16/1.01      ( v1_funct_1(k6_relat_1(X0)) ),
% 3.16/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_240,plain,
% 3.16/1.01      ( k10_relat_1(k2_funct_1(k6_relat_1(X0)),X1) = k9_relat_1(k6_relat_1(X0),X1) ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_236,c_16,c_13]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_12,plain,
% 3.16/1.01      ( ~ v1_funct_1(X0)
% 3.16/1.01      | ~ v2_funct_1(X0)
% 3.16/1.01      | ~ v1_relat_1(X0)
% 3.16/1.01      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_261,plain,
% 3.16/1.01      ( ~ v1_funct_1(X0)
% 3.16/1.01      | ~ v1_relat_1(X0)
% 3.16/1.01      | k2_funct_1(X0) = k4_relat_1(X0)
% 3.16/1.01      | k6_relat_1(X1) != X0 ),
% 3.16/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_262,plain,
% 3.16/1.01      ( ~ v1_funct_1(k6_relat_1(X0))
% 3.16/1.01      | ~ v1_relat_1(k6_relat_1(X0))
% 3.16/1.01      | k2_funct_1(k6_relat_1(X0)) = k4_relat_1(k6_relat_1(X0)) ),
% 3.16/1.01      inference(unflattening,[status(thm)],[c_261]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_266,plain,
% 3.16/1.01      ( k2_funct_1(k6_relat_1(X0)) = k4_relat_1(k6_relat_1(X0)) ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_262,c_16,c_13]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_7,plain,
% 3.16/1.01      ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_697,plain,
% 3.16/1.01      ( k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
% 3.16/1.01      inference(light_normalisation,[status(thm)],[c_266,c_7]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_707,plain,
% 3.16/1.01      ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1) ),
% 3.16/1.01      inference(light_normalisation,[status(thm)],[c_240,c_697]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1361,plain,
% 3.16/1.01      ( r1_tarski(k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
% 3.16/1.01      | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top
% 3.16/1.01      | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
% 3.16/1.01      | v1_relat_1(sK1) != iProver_top ),
% 3.16/1.01      inference(demodulation,[status(thm)],[c_1360,c_5,c_707]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_25,plain,
% 3.16/1.01      ( v1_relat_1(sK1) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2,plain,
% 3.16/1.01      ( r1_tarski(X0,X0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1129,plain,
% 3.16/1.01      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1134,plain,
% 3.16/1.01      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_1129]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1136,plain,
% 3.16/1.01      ( r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) = iProver_top ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_1134]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1416,plain,
% 3.16/1.01      ( v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top
% 3.16/1.01      | r1_tarski(k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_1361,c_25,c_1136]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1417,plain,
% 3.16/1.01      ( r1_tarski(k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top
% 3.16/1.01      | v1_relat_1(k6_relat_1(k1_relat_1(sK1))) != iProver_top ),
% 3.16/1.01      inference(renaming,[status(thm)],[c_1416]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1424,plain,
% 3.16/1.01      ( r1_tarski(k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
% 3.16/1.01      inference(forward_subsumption_resolution,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_1417,c_672]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_7534,plain,
% 3.16/1.01      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_7277,c_1424]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_17,plain,
% 3.16/1.01      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 3.16/1.01      | ~ v1_funct_1(X0)
% 3.16/1.01      | ~ v2_funct_1(X0)
% 3.16/1.01      | ~ v1_relat_1(X0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_21,negated_conjecture,
% 3.16/1.01      ( v2_funct_1(sK1) ),
% 3.16/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_283,plain,
% 3.16/1.01      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 3.16/1.01      | ~ v1_funct_1(X0)
% 3.16/1.01      | ~ v1_relat_1(X0)
% 3.16/1.01      | sK1 != X0 ),
% 3.16/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_284,plain,
% 3.16/1.01      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
% 3.16/1.01      | ~ v1_funct_1(sK1)
% 3.16/1.01      | ~ v1_relat_1(sK1) ),
% 3.16/1.01      inference(unflattening,[status(thm)],[c_283]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_23,negated_conjecture,
% 3.16/1.01      ( v1_funct_1(sK1) ),
% 3.16/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_288,plain,
% 3.16/1.01      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_284,c_24,c_23]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_833,plain,
% 3.16/1.01      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_288]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_834,plain,
% 3.16/1.01      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_833]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_0,plain,
% 3.16/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.16/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_798,plain,
% 3.16/1.01      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
% 3.16/1.01      | ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
% 3.16/1.01      | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_799,plain,
% 3.16/1.01      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0
% 3.16/1.01      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) != iProver_top
% 3.16/1.01      | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_20,negated_conjecture,
% 3.16/1.01      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
% 3.16/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(contradiction,plain,
% 3.16/1.01      ( $false ),
% 3.16/1.01      inference(minisat,[status(thm)],[c_7534,c_834,c_799,c_20]) ).
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/1.01  
% 3.16/1.01  ------                               Statistics
% 3.16/1.01  
% 3.16/1.01  ------ General
% 3.16/1.01  
% 3.16/1.01  abstr_ref_over_cycles:                  0
% 3.16/1.01  abstr_ref_under_cycles:                 0
% 3.16/1.01  gc_basic_clause_elim:                   0
% 3.16/1.01  forced_gc_time:                         0
% 3.16/1.01  parsing_time:                           0.008
% 3.16/1.01  unif_index_cands_time:                  0.
% 3.16/1.01  unif_index_add_time:                    0.
% 3.16/1.01  orderings_time:                         0.
% 3.16/1.01  out_proof_time:                         0.008
% 3.16/1.01  total_time:                             0.294
% 3.16/1.01  num_of_symbols:                         46
% 3.16/1.01  num_of_terms:                           8232
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing
% 3.16/1.01  
% 3.16/1.01  num_of_splits:                          0
% 3.16/1.01  num_of_split_atoms:                     0
% 3.16/1.01  num_of_reused_defs:                     0
% 3.16/1.01  num_eq_ax_congr_red:                    7
% 3.16/1.01  num_of_sem_filtered_clauses:            1
% 3.16/1.01  num_of_subtypes:                        0
% 3.16/1.01  monotx_restored_types:                  0
% 3.16/1.01  sat_num_of_epr_types:                   0
% 3.16/1.01  sat_num_of_non_cyclic_types:            0
% 3.16/1.01  sat_guarded_non_collapsed_types:        0
% 3.16/1.01  num_pure_diseq_elim:                    0
% 3.16/1.01  simp_replaced_by:                       0
% 3.16/1.01  res_preprocessed:                       114
% 3.16/1.01  prep_upred:                             0
% 3.16/1.01  prep_unflattend:                        6
% 3.16/1.01  smt_new_axioms:                         0
% 3.16/1.01  pred_elim_cands:                        2
% 3.16/1.01  pred_elim:                              2
% 3.16/1.01  pred_elim_cl:                           1
% 3.16/1.01  pred_elim_cycles:                       4
% 3.16/1.01  merged_defs:                            0
% 3.16/1.01  merged_defs_ncl:                        0
% 3.16/1.01  bin_hyper_res:                          0
% 3.16/1.01  prep_cycles:                            4
% 3.16/1.01  pred_elim_time:                         0.007
% 3.16/1.01  splitting_time:                         0.
% 3.16/1.01  sem_filter_time:                        0.
% 3.16/1.01  monotx_time:                            0.
% 3.16/1.01  subtype_inf_time:                       0.
% 3.16/1.01  
% 3.16/1.01  ------ Problem properties
% 3.16/1.01  
% 3.16/1.01  clauses:                                22
% 3.16/1.01  conjectures:                            3
% 3.16/1.01  epr:                                    3
% 3.16/1.01  horn:                                   22
% 3.16/1.01  ground:                                 4
% 3.16/1.01  unary:                                  14
% 3.16/1.01  binary:                                 3
% 3.16/1.01  lits:                                   36
% 3.16/1.01  lits_eq:                                15
% 3.16/1.01  fd_pure:                                0
% 3.16/1.01  fd_pseudo:                              0
% 3.16/1.01  fd_cond:                                0
% 3.16/1.01  fd_pseudo_cond:                         1
% 3.16/1.01  ac_symbols:                             0
% 3.16/1.01  
% 3.16/1.01  ------ Propositional Solver
% 3.16/1.01  
% 3.16/1.01  prop_solver_calls:                      28
% 3.16/1.01  prop_fast_solver_calls:                 631
% 3.16/1.01  smt_solver_calls:                       0
% 3.16/1.01  smt_fast_solver_calls:                  0
% 3.16/1.01  prop_num_of_clauses:                    3048
% 3.16/1.01  prop_preprocess_simplified:             7136
% 3.16/1.01  prop_fo_subsumed:                       25
% 3.16/1.01  prop_solver_time:                       0.
% 3.16/1.01  smt_solver_time:                        0.
% 3.16/1.01  smt_fast_solver_time:                   0.
% 3.16/1.01  prop_fast_solver_time:                  0.
% 3.16/1.01  prop_unsat_core_time:                   0.
% 3.16/1.01  
% 3.16/1.01  ------ QBF
% 3.16/1.01  
% 3.16/1.01  qbf_q_res:                              0
% 3.16/1.01  qbf_num_tautologies:                    0
% 3.16/1.01  qbf_prep_cycles:                        0
% 3.16/1.01  
% 3.16/1.01  ------ BMC1
% 3.16/1.01  
% 3.16/1.01  bmc1_current_bound:                     -1
% 3.16/1.01  bmc1_last_solved_bound:                 -1
% 3.16/1.01  bmc1_unsat_core_size:                   -1
% 3.16/1.01  bmc1_unsat_core_parents_size:           -1
% 3.16/1.01  bmc1_merge_next_fun:                    0
% 3.16/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.16/1.01  
% 3.16/1.01  ------ Instantiation
% 3.16/1.01  
% 3.16/1.01  inst_num_of_clauses:                    863
% 3.16/1.01  inst_num_in_passive:                    247
% 3.16/1.01  inst_num_in_active:                     353
% 3.16/1.01  inst_num_in_unprocessed:                264
% 3.16/1.01  inst_num_of_loops:                      370
% 3.16/1.01  inst_num_of_learning_restarts:          0
% 3.16/1.01  inst_num_moves_active_passive:          14
% 3.16/1.01  inst_lit_activity:                      0
% 3.16/1.01  inst_lit_activity_moves:                0
% 3.16/1.01  inst_num_tautologies:                   0
% 3.16/1.01  inst_num_prop_implied:                  0
% 3.16/1.01  inst_num_existing_simplified:           0
% 3.16/1.01  inst_num_eq_res_simplified:             0
% 3.16/1.01  inst_num_child_elim:                    0
% 3.16/1.01  inst_num_of_dismatching_blockings:      776
% 3.16/1.01  inst_num_of_non_proper_insts:           993
% 3.16/1.01  inst_num_of_duplicates:                 0
% 3.16/1.01  inst_inst_num_from_inst_to_res:         0
% 3.16/1.01  inst_dismatching_checking_time:         0.
% 3.16/1.01  
% 3.16/1.01  ------ Resolution
% 3.16/1.01  
% 3.16/1.01  res_num_of_clauses:                     0
% 3.16/1.01  res_num_in_passive:                     0
% 3.16/1.01  res_num_in_active:                      0
% 3.16/1.01  res_num_of_loops:                       118
% 3.16/1.01  res_forward_subset_subsumed:            103
% 3.16/1.01  res_backward_subset_subsumed:           2
% 3.16/1.01  res_forward_subsumed:                   0
% 3.16/1.01  res_backward_subsumed:                  0
% 3.16/1.01  res_forward_subsumption_resolution:     0
% 3.16/1.01  res_backward_subsumption_resolution:    0
% 3.16/1.01  res_clause_to_clause_subsumption:       608
% 3.16/1.01  res_orphan_elimination:                 0
% 3.16/1.01  res_tautology_del:                      56
% 3.16/1.01  res_num_eq_res_simplified:              0
% 3.16/1.01  res_num_sel_changes:                    0
% 3.16/1.01  res_moves_from_active_to_pass:          0
% 3.16/1.01  
% 3.16/1.01  ------ Superposition
% 3.16/1.01  
% 3.16/1.01  sup_time_total:                         0.
% 3.16/1.01  sup_time_generating:                    0.
% 3.16/1.01  sup_time_sim_full:                      0.
% 3.16/1.01  sup_time_sim_immed:                     0.
% 3.16/1.01  
% 3.16/1.01  sup_num_of_clauses:                     156
% 3.16/1.01  sup_num_in_active:                      72
% 3.16/1.01  sup_num_in_passive:                     84
% 3.16/1.01  sup_num_of_loops:                       73
% 3.16/1.01  sup_fw_superposition:                   73
% 3.16/1.01  sup_bw_superposition:                   117
% 3.16/1.01  sup_immediate_simplified:               72
% 3.16/1.01  sup_given_eliminated:                   0
% 3.16/1.01  comparisons_done:                       0
% 3.16/1.01  comparisons_avoided:                    0
% 3.16/1.01  
% 3.16/1.01  ------ Simplifications
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  sim_fw_subset_subsumed:                 10
% 3.16/1.01  sim_bw_subset_subsumed:                 3
% 3.16/1.01  sim_fw_subsumed:                        7
% 3.16/1.01  sim_bw_subsumed:                        4
% 3.16/1.01  sim_fw_subsumption_res:                 8
% 3.16/1.01  sim_bw_subsumption_res:                 0
% 3.16/1.01  sim_tautology_del:                      0
% 3.16/1.01  sim_eq_tautology_del:                   2
% 3.16/1.01  sim_eq_res_simp:                        0
% 3.16/1.01  sim_fw_demodulated:                     39
% 3.16/1.01  sim_bw_demodulated:                     2
% 3.16/1.01  sim_light_normalised:                   32
% 3.16/1.01  sim_joinable_taut:                      0
% 3.16/1.01  sim_joinable_simp:                      0
% 3.16/1.01  sim_ac_normalised:                      0
% 3.16/1.01  sim_smt_subsumption:                    0
% 3.16/1.01  
%------------------------------------------------------------------------------
