%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:49 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 385 expanded)
%              Number of clauses        :   56 ( 104 expanded)
%              Number of leaves         :   10 (  99 expanded)
%              Depth                    :   19
%              Number of atoms          :  341 (2471 expanded)
%              Number of equality atoms :  177 (1033 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
                & k2_relat_1(X1) = k1_relat_1(X0)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k2_funct_1(X0) != sK1
        & k5_relat_1(sK1,X0) = k6_relat_1(k2_relat_1(X0))
        & k2_relat_1(sK1) = k1_relat_1(X0)
        & v2_funct_1(X0)
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
            & k2_relat_1(X1) = k1_relat_1(X0)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k5_relat_1(X1,sK0) = k6_relat_1(k2_relat_1(sK0))
          & k2_relat_1(X1) = k1_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k2_funct_1(sK0) != sK1
    & k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0))
    & k2_relat_1(sK1) = k1_relat_1(sK0)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f28,f27])).

fof(f49,plain,(
    k2_relat_1(sK1) = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f44,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_619,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_16,negated_conjecture,
    ( k2_relat_1(sK1) = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_617,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1482,plain,
    ( k1_relat_1(k5_relat_1(sK1,X0)) = k1_relat_1(sK1)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_617])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1519,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(sK1,X0)) = k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1482,c_24])).

cnf(c_1520,plain,
    ( k1_relat_1(k5_relat_1(sK1,X0)) = k1_relat_1(sK1)
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1519])).

cnf(c_1528,plain,
    ( k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_619,c_1520])).

cnf(c_15,negated_conjecture,
    ( k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1538,plain,
    ( k1_relat_1(k6_relat_1(k2_relat_1(sK0))) = k1_relat_1(sK1)
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1528,c_15])).

cnf(c_6,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1539,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | v1_relat_1(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1538,c_6])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_22,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1665,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1539,c_22])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_97,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X0) != k1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_12])).

cnf(c_98,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X0) != k1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_97])).

cnf(c_605,plain,
    ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_98])).

cnf(c_929,plain,
    ( k2_funct_1(sK1) = sK0
    | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0))
    | k2_relat_1(sK1) != k1_relat_1(sK0)
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_605])).

cnf(c_930,plain,
    ( k2_funct_1(sK1) = sK0
    | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0))
    | k1_relat_1(sK0) != k1_relat_1(sK0)
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_929,c_16])).

cnf(c_931,plain,
    ( k2_funct_1(sK1) = sK0
    | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0))
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_930])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_932,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK1) = sK0
    | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_931])).

cnf(c_1093,plain,
    ( k2_funct_1(sK1) = sK0
    | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_931,c_21,c_20,c_19,c_18,c_932])).

cnf(c_1668,plain,
    ( k2_funct_1(sK1) = sK0
    | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k1_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_1665,c_1093])).

cnf(c_1672,plain,
    ( k2_funct_1(sK1) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1668])).

cnf(c_609,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_616,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1407,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_616])).

cnf(c_23,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_25,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1669,plain,
    ( k6_relat_1(k1_relat_1(sK1)) = k5_relat_1(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_1665,c_15])).

cnf(c_611,plain,
    ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1680,plain,
    ( v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v2_funct_1(sK1) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1669,c_611])).

cnf(c_1851,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1407,c_22,c_23,c_24,c_25,c_1680])).

cnf(c_3211,plain,
    ( k4_relat_1(sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_1672,c_1851])).

cnf(c_608,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_618,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1186,plain,
    ( k4_relat_1(k4_relat_1(sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_608,c_618])).

cnf(c_3345,plain,
    ( k4_relat_1(sK0) = sK1 ),
    inference(demodulation,[status(thm)],[c_3211,c_1186])).

cnf(c_607,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1408,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | v2_funct_1(sK0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_607,c_616])).

cnf(c_17,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_40,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2110,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1408,c_21,c_20,c_17,c_40])).

cnf(c_14,negated_conjecture,
    ( k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2113,plain,
    ( k4_relat_1(sK0) != sK1 ),
    inference(demodulation,[status(thm)],[c_2110,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3345,c_2113])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:56:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.22/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/0.98  
% 2.22/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.22/0.98  
% 2.22/0.98  ------  iProver source info
% 2.22/0.98  
% 2.22/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.22/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.22/0.98  git: non_committed_changes: false
% 2.22/0.98  git: last_make_outside_of_git: false
% 2.22/0.98  
% 2.22/0.98  ------ 
% 2.22/0.98  
% 2.22/0.98  ------ Input Options
% 2.22/0.98  
% 2.22/0.98  --out_options                           all
% 2.22/0.98  --tptp_safe_out                         true
% 2.22/0.98  --problem_path                          ""
% 2.22/0.98  --include_path                          ""
% 2.22/0.98  --clausifier                            res/vclausify_rel
% 2.22/0.98  --clausifier_options                    --mode clausify
% 2.22/0.98  --stdin                                 false
% 2.22/0.98  --stats_out                             all
% 2.22/0.98  
% 2.22/0.98  ------ General Options
% 2.22/0.98  
% 2.22/0.98  --fof                                   false
% 2.22/0.98  --time_out_real                         305.
% 2.22/0.98  --time_out_virtual                      -1.
% 2.22/0.98  --symbol_type_check                     false
% 2.22/0.98  --clausify_out                          false
% 2.22/0.98  --sig_cnt_out                           false
% 2.22/0.98  --trig_cnt_out                          false
% 2.22/0.98  --trig_cnt_out_tolerance                1.
% 2.22/0.98  --trig_cnt_out_sk_spl                   false
% 2.22/0.98  --abstr_cl_out                          false
% 2.22/0.98  
% 2.22/0.98  ------ Global Options
% 2.22/0.98  
% 2.22/0.98  --schedule                              default
% 2.22/0.98  --add_important_lit                     false
% 2.22/0.98  --prop_solver_per_cl                    1000
% 2.22/0.98  --min_unsat_core                        false
% 2.22/0.98  --soft_assumptions                      false
% 2.22/0.98  --soft_lemma_size                       3
% 2.22/0.98  --prop_impl_unit_size                   0
% 2.22/0.98  --prop_impl_unit                        []
% 2.22/0.98  --share_sel_clauses                     true
% 2.22/0.98  --reset_solvers                         false
% 2.22/0.98  --bc_imp_inh                            [conj_cone]
% 2.22/0.98  --conj_cone_tolerance                   3.
% 2.22/0.98  --extra_neg_conj                        none
% 2.22/0.98  --large_theory_mode                     true
% 2.22/0.98  --prolific_symb_bound                   200
% 2.22/0.98  --lt_threshold                          2000
% 2.22/0.98  --clause_weak_htbl                      true
% 2.22/0.98  --gc_record_bc_elim                     false
% 2.22/0.98  
% 2.22/0.98  ------ Preprocessing Options
% 2.22/0.98  
% 2.22/0.98  --preprocessing_flag                    true
% 2.22/0.98  --time_out_prep_mult                    0.1
% 2.22/0.98  --splitting_mode                        input
% 2.22/0.98  --splitting_grd                         true
% 2.22/0.98  --splitting_cvd                         false
% 2.22/0.98  --splitting_cvd_svl                     false
% 2.22/0.98  --splitting_nvd                         32
% 2.22/0.98  --sub_typing                            true
% 2.22/0.98  --prep_gs_sim                           true
% 2.22/0.98  --prep_unflatten                        true
% 2.22/0.98  --prep_res_sim                          true
% 2.22/0.98  --prep_upred                            true
% 2.22/0.98  --prep_sem_filter                       exhaustive
% 2.22/0.98  --prep_sem_filter_out                   false
% 2.22/0.98  --pred_elim                             true
% 2.22/0.98  --res_sim_input                         true
% 2.22/0.98  --eq_ax_congr_red                       true
% 2.22/0.98  --pure_diseq_elim                       true
% 2.22/0.98  --brand_transform                       false
% 2.22/0.98  --non_eq_to_eq                          false
% 2.22/0.98  --prep_def_merge                        true
% 2.22/0.98  --prep_def_merge_prop_impl              false
% 2.22/0.98  --prep_def_merge_mbd                    true
% 2.22/0.98  --prep_def_merge_tr_red                 false
% 2.22/0.98  --prep_def_merge_tr_cl                  false
% 2.22/0.98  --smt_preprocessing                     true
% 2.22/0.98  --smt_ac_axioms                         fast
% 2.22/0.98  --preprocessed_out                      false
% 2.22/0.98  --preprocessed_stats                    false
% 2.22/0.98  
% 2.22/0.98  ------ Abstraction refinement Options
% 2.22/0.98  
% 2.22/0.98  --abstr_ref                             []
% 2.22/0.98  --abstr_ref_prep                        false
% 2.22/0.98  --abstr_ref_until_sat                   false
% 2.22/0.98  --abstr_ref_sig_restrict                funpre
% 2.22/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/0.98  --abstr_ref_under                       []
% 2.22/0.98  
% 2.22/0.98  ------ SAT Options
% 2.22/0.98  
% 2.22/0.98  --sat_mode                              false
% 2.22/0.98  --sat_fm_restart_options                ""
% 2.22/0.98  --sat_gr_def                            false
% 2.22/0.98  --sat_epr_types                         true
% 2.22/0.98  --sat_non_cyclic_types                  false
% 2.22/0.98  --sat_finite_models                     false
% 2.22/0.98  --sat_fm_lemmas                         false
% 2.22/0.98  --sat_fm_prep                           false
% 2.22/0.98  --sat_fm_uc_incr                        true
% 2.22/0.98  --sat_out_model                         small
% 2.22/0.98  --sat_out_clauses                       false
% 2.22/0.98  
% 2.22/0.98  ------ QBF Options
% 2.22/0.98  
% 2.22/0.98  --qbf_mode                              false
% 2.22/0.98  --qbf_elim_univ                         false
% 2.22/0.98  --qbf_dom_inst                          none
% 2.22/0.98  --qbf_dom_pre_inst                      false
% 2.22/0.98  --qbf_sk_in                             false
% 2.22/0.98  --qbf_pred_elim                         true
% 2.22/0.98  --qbf_split                             512
% 2.22/0.98  
% 2.22/0.98  ------ BMC1 Options
% 2.22/0.98  
% 2.22/0.98  --bmc1_incremental                      false
% 2.22/0.98  --bmc1_axioms                           reachable_all
% 2.22/0.98  --bmc1_min_bound                        0
% 2.22/0.98  --bmc1_max_bound                        -1
% 2.22/0.98  --bmc1_max_bound_default                -1
% 2.22/0.98  --bmc1_symbol_reachability              true
% 2.22/0.98  --bmc1_property_lemmas                  false
% 2.22/0.98  --bmc1_k_induction                      false
% 2.22/0.98  --bmc1_non_equiv_states                 false
% 2.22/0.98  --bmc1_deadlock                         false
% 2.22/0.98  --bmc1_ucm                              false
% 2.22/0.98  --bmc1_add_unsat_core                   none
% 2.22/0.98  --bmc1_unsat_core_children              false
% 2.22/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/0.98  --bmc1_out_stat                         full
% 2.22/0.98  --bmc1_ground_init                      false
% 2.22/0.98  --bmc1_pre_inst_next_state              false
% 2.22/0.98  --bmc1_pre_inst_state                   false
% 2.22/0.98  --bmc1_pre_inst_reach_state             false
% 2.22/0.98  --bmc1_out_unsat_core                   false
% 2.22/0.98  --bmc1_aig_witness_out                  false
% 2.22/0.98  --bmc1_verbose                          false
% 2.22/0.98  --bmc1_dump_clauses_tptp                false
% 2.22/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.22/0.98  --bmc1_dump_file                        -
% 2.22/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.22/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.22/0.98  --bmc1_ucm_extend_mode                  1
% 2.22/0.98  --bmc1_ucm_init_mode                    2
% 2.22/0.98  --bmc1_ucm_cone_mode                    none
% 2.22/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.22/0.98  --bmc1_ucm_relax_model                  4
% 2.22/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.22/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/0.98  --bmc1_ucm_layered_model                none
% 2.22/0.98  --bmc1_ucm_max_lemma_size               10
% 2.22/0.98  
% 2.22/0.98  ------ AIG Options
% 2.22/0.98  
% 2.22/0.98  --aig_mode                              false
% 2.22/0.98  
% 2.22/0.98  ------ Instantiation Options
% 2.22/0.98  
% 2.22/0.98  --instantiation_flag                    true
% 2.22/0.98  --inst_sos_flag                         false
% 2.22/0.98  --inst_sos_phase                        true
% 2.22/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/0.98  --inst_lit_sel_side                     num_symb
% 2.22/0.98  --inst_solver_per_active                1400
% 2.22/0.98  --inst_solver_calls_frac                1.
% 2.22/0.98  --inst_passive_queue_type               priority_queues
% 2.22/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/0.98  --inst_passive_queues_freq              [25;2]
% 2.22/0.98  --inst_dismatching                      true
% 2.22/0.98  --inst_eager_unprocessed_to_passive     true
% 2.22/0.98  --inst_prop_sim_given                   true
% 2.22/0.98  --inst_prop_sim_new                     false
% 2.22/0.98  --inst_subs_new                         false
% 2.22/0.98  --inst_eq_res_simp                      false
% 2.22/0.98  --inst_subs_given                       false
% 2.22/0.98  --inst_orphan_elimination               true
% 2.22/0.98  --inst_learning_loop_flag               true
% 2.22/0.98  --inst_learning_start                   3000
% 2.22/0.98  --inst_learning_factor                  2
% 2.22/0.98  --inst_start_prop_sim_after_learn       3
% 2.22/0.98  --inst_sel_renew                        solver
% 2.22/0.98  --inst_lit_activity_flag                true
% 2.22/0.98  --inst_restr_to_given                   false
% 2.22/0.98  --inst_activity_threshold               500
% 2.22/0.98  --inst_out_proof                        true
% 2.22/0.98  
% 2.22/0.98  ------ Resolution Options
% 2.22/0.98  
% 2.22/0.98  --resolution_flag                       true
% 2.22/0.98  --res_lit_sel                           adaptive
% 2.22/0.98  --res_lit_sel_side                      none
% 2.22/0.98  --res_ordering                          kbo
% 2.22/0.98  --res_to_prop_solver                    active
% 2.22/0.98  --res_prop_simpl_new                    false
% 2.22/0.98  --res_prop_simpl_given                  true
% 2.22/0.98  --res_passive_queue_type                priority_queues
% 2.22/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/0.98  --res_passive_queues_freq               [15;5]
% 2.22/0.98  --res_forward_subs                      full
% 2.22/0.98  --res_backward_subs                     full
% 2.22/0.98  --res_forward_subs_resolution           true
% 2.22/0.98  --res_backward_subs_resolution          true
% 2.22/0.98  --res_orphan_elimination                true
% 2.22/0.98  --res_time_limit                        2.
% 2.22/0.98  --res_out_proof                         true
% 2.22/0.98  
% 2.22/0.98  ------ Superposition Options
% 2.22/0.98  
% 2.22/0.98  --superposition_flag                    true
% 2.22/0.98  --sup_passive_queue_type                priority_queues
% 2.22/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.22/0.98  --demod_completeness_check              fast
% 2.22/0.98  --demod_use_ground                      true
% 2.22/0.98  --sup_to_prop_solver                    passive
% 2.22/0.98  --sup_prop_simpl_new                    true
% 2.22/0.98  --sup_prop_simpl_given                  true
% 2.22/0.98  --sup_fun_splitting                     false
% 2.22/0.98  --sup_smt_interval                      50000
% 2.22/0.98  
% 2.22/0.98  ------ Superposition Simplification Setup
% 2.22/0.98  
% 2.22/0.98  --sup_indices_passive                   []
% 2.22/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.98  --sup_full_bw                           [BwDemod]
% 2.22/0.98  --sup_immed_triv                        [TrivRules]
% 2.22/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.98  --sup_immed_bw_main                     []
% 2.22/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.98  
% 2.22/0.98  ------ Combination Options
% 2.22/0.98  
% 2.22/0.98  --comb_res_mult                         3
% 2.22/0.98  --comb_sup_mult                         2
% 2.22/0.98  --comb_inst_mult                        10
% 2.22/0.98  
% 2.22/0.98  ------ Debug Options
% 2.22/0.98  
% 2.22/0.98  --dbg_backtrace                         false
% 2.22/0.98  --dbg_dump_prop_clauses                 false
% 2.22/0.98  --dbg_dump_prop_clauses_file            -
% 2.22/0.98  --dbg_out_stat                          false
% 2.22/0.98  ------ Parsing...
% 2.22/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.22/0.98  
% 2.22/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.22/0.98  
% 2.22/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.22/0.98  
% 2.22/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.22/0.98  ------ Proving...
% 2.22/0.98  ------ Problem Properties 
% 2.22/0.98  
% 2.22/0.98  
% 2.22/0.98  clauses                                 21
% 2.22/0.98  conjectures                             8
% 2.22/0.98  EPR                                     7
% 2.22/0.98  Horn                                    21
% 2.22/0.98  unary                                   13
% 2.22/0.98  binary                                  1
% 2.22/0.98  lits                                    53
% 2.22/0.98  lits eq                                 15
% 2.22/0.98  fd_pure                                 0
% 2.22/0.98  fd_pseudo                               0
% 2.22/0.98  fd_cond                                 0
% 2.22/0.98  fd_pseudo_cond                          2
% 2.22/0.98  AC symbols                              0
% 2.22/0.98  
% 2.22/0.98  ------ Schedule dynamic 5 is on 
% 2.22/0.98  
% 2.22/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.22/0.98  
% 2.22/0.98  
% 2.22/0.98  ------ 
% 2.22/0.98  Current options:
% 2.22/0.98  ------ 
% 2.22/0.98  
% 2.22/0.98  ------ Input Options
% 2.22/0.98  
% 2.22/0.98  --out_options                           all
% 2.22/0.98  --tptp_safe_out                         true
% 2.22/0.98  --problem_path                          ""
% 2.22/0.98  --include_path                          ""
% 2.22/0.98  --clausifier                            res/vclausify_rel
% 2.22/0.98  --clausifier_options                    --mode clausify
% 2.22/0.98  --stdin                                 false
% 2.22/0.98  --stats_out                             all
% 2.22/0.98  
% 2.22/0.98  ------ General Options
% 2.22/0.98  
% 2.22/0.98  --fof                                   false
% 2.22/0.98  --time_out_real                         305.
% 2.22/0.98  --time_out_virtual                      -1.
% 2.22/0.98  --symbol_type_check                     false
% 2.22/0.98  --clausify_out                          false
% 2.22/0.98  --sig_cnt_out                           false
% 2.22/0.98  --trig_cnt_out                          false
% 2.22/0.98  --trig_cnt_out_tolerance                1.
% 2.22/0.98  --trig_cnt_out_sk_spl                   false
% 2.22/0.98  --abstr_cl_out                          false
% 2.22/0.98  
% 2.22/0.98  ------ Global Options
% 2.22/0.98  
% 2.22/0.98  --schedule                              default
% 2.22/0.98  --add_important_lit                     false
% 2.22/0.98  --prop_solver_per_cl                    1000
% 2.22/0.98  --min_unsat_core                        false
% 2.22/0.98  --soft_assumptions                      false
% 2.22/0.98  --soft_lemma_size                       3
% 2.22/0.98  --prop_impl_unit_size                   0
% 2.22/0.98  --prop_impl_unit                        []
% 2.22/0.98  --share_sel_clauses                     true
% 2.22/0.98  --reset_solvers                         false
% 2.22/0.98  --bc_imp_inh                            [conj_cone]
% 2.22/0.98  --conj_cone_tolerance                   3.
% 2.22/0.98  --extra_neg_conj                        none
% 2.22/0.98  --large_theory_mode                     true
% 2.22/0.98  --prolific_symb_bound                   200
% 2.22/0.98  --lt_threshold                          2000
% 2.22/0.98  --clause_weak_htbl                      true
% 2.22/0.98  --gc_record_bc_elim                     false
% 2.22/0.98  
% 2.22/0.98  ------ Preprocessing Options
% 2.22/0.98  
% 2.22/0.98  --preprocessing_flag                    true
% 2.22/0.98  --time_out_prep_mult                    0.1
% 2.22/0.98  --splitting_mode                        input
% 2.22/0.98  --splitting_grd                         true
% 2.22/0.98  --splitting_cvd                         false
% 2.22/0.98  --splitting_cvd_svl                     false
% 2.22/0.98  --splitting_nvd                         32
% 2.22/0.98  --sub_typing                            true
% 2.22/0.98  --prep_gs_sim                           true
% 2.22/0.98  --prep_unflatten                        true
% 2.22/0.98  --prep_res_sim                          true
% 2.22/0.98  --prep_upred                            true
% 2.22/0.98  --prep_sem_filter                       exhaustive
% 2.22/0.98  --prep_sem_filter_out                   false
% 2.22/0.98  --pred_elim                             true
% 2.22/0.98  --res_sim_input                         true
% 2.22/0.98  --eq_ax_congr_red                       true
% 2.22/0.98  --pure_diseq_elim                       true
% 2.22/0.98  --brand_transform                       false
% 2.22/0.98  --non_eq_to_eq                          false
% 2.22/0.98  --prep_def_merge                        true
% 2.22/0.98  --prep_def_merge_prop_impl              false
% 2.22/0.98  --prep_def_merge_mbd                    true
% 2.22/0.98  --prep_def_merge_tr_red                 false
% 2.22/0.98  --prep_def_merge_tr_cl                  false
% 2.22/0.98  --smt_preprocessing                     true
% 2.22/0.98  --smt_ac_axioms                         fast
% 2.22/0.98  --preprocessed_out                      false
% 2.22/0.98  --preprocessed_stats                    false
% 2.22/0.98  
% 2.22/0.98  ------ Abstraction refinement Options
% 2.22/0.98  
% 2.22/0.98  --abstr_ref                             []
% 2.22/0.98  --abstr_ref_prep                        false
% 2.22/0.98  --abstr_ref_until_sat                   false
% 2.22/0.98  --abstr_ref_sig_restrict                funpre
% 2.22/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/0.98  --abstr_ref_under                       []
% 2.22/0.98  
% 2.22/0.98  ------ SAT Options
% 2.22/0.98  
% 2.22/0.98  --sat_mode                              false
% 2.22/0.98  --sat_fm_restart_options                ""
% 2.22/0.98  --sat_gr_def                            false
% 2.22/0.98  --sat_epr_types                         true
% 2.22/0.98  --sat_non_cyclic_types                  false
% 2.22/0.98  --sat_finite_models                     false
% 2.22/0.98  --sat_fm_lemmas                         false
% 2.22/0.98  --sat_fm_prep                           false
% 2.22/0.98  --sat_fm_uc_incr                        true
% 2.22/0.98  --sat_out_model                         small
% 2.22/0.98  --sat_out_clauses                       false
% 2.22/0.98  
% 2.22/0.98  ------ QBF Options
% 2.22/0.98  
% 2.22/0.98  --qbf_mode                              false
% 2.22/0.98  --qbf_elim_univ                         false
% 2.22/0.98  --qbf_dom_inst                          none
% 2.22/0.98  --qbf_dom_pre_inst                      false
% 2.22/0.98  --qbf_sk_in                             false
% 2.22/0.98  --qbf_pred_elim                         true
% 2.22/0.98  --qbf_split                             512
% 2.22/0.98  
% 2.22/0.98  ------ BMC1 Options
% 2.22/0.98  
% 2.22/0.98  --bmc1_incremental                      false
% 2.22/0.98  --bmc1_axioms                           reachable_all
% 2.22/0.98  --bmc1_min_bound                        0
% 2.22/0.98  --bmc1_max_bound                        -1
% 2.22/0.98  --bmc1_max_bound_default                -1
% 2.22/0.98  --bmc1_symbol_reachability              true
% 2.22/0.98  --bmc1_property_lemmas                  false
% 2.22/0.98  --bmc1_k_induction                      false
% 2.22/0.98  --bmc1_non_equiv_states                 false
% 2.22/0.98  --bmc1_deadlock                         false
% 2.22/0.98  --bmc1_ucm                              false
% 2.22/0.98  --bmc1_add_unsat_core                   none
% 2.22/0.98  --bmc1_unsat_core_children              false
% 2.22/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/0.98  --bmc1_out_stat                         full
% 2.22/0.98  --bmc1_ground_init                      false
% 2.22/0.98  --bmc1_pre_inst_next_state              false
% 2.22/0.98  --bmc1_pre_inst_state                   false
% 2.22/0.98  --bmc1_pre_inst_reach_state             false
% 2.22/0.98  --bmc1_out_unsat_core                   false
% 2.22/0.98  --bmc1_aig_witness_out                  false
% 2.22/0.98  --bmc1_verbose                          false
% 2.22/0.98  --bmc1_dump_clauses_tptp                false
% 2.22/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.22/0.98  --bmc1_dump_file                        -
% 2.22/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.22/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.22/0.98  --bmc1_ucm_extend_mode                  1
% 2.22/0.98  --bmc1_ucm_init_mode                    2
% 2.22/0.98  --bmc1_ucm_cone_mode                    none
% 2.22/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.22/0.98  --bmc1_ucm_relax_model                  4
% 2.22/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.22/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/0.98  --bmc1_ucm_layered_model                none
% 2.22/0.98  --bmc1_ucm_max_lemma_size               10
% 2.22/0.98  
% 2.22/0.98  ------ AIG Options
% 2.22/0.98  
% 2.22/0.98  --aig_mode                              false
% 2.22/0.98  
% 2.22/0.98  ------ Instantiation Options
% 2.22/0.98  
% 2.22/0.98  --instantiation_flag                    true
% 2.22/0.98  --inst_sos_flag                         false
% 2.22/0.98  --inst_sos_phase                        true
% 2.22/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/0.98  --inst_lit_sel_side                     none
% 2.22/0.98  --inst_solver_per_active                1400
% 2.22/0.98  --inst_solver_calls_frac                1.
% 2.22/0.98  --inst_passive_queue_type               priority_queues
% 2.22/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/0.98  --inst_passive_queues_freq              [25;2]
% 2.22/0.98  --inst_dismatching                      true
% 2.22/0.98  --inst_eager_unprocessed_to_passive     true
% 2.22/0.98  --inst_prop_sim_given                   true
% 2.22/0.98  --inst_prop_sim_new                     false
% 2.22/0.98  --inst_subs_new                         false
% 2.22/0.98  --inst_eq_res_simp                      false
% 2.22/0.98  --inst_subs_given                       false
% 2.22/0.98  --inst_orphan_elimination               true
% 2.22/0.98  --inst_learning_loop_flag               true
% 2.22/0.98  --inst_learning_start                   3000
% 2.22/0.98  --inst_learning_factor                  2
% 2.22/0.98  --inst_start_prop_sim_after_learn       3
% 2.22/0.98  --inst_sel_renew                        solver
% 2.22/0.98  --inst_lit_activity_flag                true
% 2.22/0.98  --inst_restr_to_given                   false
% 2.22/0.98  --inst_activity_threshold               500
% 2.22/0.98  --inst_out_proof                        true
% 2.22/0.98  
% 2.22/0.98  ------ Resolution Options
% 2.22/0.98  
% 2.22/0.98  --resolution_flag                       false
% 2.22/0.98  --res_lit_sel                           adaptive
% 2.22/0.98  --res_lit_sel_side                      none
% 2.22/0.98  --res_ordering                          kbo
% 2.22/0.98  --res_to_prop_solver                    active
% 2.22/0.98  --res_prop_simpl_new                    false
% 2.22/0.98  --res_prop_simpl_given                  true
% 2.22/0.98  --res_passive_queue_type                priority_queues
% 2.22/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/0.98  --res_passive_queues_freq               [15;5]
% 2.22/0.98  --res_forward_subs                      full
% 2.22/0.98  --res_backward_subs                     full
% 2.22/0.98  --res_forward_subs_resolution           true
% 2.22/0.98  --res_backward_subs_resolution          true
% 2.22/0.98  --res_orphan_elimination                true
% 2.22/0.98  --res_time_limit                        2.
% 2.22/0.98  --res_out_proof                         true
% 2.22/0.98  
% 2.22/0.98  ------ Superposition Options
% 2.22/0.98  
% 2.22/0.98  --superposition_flag                    true
% 2.22/0.98  --sup_passive_queue_type                priority_queues
% 2.22/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.22/0.98  --demod_completeness_check              fast
% 2.22/0.98  --demod_use_ground                      true
% 2.22/0.98  --sup_to_prop_solver                    passive
% 2.22/0.98  --sup_prop_simpl_new                    true
% 2.22/0.98  --sup_prop_simpl_given                  true
% 2.22/0.98  --sup_fun_splitting                     false
% 2.22/0.98  --sup_smt_interval                      50000
% 2.22/0.98  
% 2.22/0.98  ------ Superposition Simplification Setup
% 2.22/0.98  
% 2.22/0.98  --sup_indices_passive                   []
% 2.22/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.98  --sup_full_bw                           [BwDemod]
% 2.22/0.98  --sup_immed_triv                        [TrivRules]
% 2.22/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.98  --sup_immed_bw_main                     []
% 2.22/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.98  
% 2.22/0.98  ------ Combination Options
% 2.22/0.98  
% 2.22/0.98  --comb_res_mult                         3
% 2.22/0.98  --comb_sup_mult                         2
% 2.22/0.98  --comb_inst_mult                        10
% 2.22/0.98  
% 2.22/0.98  ------ Debug Options
% 2.22/0.98  
% 2.22/0.98  --dbg_backtrace                         false
% 2.22/0.98  --dbg_dump_prop_clauses                 false
% 2.22/0.98  --dbg_dump_prop_clauses_file            -
% 2.22/0.98  --dbg_out_stat                          false
% 2.22/0.98  
% 2.22/0.98  
% 2.22/0.98  
% 2.22/0.98  
% 2.22/0.98  ------ Proving...
% 2.22/0.98  
% 2.22/0.98  
% 2.22/0.98  % SZS status Theorem for theBenchmark.p
% 2.22/0.98  
% 2.22/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.22/0.98  
% 2.22/0.98  fof(f1,axiom,(
% 2.22/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f25,plain,(
% 2.22/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/0.98    inference(nnf_transformation,[],[f1])).
% 2.22/0.98  
% 2.22/0.98  fof(f26,plain,(
% 2.22/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/0.98    inference(flattening,[],[f25])).
% 2.22/0.98  
% 2.22/0.98  fof(f31,plain,(
% 2.22/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.22/0.98    inference(cnf_transformation,[],[f26])).
% 2.22/0.98  
% 2.22/0.98  fof(f52,plain,(
% 2.22/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.22/0.98    inference(equality_resolution,[],[f31])).
% 2.22/0.98  
% 2.22/0.98  fof(f10,conjecture,(
% 2.22/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f11,negated_conjecture,(
% 2.22/0.98    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.22/0.98    inference(negated_conjecture,[],[f10])).
% 2.22/0.98  
% 2.22/0.98  fof(f23,plain,(
% 2.22/0.98    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.22/0.98    inference(ennf_transformation,[],[f11])).
% 2.22/0.98  
% 2.22/0.98  fof(f24,plain,(
% 2.22/0.98    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.22/0.98    inference(flattening,[],[f23])).
% 2.22/0.98  
% 2.22/0.98  fof(f28,plain,(
% 2.22/0.98    ( ! [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) != sK1 & k5_relat_1(sK1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(sK1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(sK1) & v1_relat_1(sK1))) )),
% 2.22/0.98    introduced(choice_axiom,[])).
% 2.22/0.98  
% 2.22/0.98  fof(f27,plain,(
% 2.22/0.98    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k5_relat_1(X1,sK0) = k6_relat_1(k2_relat_1(sK0)) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.22/0.98    introduced(choice_axiom,[])).
% 2.22/0.98  
% 2.22/0.98  fof(f29,plain,(
% 2.22/0.98    (k2_funct_1(sK0) != sK1 & k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) & k2_relat_1(sK1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.22/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f28,f27])).
% 2.22/0.98  
% 2.22/0.98  fof(f49,plain,(
% 2.22/0.98    k2_relat_1(sK1) = k1_relat_1(sK0)),
% 2.22/0.98    inference(cnf_transformation,[],[f29])).
% 2.22/0.98  
% 2.22/0.98  fof(f3,axiom,(
% 2.22/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f13,plain,(
% 2.22/0.98    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.22/0.98    inference(ennf_transformation,[],[f3])).
% 2.22/0.98  
% 2.22/0.98  fof(f14,plain,(
% 2.22/0.98    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.22/0.98    inference(flattening,[],[f13])).
% 2.22/0.98  
% 2.22/0.98  fof(f34,plain,(
% 2.22/0.98    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f14])).
% 2.22/0.98  
% 2.22/0.98  fof(f46,plain,(
% 2.22/0.98    v1_relat_1(sK1)),
% 2.22/0.98    inference(cnf_transformation,[],[f29])).
% 2.22/0.98  
% 2.22/0.98  fof(f50,plain,(
% 2.22/0.98    k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0))),
% 2.22/0.98    inference(cnf_transformation,[],[f29])).
% 2.22/0.98  
% 2.22/0.98  fof(f4,axiom,(
% 2.22/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f35,plain,(
% 2.22/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.22/0.98    inference(cnf_transformation,[],[f4])).
% 2.22/0.98  
% 2.22/0.98  fof(f44,plain,(
% 2.22/0.98    v1_relat_1(sK0)),
% 2.22/0.98    inference(cnf_transformation,[],[f29])).
% 2.22/0.98  
% 2.22/0.98  fof(f9,axiom,(
% 2.22/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f21,plain,(
% 2.22/0.98    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.22/0.98    inference(ennf_transformation,[],[f9])).
% 2.22/0.98  
% 2.22/0.98  fof(f22,plain,(
% 2.22/0.98    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.22/0.98    inference(flattening,[],[f21])).
% 2.22/0.98  
% 2.22/0.98  fof(f43,plain,(
% 2.22/0.98    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f22])).
% 2.22/0.98  
% 2.22/0.98  fof(f8,axiom,(
% 2.22/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f19,plain,(
% 2.22/0.98    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.22/0.98    inference(ennf_transformation,[],[f8])).
% 2.22/0.98  
% 2.22/0.98  fof(f20,plain,(
% 2.22/0.98    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.22/0.98    inference(flattening,[],[f19])).
% 2.22/0.98  
% 2.22/0.98  fof(f42,plain,(
% 2.22/0.98    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f20])).
% 2.22/0.98  
% 2.22/0.98  fof(f45,plain,(
% 2.22/0.98    v1_funct_1(sK0)),
% 2.22/0.98    inference(cnf_transformation,[],[f29])).
% 2.22/0.98  
% 2.22/0.98  fof(f47,plain,(
% 2.22/0.98    v1_funct_1(sK1)),
% 2.22/0.98    inference(cnf_transformation,[],[f29])).
% 2.22/0.98  
% 2.22/0.98  fof(f5,axiom,(
% 2.22/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f15,plain,(
% 2.22/0.98    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.22/0.98    inference(ennf_transformation,[],[f5])).
% 2.22/0.98  
% 2.22/0.98  fof(f16,plain,(
% 2.22/0.98    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.22/0.98    inference(flattening,[],[f15])).
% 2.22/0.98  
% 2.22/0.98  fof(f37,plain,(
% 2.22/0.98    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f16])).
% 2.22/0.98  
% 2.22/0.98  fof(f2,axiom,(
% 2.22/0.98    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f12,plain,(
% 2.22/0.98    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.22/0.98    inference(ennf_transformation,[],[f2])).
% 2.22/0.98  
% 2.22/0.98  fof(f33,plain,(
% 2.22/0.98    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f12])).
% 2.22/0.98  
% 2.22/0.98  fof(f48,plain,(
% 2.22/0.98    v2_funct_1(sK0)),
% 2.22/0.98    inference(cnf_transformation,[],[f29])).
% 2.22/0.98  
% 2.22/0.98  fof(f51,plain,(
% 2.22/0.98    k2_funct_1(sK0) != sK1),
% 2.22/0.98    inference(cnf_transformation,[],[f29])).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1,plain,
% 2.22/0.98      ( r1_tarski(X0,X0) ),
% 2.22/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_619,plain,
% 2.22/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_16,negated_conjecture,
% 2.22/0.98      ( k2_relat_1(sK1) = k1_relat_1(sK0) ),
% 2.22/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_4,plain,
% 2.22/0.98      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 2.22/0.98      | ~ v1_relat_1(X0)
% 2.22/0.98      | ~ v1_relat_1(X1)
% 2.22/0.98      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 2.22/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_617,plain,
% 2.22/0.98      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 2.22/0.98      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 2.22/0.98      | v1_relat_1(X0) != iProver_top
% 2.22/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1482,plain,
% 2.22/0.98      ( k1_relat_1(k5_relat_1(sK1,X0)) = k1_relat_1(sK1)
% 2.22/0.98      | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) != iProver_top
% 2.22/0.98      | v1_relat_1(X0) != iProver_top
% 2.22/0.98      | v1_relat_1(sK1) != iProver_top ),
% 2.22/0.98      inference(superposition,[status(thm)],[c_16,c_617]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_19,negated_conjecture,
% 2.22/0.98      ( v1_relat_1(sK1) ),
% 2.22/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_24,plain,
% 2.22/0.98      ( v1_relat_1(sK1) = iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1519,plain,
% 2.22/0.98      ( v1_relat_1(X0) != iProver_top
% 2.22/0.98      | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) != iProver_top
% 2.22/0.98      | k1_relat_1(k5_relat_1(sK1,X0)) = k1_relat_1(sK1) ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_1482,c_24]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1520,plain,
% 2.22/0.98      ( k1_relat_1(k5_relat_1(sK1,X0)) = k1_relat_1(sK1)
% 2.22/0.98      | r1_tarski(k1_relat_1(sK0),k1_relat_1(X0)) != iProver_top
% 2.22/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.22/0.98      inference(renaming,[status(thm)],[c_1519]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1528,plain,
% 2.22/0.98      ( k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)
% 2.22/0.98      | v1_relat_1(sK0) != iProver_top ),
% 2.22/0.98      inference(superposition,[status(thm)],[c_619,c_1520]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_15,negated_conjecture,
% 2.22/0.98      ( k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 2.22/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1538,plain,
% 2.22/0.98      ( k1_relat_1(k6_relat_1(k2_relat_1(sK0))) = k1_relat_1(sK1)
% 2.22/0.98      | v1_relat_1(sK0) != iProver_top ),
% 2.22/0.98      inference(light_normalisation,[status(thm)],[c_1528,c_15]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_6,plain,
% 2.22/0.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.22/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1539,plain,
% 2.22/0.98      ( k2_relat_1(sK0) = k1_relat_1(sK1)
% 2.22/0.98      | v1_relat_1(sK0) != iProver_top ),
% 2.22/0.98      inference(demodulation,[status(thm)],[c_1538,c_6]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_21,negated_conjecture,
% 2.22/0.98      ( v1_relat_1(sK0) ),
% 2.22/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_22,plain,
% 2.22/0.98      ( v1_relat_1(sK0) = iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1665,plain,
% 2.22/0.98      ( k2_relat_1(sK0) = k1_relat_1(sK1) ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_1539,c_22]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_13,plain,
% 2.22/0.98      ( ~ v1_funct_1(X0)
% 2.22/0.98      | ~ v1_funct_1(X1)
% 2.22/0.98      | ~ v2_funct_1(X0)
% 2.22/0.98      | ~ v1_relat_1(X0)
% 2.22/0.98      | ~ v1_relat_1(X1)
% 2.22/0.98      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
% 2.22/0.98      | k2_funct_1(X0) = X1
% 2.22/0.98      | k2_relat_1(X0) != k1_relat_1(X1) ),
% 2.22/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_12,plain,
% 2.22/0.98      ( ~ v1_funct_1(X0)
% 2.22/0.98      | ~ v1_funct_1(X1)
% 2.22/0.98      | v2_funct_1(X0)
% 2.22/0.98      | ~ v1_relat_1(X0)
% 2.22/0.98      | ~ v1_relat_1(X1)
% 2.22/0.98      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) ),
% 2.22/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_97,plain,
% 2.22/0.98      ( ~ v1_funct_1(X1)
% 2.22/0.98      | ~ v1_funct_1(X0)
% 2.22/0.98      | ~ v1_relat_1(X0)
% 2.22/0.98      | ~ v1_relat_1(X1)
% 2.22/0.98      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
% 2.22/0.98      | k2_funct_1(X0) = X1
% 2.22/0.98      | k2_relat_1(X0) != k1_relat_1(X1) ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_13,c_12]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_98,plain,
% 2.22/0.98      ( ~ v1_funct_1(X0)
% 2.22/0.98      | ~ v1_funct_1(X1)
% 2.22/0.98      | ~ v1_relat_1(X0)
% 2.22/0.98      | ~ v1_relat_1(X1)
% 2.22/0.98      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
% 2.22/0.98      | k2_funct_1(X0) = X1
% 2.22/0.98      | k2_relat_1(X0) != k1_relat_1(X1) ),
% 2.22/0.98      inference(renaming,[status(thm)],[c_97]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_605,plain,
% 2.22/0.98      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
% 2.22/0.98      | k2_funct_1(X0) = X1
% 2.22/0.98      | k2_relat_1(X0) != k1_relat_1(X1)
% 2.22/0.98      | v1_funct_1(X0) != iProver_top
% 2.22/0.98      | v1_funct_1(X1) != iProver_top
% 2.22/0.98      | v1_relat_1(X0) != iProver_top
% 2.22/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_98]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_929,plain,
% 2.22/0.98      ( k2_funct_1(sK1) = sK0
% 2.22/0.98      | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0))
% 2.22/0.98      | k2_relat_1(sK1) != k1_relat_1(sK0)
% 2.22/0.98      | v1_funct_1(sK1) != iProver_top
% 2.22/0.98      | v1_funct_1(sK0) != iProver_top
% 2.22/0.98      | v1_relat_1(sK1) != iProver_top
% 2.22/0.98      | v1_relat_1(sK0) != iProver_top ),
% 2.22/0.98      inference(superposition,[status(thm)],[c_15,c_605]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_930,plain,
% 2.22/0.98      ( k2_funct_1(sK1) = sK0
% 2.22/0.98      | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0))
% 2.22/0.98      | k1_relat_1(sK0) != k1_relat_1(sK0)
% 2.22/0.98      | v1_funct_1(sK1) != iProver_top
% 2.22/0.98      | v1_funct_1(sK0) != iProver_top
% 2.22/0.98      | v1_relat_1(sK1) != iProver_top
% 2.22/0.98      | v1_relat_1(sK0) != iProver_top ),
% 2.22/0.98      inference(light_normalisation,[status(thm)],[c_929,c_16]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_931,plain,
% 2.22/0.98      ( k2_funct_1(sK1) = sK0
% 2.22/0.98      | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0))
% 2.22/0.98      | v1_funct_1(sK1) != iProver_top
% 2.22/0.98      | v1_funct_1(sK0) != iProver_top
% 2.22/0.98      | v1_relat_1(sK1) != iProver_top
% 2.22/0.98      | v1_relat_1(sK0) != iProver_top ),
% 2.22/0.98      inference(equality_resolution_simp,[status(thm)],[c_930]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_20,negated_conjecture,
% 2.22/0.98      ( v1_funct_1(sK0) ),
% 2.22/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_18,negated_conjecture,
% 2.22/0.98      ( v1_funct_1(sK1) ),
% 2.22/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_932,plain,
% 2.22/0.98      ( ~ v1_funct_1(sK1)
% 2.22/0.98      | ~ v1_funct_1(sK0)
% 2.22/0.98      | ~ v1_relat_1(sK1)
% 2.22/0.98      | ~ v1_relat_1(sK0)
% 2.22/0.98      | k2_funct_1(sK1) = sK0
% 2.22/0.98      | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0)) ),
% 2.22/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_931]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1093,plain,
% 2.22/0.98      ( k2_funct_1(sK1) = sK0
% 2.22/0.98      | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k2_relat_1(sK0)) ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_931,c_21,c_20,c_19,c_18,c_932]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1668,plain,
% 2.22/0.98      ( k2_funct_1(sK1) = sK0
% 2.22/0.98      | k6_relat_1(k1_relat_1(sK1)) != k6_relat_1(k1_relat_1(sK1)) ),
% 2.22/0.98      inference(demodulation,[status(thm)],[c_1665,c_1093]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1672,plain,
% 2.22/0.98      ( k2_funct_1(sK1) = sK0 ),
% 2.22/0.98      inference(equality_resolution_simp,[status(thm)],[c_1668]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_609,plain,
% 2.22/0.98      ( v1_funct_1(sK1) = iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_7,plain,
% 2.22/0.98      ( ~ v1_funct_1(X0)
% 2.22/0.98      | ~ v2_funct_1(X0)
% 2.22/0.98      | ~ v1_relat_1(X0)
% 2.22/0.98      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.22/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_616,plain,
% 2.22/0.98      ( k2_funct_1(X0) = k4_relat_1(X0)
% 2.22/0.98      | v1_funct_1(X0) != iProver_top
% 2.22/0.98      | v2_funct_1(X0) != iProver_top
% 2.22/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1407,plain,
% 2.22/0.98      ( k2_funct_1(sK1) = k4_relat_1(sK1)
% 2.22/0.98      | v2_funct_1(sK1) != iProver_top
% 2.22/0.98      | v1_relat_1(sK1) != iProver_top ),
% 2.22/0.98      inference(superposition,[status(thm)],[c_609,c_616]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_23,plain,
% 2.22/0.98      ( v1_funct_1(sK0) = iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_25,plain,
% 2.22/0.98      ( v1_funct_1(sK1) = iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1669,plain,
% 2.22/0.98      ( k6_relat_1(k1_relat_1(sK1)) = k5_relat_1(sK1,sK0) ),
% 2.22/0.98      inference(demodulation,[status(thm)],[c_1665,c_15]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_611,plain,
% 2.22/0.98      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
% 2.22/0.98      | v1_funct_1(X0) != iProver_top
% 2.22/0.98      | v1_funct_1(X1) != iProver_top
% 2.22/0.98      | v2_funct_1(X0) = iProver_top
% 2.22/0.98      | v1_relat_1(X0) != iProver_top
% 2.22/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1680,plain,
% 2.22/0.98      ( v1_funct_1(sK1) != iProver_top
% 2.22/0.98      | v1_funct_1(sK0) != iProver_top
% 2.22/0.98      | v2_funct_1(sK1) = iProver_top
% 2.22/0.98      | v1_relat_1(sK1) != iProver_top
% 2.22/0.98      | v1_relat_1(sK0) != iProver_top ),
% 2.22/0.98      inference(superposition,[status(thm)],[c_1669,c_611]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1851,plain,
% 2.22/0.98      ( k2_funct_1(sK1) = k4_relat_1(sK1) ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_1407,c_22,c_23,c_24,c_25,c_1680]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_3211,plain,
% 2.22/0.98      ( k4_relat_1(sK1) = sK0 ),
% 2.22/0.98      inference(demodulation,[status(thm)],[c_1672,c_1851]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_608,plain,
% 2.22/0.98      ( v1_relat_1(sK1) = iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_3,plain,
% 2.22/0.98      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 2.22/0.98      inference(cnf_transformation,[],[f33]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_618,plain,
% 2.22/0.98      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1186,plain,
% 2.22/0.98      ( k4_relat_1(k4_relat_1(sK1)) = sK1 ),
% 2.22/0.98      inference(superposition,[status(thm)],[c_608,c_618]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_3345,plain,
% 2.22/0.98      ( k4_relat_1(sK0) = sK1 ),
% 2.22/0.98      inference(demodulation,[status(thm)],[c_3211,c_1186]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_607,plain,
% 2.22/0.98      ( v1_funct_1(sK0) = iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1408,plain,
% 2.22/0.98      ( k2_funct_1(sK0) = k4_relat_1(sK0)
% 2.22/0.98      | v2_funct_1(sK0) != iProver_top
% 2.22/0.98      | v1_relat_1(sK0) != iProver_top ),
% 2.22/0.98      inference(superposition,[status(thm)],[c_607,c_616]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_17,negated_conjecture,
% 2.22/0.98      ( v2_funct_1(sK0) ),
% 2.22/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_40,plain,
% 2.22/0.98      ( ~ v1_funct_1(sK0)
% 2.22/0.98      | ~ v2_funct_1(sK0)
% 2.22/0.98      | ~ v1_relat_1(sK0)
% 2.22/0.98      | k2_funct_1(sK0) = k4_relat_1(sK0) ),
% 2.22/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_2110,plain,
% 2.22/0.98      ( k2_funct_1(sK0) = k4_relat_1(sK0) ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_1408,c_21,c_20,c_17,c_40]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_14,negated_conjecture,
% 2.22/0.98      ( k2_funct_1(sK0) != sK1 ),
% 2.22/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_2113,plain,
% 2.22/0.98      ( k4_relat_1(sK0) != sK1 ),
% 2.22/0.98      inference(demodulation,[status(thm)],[c_2110,c_14]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(contradiction,plain,
% 2.22/0.98      ( $false ),
% 2.22/0.98      inference(minisat,[status(thm)],[c_3345,c_2113]) ).
% 2.22/0.98  
% 2.22/0.98  
% 2.22/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.22/0.98  
% 2.22/0.98  ------                               Statistics
% 2.22/0.98  
% 2.22/0.98  ------ General
% 2.22/0.98  
% 2.22/0.98  abstr_ref_over_cycles:                  0
% 2.22/0.98  abstr_ref_under_cycles:                 0
% 2.22/0.98  gc_basic_clause_elim:                   0
% 2.22/0.98  forced_gc_time:                         0
% 2.22/0.98  parsing_time:                           0.008
% 2.22/0.98  unif_index_cands_time:                  0.
% 2.22/0.98  unif_index_add_time:                    0.
% 2.22/0.98  orderings_time:                         0.
% 2.22/0.98  out_proof_time:                         0.007
% 2.22/0.98  total_time:                             0.138
% 2.22/0.98  num_of_symbols:                         43
% 2.22/0.98  num_of_terms:                           2860
% 2.22/0.98  
% 2.22/0.98  ------ Preprocessing
% 2.22/0.98  
% 2.22/0.98  num_of_splits:                          0
% 2.22/0.98  num_of_split_atoms:                     0
% 2.22/0.98  num_of_reused_defs:                     0
% 2.22/0.98  num_eq_ax_congr_red:                    0
% 2.22/0.98  num_of_sem_filtered_clauses:            1
% 2.22/0.98  num_of_subtypes:                        0
% 2.22/0.98  monotx_restored_types:                  0
% 2.22/0.98  sat_num_of_epr_types:                   0
% 2.22/0.98  sat_num_of_non_cyclic_types:            0
% 2.22/0.98  sat_guarded_non_collapsed_types:        0
% 2.22/0.98  num_pure_diseq_elim:                    0
% 2.22/0.98  simp_replaced_by:                       0
% 2.22/0.98  res_preprocessed:                       109
% 2.22/0.98  prep_upred:                             0
% 2.22/0.98  prep_unflattend:                        0
% 2.22/0.98  smt_new_axioms:                         0
% 2.22/0.98  pred_elim_cands:                        4
% 2.22/0.98  pred_elim:                              0
% 2.22/0.98  pred_elim_cl:                           0
% 2.22/0.98  pred_elim_cycles:                       2
% 2.22/0.98  merged_defs:                            0
% 2.22/0.98  merged_defs_ncl:                        0
% 2.22/0.98  bin_hyper_res:                          0
% 2.22/0.98  prep_cycles:                            4
% 2.22/0.98  pred_elim_time:                         0.
% 2.22/0.98  splitting_time:                         0.
% 2.22/0.98  sem_filter_time:                        0.
% 2.22/0.98  monotx_time:                            0.
% 2.22/0.98  subtype_inf_time:                       0.
% 2.22/0.98  
% 2.22/0.98  ------ Problem properties
% 2.22/0.98  
% 2.22/0.98  clauses:                                21
% 2.22/0.98  conjectures:                            8
% 2.22/0.98  epr:                                    7
% 2.22/0.98  horn:                                   21
% 2.22/0.98  ground:                                 8
% 2.22/0.98  unary:                                  13
% 2.22/0.98  binary:                                 1
% 2.22/0.98  lits:                                   53
% 2.22/0.98  lits_eq:                                15
% 2.22/0.98  fd_pure:                                0
% 2.22/0.98  fd_pseudo:                              0
% 2.22/0.98  fd_cond:                                0
% 2.22/0.98  fd_pseudo_cond:                         2
% 2.22/0.98  ac_symbols:                             0
% 2.22/0.98  
% 2.22/0.98  ------ Propositional Solver
% 2.22/0.98  
% 2.22/0.98  prop_solver_calls:                      28
% 2.22/0.98  prop_fast_solver_calls:                 723
% 2.22/0.98  smt_solver_calls:                       0
% 2.22/0.98  smt_fast_solver_calls:                  0
% 2.22/0.98  prop_num_of_clauses:                    1136
% 2.22/0.98  prop_preprocess_simplified:             4311
% 2.22/0.98  prop_fo_subsumed:                       28
% 2.22/0.98  prop_solver_time:                       0.
% 2.22/0.98  smt_solver_time:                        0.
% 2.22/0.98  smt_fast_solver_time:                   0.
% 2.22/0.98  prop_fast_solver_time:                  0.
% 2.22/0.98  prop_unsat_core_time:                   0.
% 2.22/0.98  
% 2.22/0.98  ------ QBF
% 2.22/0.98  
% 2.22/0.98  qbf_q_res:                              0
% 2.22/0.98  qbf_num_tautologies:                    0
% 2.22/0.98  qbf_prep_cycles:                        0
% 2.22/0.98  
% 2.22/0.98  ------ BMC1
% 2.22/0.98  
% 2.22/0.98  bmc1_current_bound:                     -1
% 2.22/0.98  bmc1_last_solved_bound:                 -1
% 2.22/0.98  bmc1_unsat_core_size:                   -1
% 2.22/0.98  bmc1_unsat_core_parents_size:           -1
% 2.22/0.98  bmc1_merge_next_fun:                    0
% 2.22/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.22/0.98  
% 2.22/0.98  ------ Instantiation
% 2.22/0.98  
% 2.22/0.98  inst_num_of_clauses:                    463
% 2.22/0.98  inst_num_in_passive:                    73
% 2.22/0.98  inst_num_in_active:                     216
% 2.22/0.98  inst_num_in_unprocessed:                174
% 2.22/0.98  inst_num_of_loops:                      230
% 2.22/0.98  inst_num_of_learning_restarts:          0
% 2.22/0.98  inst_num_moves_active_passive:          10
% 2.22/0.98  inst_lit_activity:                      0
% 2.22/0.98  inst_lit_activity_moves:                0
% 2.22/0.98  inst_num_tautologies:                   0
% 2.22/0.98  inst_num_prop_implied:                  0
% 2.22/0.98  inst_num_existing_simplified:           0
% 2.22/0.98  inst_num_eq_res_simplified:             0
% 2.22/0.98  inst_num_child_elim:                    0
% 2.22/0.98  inst_num_of_dismatching_blockings:      275
% 2.22/0.98  inst_num_of_non_proper_insts:           581
% 2.22/0.98  inst_num_of_duplicates:                 0
% 2.22/0.98  inst_inst_num_from_inst_to_res:         0
% 2.22/0.98  inst_dismatching_checking_time:         0.
% 2.22/0.98  
% 2.22/0.98  ------ Resolution
% 2.22/0.98  
% 2.22/0.98  res_num_of_clauses:                     0
% 2.22/0.98  res_num_in_passive:                     0
% 2.22/0.98  res_num_in_active:                      0
% 2.22/0.98  res_num_of_loops:                       113
% 2.22/0.98  res_forward_subset_subsumed:            66
% 2.22/0.98  res_backward_subset_subsumed:           4
% 2.22/0.98  res_forward_subsumed:                   0
% 2.22/0.98  res_backward_subsumed:                  0
% 2.22/0.98  res_forward_subsumption_resolution:     0
% 2.22/0.98  res_backward_subsumption_resolution:    0
% 2.22/0.98  res_clause_to_clause_subsumption:       102
% 2.22/0.98  res_orphan_elimination:                 0
% 2.22/0.98  res_tautology_del:                      46
% 2.22/0.98  res_num_eq_res_simplified:              0
% 2.22/0.98  res_num_sel_changes:                    0
% 2.22/0.98  res_moves_from_active_to_pass:          0
% 2.22/0.98  
% 2.22/0.98  ------ Superposition
% 2.22/0.98  
% 2.22/0.98  sup_time_total:                         0.
% 2.22/0.98  sup_time_generating:                    0.
% 2.22/0.98  sup_time_sim_full:                      0.
% 2.22/0.98  sup_time_sim_immed:                     0.
% 2.22/0.98  
% 2.22/0.98  sup_num_of_clauses:                     55
% 2.22/0.98  sup_num_in_active:                      39
% 2.22/0.98  sup_num_in_passive:                     16
% 2.22/0.98  sup_num_of_loops:                       44
% 2.22/0.98  sup_fw_superposition:                   40
% 2.22/0.98  sup_bw_superposition:                   5
% 2.22/0.98  sup_immediate_simplified:               15
% 2.22/0.98  sup_given_eliminated:                   0
% 2.22/0.98  comparisons_done:                       0
% 2.22/0.98  comparisons_avoided:                    0
% 2.22/0.98  
% 2.22/0.98  ------ Simplifications
% 2.22/0.98  
% 2.22/0.98  
% 2.22/0.98  sim_fw_subset_subsumed:                 9
% 2.22/0.98  sim_bw_subset_subsumed:                 0
% 2.22/0.98  sim_fw_subsumed:                        3
% 2.22/0.98  sim_bw_subsumed:                        0
% 2.22/0.98  sim_fw_subsumption_res:                 2
% 2.22/0.98  sim_bw_subsumption_res:                 0
% 2.22/0.98  sim_tautology_del:                      0
% 2.22/0.98  sim_eq_tautology_del:                   1
% 2.22/0.98  sim_eq_res_simp:                        2
% 2.22/0.98  sim_fw_demodulated:                     1
% 2.22/0.98  sim_bw_demodulated:                     5
% 2.22/0.98  sim_light_normalised:                   4
% 2.22/0.98  sim_joinable_taut:                      0
% 2.22/0.98  sim_joinable_simp:                      0
% 2.22/0.98  sim_ac_normalised:                      0
% 2.22/0.98  sim_smt_subsumption:                    0
% 2.22/0.98  
%------------------------------------------------------------------------------
