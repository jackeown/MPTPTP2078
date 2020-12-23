%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:45 EST 2020

% Result     : Theorem 5.78s
% Output     : CNFRefutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 357 expanded)
%              Number of clauses        :   59 (  92 expanded)
%              Number of leaves         :   12 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :  311 (2226 expanded)
%              Number of equality atoms :  152 ( 892 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
                & k2_relat_1(X0) = k1_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k2_funct_1(X0) != sK1
        & k5_relat_1(X0,sK1) = k6_relat_1(k1_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(sK1)
        & v2_funct_1(X0)
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & k2_relat_1(X0) = k1_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0))
          & k2_relat_1(sK0) = k1_relat_1(X1)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k2_funct_1(sK0) != sK1
    & k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))
    & k2_relat_1(sK0) = k1_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).

fof(f48,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f45,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_649,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_647,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_659,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X2),X1) = k5_relat_1(X0,k5_relat_1(X2,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_656,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2128,plain,
    ( k5_relat_1(k4_relat_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k4_relat_1(X0),X1),X2)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_659,c_656])).

cnf(c_7918,plain,
    ( k5_relat_1(k5_relat_1(k4_relat_1(sK0),X0),X1) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_647,c_2128])).

cnf(c_9472,plain,
    ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k5_relat_1(k4_relat_1(sK0),sK0),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_647,c_7918])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_17,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_246,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_247,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_31,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_249,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_247,c_21,c_20,c_17,c_31])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_254,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_255,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_43,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_257,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_255,c_21,c_20,c_17,c_43])).

cnf(c_681,plain,
    ( k5_relat_1(k4_relat_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_249,c_257])).

cnf(c_9475,plain,
    ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9472,c_681])).

cnf(c_12613,plain,
    ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) ),
    inference(superposition,[status(thm)],[c_649,c_9475])).

cnf(c_15,negated_conjecture,
    ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_11,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_651,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_880,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(sK0))) != k1_relat_1(sK0)
    | r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_651])).

cnf(c_16,negated_conjecture,
    ( k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_881,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(sK0))) != k1_relat_1(sK0)
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_880,c_16])).

cnf(c_22,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_24,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_25,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_952,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(X0))) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_954,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(sK0))) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_952])).

cnf(c_1053,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_881,c_22,c_23,c_24,c_25,c_954])).

cnf(c_6,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_655,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1666,plain,
    ( k5_relat_1(k6_relat_1(X0),sK1) = sK1
    | r1_tarski(k2_relat_1(sK0),X0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_655])).

cnf(c_1706,plain,
    ( r1_tarski(k2_relat_1(sK0),X0) != iProver_top
    | k5_relat_1(k6_relat_1(X0),sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1666,c_24])).

cnf(c_1707,plain,
    ( k5_relat_1(k6_relat_1(X0),sK1) = sK1
    | r1_tarski(k2_relat_1(sK0),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1706])).

cnf(c_1714,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_1053,c_1707])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_654,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1525,plain,
    ( k5_relat_1(k4_relat_1(X0),k6_relat_1(k2_relat_1(k4_relat_1(X0)))) = k4_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_659,c_654])).

cnf(c_3542,plain,
    ( k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(k4_relat_1(sK0)))) = k4_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_647,c_1525])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_658,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1317,plain,
    ( k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_647,c_658])).

cnf(c_3544,plain,
    ( k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k4_relat_1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_3542,c_1317])).

cnf(c_12618,plain,
    ( k4_relat_1(sK0) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_12613,c_15,c_1714,c_3544])).

cnf(c_14,negated_conjecture,
    ( k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_672,plain,
    ( k4_relat_1(sK0) != sK1 ),
    inference(light_normalisation,[status(thm)],[c_14,c_257])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12618,c_672])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 5.78/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/1.51  
% 5.78/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 5.78/1.51  
% 5.78/1.51  ------  iProver source info
% 5.78/1.51  
% 5.78/1.51  git: date: 2020-06-30 10:37:57 +0100
% 5.78/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 5.78/1.51  git: non_committed_changes: false
% 5.78/1.51  git: last_make_outside_of_git: false
% 5.78/1.51  
% 5.78/1.51  ------ 
% 5.78/1.51  
% 5.78/1.51  ------ Input Options
% 5.78/1.51  
% 5.78/1.51  --out_options                           all
% 5.78/1.51  --tptp_safe_out                         true
% 5.78/1.51  --problem_path                          ""
% 5.78/1.51  --include_path                          ""
% 5.78/1.51  --clausifier                            res/vclausify_rel
% 5.78/1.51  --clausifier_options                    --mode clausify
% 5.78/1.51  --stdin                                 false
% 5.78/1.51  --stats_out                             all
% 5.78/1.51  
% 5.78/1.51  ------ General Options
% 5.78/1.51  
% 5.78/1.51  --fof                                   false
% 5.78/1.51  --time_out_real                         305.
% 5.78/1.51  --time_out_virtual                      -1.
% 5.78/1.51  --symbol_type_check                     false
% 5.78/1.51  --clausify_out                          false
% 5.78/1.51  --sig_cnt_out                           false
% 5.78/1.51  --trig_cnt_out                          false
% 5.78/1.51  --trig_cnt_out_tolerance                1.
% 5.78/1.51  --trig_cnt_out_sk_spl                   false
% 5.78/1.51  --abstr_cl_out                          false
% 5.78/1.51  
% 5.78/1.51  ------ Global Options
% 5.78/1.51  
% 5.78/1.51  --schedule                              default
% 5.78/1.51  --add_important_lit                     false
% 5.78/1.51  --prop_solver_per_cl                    1000
% 5.78/1.51  --min_unsat_core                        false
% 5.78/1.51  --soft_assumptions                      false
% 5.78/1.51  --soft_lemma_size                       3
% 5.78/1.51  --prop_impl_unit_size                   0
% 5.78/1.51  --prop_impl_unit                        []
% 5.78/1.51  --share_sel_clauses                     true
% 5.78/1.51  --reset_solvers                         false
% 5.78/1.51  --bc_imp_inh                            [conj_cone]
% 5.78/1.51  --conj_cone_tolerance                   3.
% 5.78/1.51  --extra_neg_conj                        none
% 5.78/1.51  --large_theory_mode                     true
% 5.78/1.51  --prolific_symb_bound                   200
% 5.78/1.51  --lt_threshold                          2000
% 5.78/1.51  --clause_weak_htbl                      true
% 5.78/1.51  --gc_record_bc_elim                     false
% 5.78/1.51  
% 5.78/1.51  ------ Preprocessing Options
% 5.78/1.51  
% 5.78/1.51  --preprocessing_flag                    true
% 5.78/1.51  --time_out_prep_mult                    0.1
% 5.78/1.51  --splitting_mode                        input
% 5.78/1.51  --splitting_grd                         true
% 5.78/1.51  --splitting_cvd                         false
% 5.78/1.51  --splitting_cvd_svl                     false
% 5.78/1.51  --splitting_nvd                         32
% 5.78/1.51  --sub_typing                            true
% 5.78/1.51  --prep_gs_sim                           true
% 5.78/1.51  --prep_unflatten                        true
% 5.78/1.51  --prep_res_sim                          true
% 5.78/1.51  --prep_upred                            true
% 5.78/1.51  --prep_sem_filter                       exhaustive
% 5.78/1.51  --prep_sem_filter_out                   false
% 5.78/1.51  --pred_elim                             true
% 5.78/1.51  --res_sim_input                         true
% 5.78/1.51  --eq_ax_congr_red                       true
% 5.78/1.51  --pure_diseq_elim                       true
% 5.78/1.51  --brand_transform                       false
% 5.78/1.51  --non_eq_to_eq                          false
% 5.78/1.51  --prep_def_merge                        true
% 5.78/1.51  --prep_def_merge_prop_impl              false
% 5.78/1.51  --prep_def_merge_mbd                    true
% 5.78/1.51  --prep_def_merge_tr_red                 false
% 5.78/1.51  --prep_def_merge_tr_cl                  false
% 5.78/1.51  --smt_preprocessing                     true
% 5.78/1.51  --smt_ac_axioms                         fast
% 5.78/1.51  --preprocessed_out                      false
% 5.78/1.51  --preprocessed_stats                    false
% 5.78/1.51  
% 5.78/1.51  ------ Abstraction refinement Options
% 5.78/1.51  
% 5.78/1.51  --abstr_ref                             []
% 5.78/1.51  --abstr_ref_prep                        false
% 5.78/1.51  --abstr_ref_until_sat                   false
% 5.78/1.51  --abstr_ref_sig_restrict                funpre
% 5.78/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 5.78/1.51  --abstr_ref_under                       []
% 5.78/1.51  
% 5.78/1.51  ------ SAT Options
% 5.78/1.51  
% 5.78/1.51  --sat_mode                              false
% 5.78/1.51  --sat_fm_restart_options                ""
% 5.78/1.51  --sat_gr_def                            false
% 5.78/1.51  --sat_epr_types                         true
% 5.78/1.51  --sat_non_cyclic_types                  false
% 5.78/1.51  --sat_finite_models                     false
% 5.78/1.51  --sat_fm_lemmas                         false
% 5.78/1.51  --sat_fm_prep                           false
% 5.78/1.51  --sat_fm_uc_incr                        true
% 5.78/1.51  --sat_out_model                         small
% 5.78/1.51  --sat_out_clauses                       false
% 5.78/1.51  
% 5.78/1.51  ------ QBF Options
% 5.78/1.51  
% 5.78/1.51  --qbf_mode                              false
% 5.78/1.51  --qbf_elim_univ                         false
% 5.78/1.51  --qbf_dom_inst                          none
% 5.78/1.51  --qbf_dom_pre_inst                      false
% 5.78/1.51  --qbf_sk_in                             false
% 5.78/1.51  --qbf_pred_elim                         true
% 5.78/1.51  --qbf_split                             512
% 5.78/1.51  
% 5.78/1.51  ------ BMC1 Options
% 5.78/1.51  
% 5.78/1.51  --bmc1_incremental                      false
% 5.78/1.51  --bmc1_axioms                           reachable_all
% 5.78/1.51  --bmc1_min_bound                        0
% 5.78/1.51  --bmc1_max_bound                        -1
% 5.78/1.51  --bmc1_max_bound_default                -1
% 5.78/1.51  --bmc1_symbol_reachability              true
% 5.78/1.51  --bmc1_property_lemmas                  false
% 5.78/1.51  --bmc1_k_induction                      false
% 5.78/1.51  --bmc1_non_equiv_states                 false
% 5.78/1.51  --bmc1_deadlock                         false
% 5.78/1.51  --bmc1_ucm                              false
% 5.78/1.51  --bmc1_add_unsat_core                   none
% 5.78/1.51  --bmc1_unsat_core_children              false
% 5.78/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 5.78/1.51  --bmc1_out_stat                         full
% 5.78/1.51  --bmc1_ground_init                      false
% 5.78/1.51  --bmc1_pre_inst_next_state              false
% 5.78/1.51  --bmc1_pre_inst_state                   false
% 5.78/1.51  --bmc1_pre_inst_reach_state             false
% 5.78/1.51  --bmc1_out_unsat_core                   false
% 5.78/1.51  --bmc1_aig_witness_out                  false
% 5.78/1.51  --bmc1_verbose                          false
% 5.78/1.51  --bmc1_dump_clauses_tptp                false
% 5.78/1.51  --bmc1_dump_unsat_core_tptp             false
% 5.78/1.51  --bmc1_dump_file                        -
% 5.78/1.51  --bmc1_ucm_expand_uc_limit              128
% 5.78/1.51  --bmc1_ucm_n_expand_iterations          6
% 5.78/1.51  --bmc1_ucm_extend_mode                  1
% 5.78/1.51  --bmc1_ucm_init_mode                    2
% 5.78/1.51  --bmc1_ucm_cone_mode                    none
% 5.78/1.51  --bmc1_ucm_reduced_relation_type        0
% 5.78/1.51  --bmc1_ucm_relax_model                  4
% 5.78/1.51  --bmc1_ucm_full_tr_after_sat            true
% 5.78/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 5.78/1.51  --bmc1_ucm_layered_model                none
% 5.78/1.51  --bmc1_ucm_max_lemma_size               10
% 5.78/1.51  
% 5.78/1.51  ------ AIG Options
% 5.78/1.51  
% 5.78/1.51  --aig_mode                              false
% 5.78/1.51  
% 5.78/1.51  ------ Instantiation Options
% 5.78/1.51  
% 5.78/1.51  --instantiation_flag                    true
% 5.78/1.51  --inst_sos_flag                         false
% 5.78/1.51  --inst_sos_phase                        true
% 5.78/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 5.78/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 5.78/1.51  --inst_lit_sel_side                     num_symb
% 5.78/1.51  --inst_solver_per_active                1400
% 5.78/1.51  --inst_solver_calls_frac                1.
% 5.78/1.51  --inst_passive_queue_type               priority_queues
% 5.78/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 5.78/1.51  --inst_passive_queues_freq              [25;2]
% 5.78/1.51  --inst_dismatching                      true
% 5.78/1.51  --inst_eager_unprocessed_to_passive     true
% 5.78/1.51  --inst_prop_sim_given                   true
% 5.78/1.51  --inst_prop_sim_new                     false
% 5.78/1.51  --inst_subs_new                         false
% 5.78/1.51  --inst_eq_res_simp                      false
% 5.78/1.51  --inst_subs_given                       false
% 5.78/1.51  --inst_orphan_elimination               true
% 5.78/1.51  --inst_learning_loop_flag               true
% 5.78/1.51  --inst_learning_start                   3000
% 5.78/1.51  --inst_learning_factor                  2
% 5.78/1.51  --inst_start_prop_sim_after_learn       3
% 5.78/1.51  --inst_sel_renew                        solver
% 5.78/1.51  --inst_lit_activity_flag                true
% 5.78/1.51  --inst_restr_to_given                   false
% 5.78/1.51  --inst_activity_threshold               500
% 5.78/1.51  --inst_out_proof                        true
% 5.78/1.51  
% 5.78/1.51  ------ Resolution Options
% 5.78/1.51  
% 5.78/1.51  --resolution_flag                       true
% 5.78/1.51  --res_lit_sel                           adaptive
% 5.78/1.51  --res_lit_sel_side                      none
% 5.78/1.51  --res_ordering                          kbo
% 5.78/1.51  --res_to_prop_solver                    active
% 5.78/1.51  --res_prop_simpl_new                    false
% 5.78/1.51  --res_prop_simpl_given                  true
% 5.78/1.51  --res_passive_queue_type                priority_queues
% 5.78/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 5.78/1.51  --res_passive_queues_freq               [15;5]
% 5.78/1.51  --res_forward_subs                      full
% 5.78/1.51  --res_backward_subs                     full
% 5.78/1.51  --res_forward_subs_resolution           true
% 5.78/1.51  --res_backward_subs_resolution          true
% 5.78/1.51  --res_orphan_elimination                true
% 5.78/1.51  --res_time_limit                        2.
% 5.78/1.51  --res_out_proof                         true
% 5.78/1.51  
% 5.78/1.51  ------ Superposition Options
% 5.78/1.51  
% 5.78/1.51  --superposition_flag                    true
% 5.78/1.51  --sup_passive_queue_type                priority_queues
% 5.78/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 5.78/1.51  --sup_passive_queues_freq               [8;1;4]
% 5.78/1.51  --demod_completeness_check              fast
% 5.78/1.51  --demod_use_ground                      true
% 5.78/1.51  --sup_to_prop_solver                    passive
% 5.78/1.51  --sup_prop_simpl_new                    true
% 5.78/1.51  --sup_prop_simpl_given                  true
% 5.78/1.51  --sup_fun_splitting                     false
% 5.78/1.51  --sup_smt_interval                      50000
% 5.78/1.51  
% 5.78/1.51  ------ Superposition Simplification Setup
% 5.78/1.51  
% 5.78/1.51  --sup_indices_passive                   []
% 5.78/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.78/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.78/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.78/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 5.78/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.78/1.51  --sup_full_bw                           [BwDemod]
% 5.78/1.51  --sup_immed_triv                        [TrivRules]
% 5.78/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 5.78/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.78/1.51  --sup_immed_bw_main                     []
% 5.78/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 5.78/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 5.78/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.78/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 5.78/1.51  
% 5.78/1.51  ------ Combination Options
% 5.78/1.51  
% 5.78/1.51  --comb_res_mult                         3
% 5.78/1.51  --comb_sup_mult                         2
% 5.78/1.51  --comb_inst_mult                        10
% 5.78/1.51  
% 5.78/1.51  ------ Debug Options
% 5.78/1.51  
% 5.78/1.51  --dbg_backtrace                         false
% 5.78/1.51  --dbg_dump_prop_clauses                 false
% 5.78/1.51  --dbg_dump_prop_clauses_file            -
% 5.78/1.51  --dbg_out_stat                          false
% 5.78/1.51  ------ Parsing...
% 5.78/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 5.78/1.51  
% 5.78/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 5.78/1.51  
% 5.78/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 5.78/1.51  
% 5.78/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 5.78/1.51  ------ Proving...
% 5.78/1.51  ------ Problem Properties 
% 5.78/1.51  
% 5.78/1.51  
% 5.78/1.51  clauses                                 21
% 5.78/1.51  conjectures                             7
% 5.78/1.51  EPR                                     4
% 5.78/1.51  Horn                                    21
% 5.78/1.51  unary                                   12
% 5.78/1.51  binary                                  4
% 5.78/1.51  lits                                    39
% 5.78/1.51  lits eq                                 14
% 5.78/1.51  fd_pure                                 0
% 5.78/1.51  fd_pseudo                               0
% 5.78/1.51  fd_cond                                 0
% 5.78/1.51  fd_pseudo_cond                          0
% 5.78/1.51  AC symbols                              0
% 5.78/1.51  
% 5.78/1.51  ------ Schedule dynamic 5 is on 
% 5.78/1.51  
% 5.78/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 5.78/1.51  
% 5.78/1.51  
% 5.78/1.51  ------ 
% 5.78/1.51  Current options:
% 5.78/1.51  ------ 
% 5.78/1.51  
% 5.78/1.51  ------ Input Options
% 5.78/1.51  
% 5.78/1.51  --out_options                           all
% 5.78/1.51  --tptp_safe_out                         true
% 5.78/1.51  --problem_path                          ""
% 5.78/1.51  --include_path                          ""
% 5.78/1.51  --clausifier                            res/vclausify_rel
% 5.78/1.51  --clausifier_options                    --mode clausify
% 5.78/1.51  --stdin                                 false
% 5.78/1.51  --stats_out                             all
% 5.78/1.51  
% 5.78/1.51  ------ General Options
% 5.78/1.51  
% 5.78/1.51  --fof                                   false
% 5.78/1.51  --time_out_real                         305.
% 5.78/1.51  --time_out_virtual                      -1.
% 5.78/1.51  --symbol_type_check                     false
% 5.78/1.51  --clausify_out                          false
% 5.78/1.51  --sig_cnt_out                           false
% 5.78/1.51  --trig_cnt_out                          false
% 5.78/1.51  --trig_cnt_out_tolerance                1.
% 5.78/1.51  --trig_cnt_out_sk_spl                   false
% 5.78/1.51  --abstr_cl_out                          false
% 5.78/1.51  
% 5.78/1.51  ------ Global Options
% 5.78/1.51  
% 5.78/1.51  --schedule                              default
% 5.78/1.51  --add_important_lit                     false
% 5.78/1.51  --prop_solver_per_cl                    1000
% 5.78/1.51  --min_unsat_core                        false
% 5.78/1.51  --soft_assumptions                      false
% 5.78/1.51  --soft_lemma_size                       3
% 5.78/1.51  --prop_impl_unit_size                   0
% 5.78/1.51  --prop_impl_unit                        []
% 5.78/1.51  --share_sel_clauses                     true
% 5.78/1.51  --reset_solvers                         false
% 5.78/1.51  --bc_imp_inh                            [conj_cone]
% 5.78/1.51  --conj_cone_tolerance                   3.
% 5.78/1.51  --extra_neg_conj                        none
% 5.78/1.51  --large_theory_mode                     true
% 5.78/1.51  --prolific_symb_bound                   200
% 5.78/1.51  --lt_threshold                          2000
% 5.78/1.51  --clause_weak_htbl                      true
% 5.78/1.51  --gc_record_bc_elim                     false
% 5.78/1.51  
% 5.78/1.51  ------ Preprocessing Options
% 5.78/1.51  
% 5.78/1.51  --preprocessing_flag                    true
% 5.78/1.51  --time_out_prep_mult                    0.1
% 5.78/1.51  --splitting_mode                        input
% 5.78/1.51  --splitting_grd                         true
% 5.78/1.51  --splitting_cvd                         false
% 5.78/1.51  --splitting_cvd_svl                     false
% 5.78/1.51  --splitting_nvd                         32
% 5.78/1.51  --sub_typing                            true
% 5.78/1.51  --prep_gs_sim                           true
% 5.78/1.51  --prep_unflatten                        true
% 5.78/1.51  --prep_res_sim                          true
% 5.78/1.51  --prep_upred                            true
% 5.78/1.51  --prep_sem_filter                       exhaustive
% 5.78/1.51  --prep_sem_filter_out                   false
% 5.78/1.51  --pred_elim                             true
% 5.78/1.51  --res_sim_input                         true
% 5.78/1.51  --eq_ax_congr_red                       true
% 5.78/1.51  --pure_diseq_elim                       true
% 5.78/1.51  --brand_transform                       false
% 5.78/1.51  --non_eq_to_eq                          false
% 5.78/1.51  --prep_def_merge                        true
% 5.78/1.51  --prep_def_merge_prop_impl              false
% 5.78/1.51  --prep_def_merge_mbd                    true
% 5.78/1.51  --prep_def_merge_tr_red                 false
% 5.78/1.51  --prep_def_merge_tr_cl                  false
% 5.78/1.51  --smt_preprocessing                     true
% 5.78/1.51  --smt_ac_axioms                         fast
% 5.78/1.51  --preprocessed_out                      false
% 5.78/1.51  --preprocessed_stats                    false
% 5.78/1.51  
% 5.78/1.51  ------ Abstraction refinement Options
% 5.78/1.51  
% 5.78/1.51  --abstr_ref                             []
% 5.78/1.51  --abstr_ref_prep                        false
% 5.78/1.51  --abstr_ref_until_sat                   false
% 5.78/1.51  --abstr_ref_sig_restrict                funpre
% 5.78/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 5.78/1.51  --abstr_ref_under                       []
% 5.78/1.51  
% 5.78/1.51  ------ SAT Options
% 5.78/1.51  
% 5.78/1.51  --sat_mode                              false
% 5.78/1.51  --sat_fm_restart_options                ""
% 5.78/1.51  --sat_gr_def                            false
% 5.78/1.51  --sat_epr_types                         true
% 5.78/1.51  --sat_non_cyclic_types                  false
% 5.78/1.51  --sat_finite_models                     false
% 5.78/1.51  --sat_fm_lemmas                         false
% 5.78/1.51  --sat_fm_prep                           false
% 5.78/1.51  --sat_fm_uc_incr                        true
% 5.78/1.51  --sat_out_model                         small
% 5.78/1.51  --sat_out_clauses                       false
% 5.78/1.51  
% 5.78/1.51  ------ QBF Options
% 5.78/1.51  
% 5.78/1.51  --qbf_mode                              false
% 5.78/1.51  --qbf_elim_univ                         false
% 5.78/1.51  --qbf_dom_inst                          none
% 5.78/1.51  --qbf_dom_pre_inst                      false
% 5.78/1.51  --qbf_sk_in                             false
% 5.78/1.51  --qbf_pred_elim                         true
% 5.78/1.51  --qbf_split                             512
% 5.78/1.51  
% 5.78/1.51  ------ BMC1 Options
% 5.78/1.51  
% 5.78/1.51  --bmc1_incremental                      false
% 5.78/1.51  --bmc1_axioms                           reachable_all
% 5.78/1.51  --bmc1_min_bound                        0
% 5.78/1.51  --bmc1_max_bound                        -1
% 5.78/1.51  --bmc1_max_bound_default                -1
% 5.78/1.51  --bmc1_symbol_reachability              true
% 5.78/1.51  --bmc1_property_lemmas                  false
% 5.78/1.51  --bmc1_k_induction                      false
% 5.78/1.51  --bmc1_non_equiv_states                 false
% 5.78/1.51  --bmc1_deadlock                         false
% 5.78/1.51  --bmc1_ucm                              false
% 5.78/1.51  --bmc1_add_unsat_core                   none
% 5.78/1.51  --bmc1_unsat_core_children              false
% 5.78/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 5.78/1.51  --bmc1_out_stat                         full
% 5.78/1.51  --bmc1_ground_init                      false
% 5.78/1.51  --bmc1_pre_inst_next_state              false
% 5.78/1.51  --bmc1_pre_inst_state                   false
% 5.78/1.51  --bmc1_pre_inst_reach_state             false
% 5.78/1.51  --bmc1_out_unsat_core                   false
% 5.78/1.51  --bmc1_aig_witness_out                  false
% 5.78/1.51  --bmc1_verbose                          false
% 5.78/1.51  --bmc1_dump_clauses_tptp                false
% 5.78/1.51  --bmc1_dump_unsat_core_tptp             false
% 5.78/1.51  --bmc1_dump_file                        -
% 5.78/1.51  --bmc1_ucm_expand_uc_limit              128
% 5.78/1.51  --bmc1_ucm_n_expand_iterations          6
% 5.78/1.51  --bmc1_ucm_extend_mode                  1
% 5.78/1.51  --bmc1_ucm_init_mode                    2
% 5.78/1.51  --bmc1_ucm_cone_mode                    none
% 5.78/1.51  --bmc1_ucm_reduced_relation_type        0
% 5.78/1.51  --bmc1_ucm_relax_model                  4
% 5.78/1.51  --bmc1_ucm_full_tr_after_sat            true
% 5.78/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 5.78/1.51  --bmc1_ucm_layered_model                none
% 5.78/1.51  --bmc1_ucm_max_lemma_size               10
% 5.78/1.51  
% 5.78/1.51  ------ AIG Options
% 5.78/1.51  
% 5.78/1.51  --aig_mode                              false
% 5.78/1.51  
% 5.78/1.51  ------ Instantiation Options
% 5.78/1.51  
% 5.78/1.51  --instantiation_flag                    true
% 5.78/1.51  --inst_sos_flag                         false
% 5.78/1.51  --inst_sos_phase                        true
% 5.78/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 5.78/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 5.78/1.51  --inst_lit_sel_side                     none
% 5.78/1.51  --inst_solver_per_active                1400
% 5.78/1.51  --inst_solver_calls_frac                1.
% 5.78/1.51  --inst_passive_queue_type               priority_queues
% 5.78/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 5.78/1.51  --inst_passive_queues_freq              [25;2]
% 5.78/1.51  --inst_dismatching                      true
% 5.78/1.51  --inst_eager_unprocessed_to_passive     true
% 5.78/1.51  --inst_prop_sim_given                   true
% 5.78/1.51  --inst_prop_sim_new                     false
% 5.78/1.51  --inst_subs_new                         false
% 5.78/1.51  --inst_eq_res_simp                      false
% 5.78/1.51  --inst_subs_given                       false
% 5.78/1.51  --inst_orphan_elimination               true
% 5.78/1.51  --inst_learning_loop_flag               true
% 5.78/1.51  --inst_learning_start                   3000
% 5.78/1.51  --inst_learning_factor                  2
% 5.78/1.51  --inst_start_prop_sim_after_learn       3
% 5.78/1.51  --inst_sel_renew                        solver
% 5.78/1.51  --inst_lit_activity_flag                true
% 5.78/1.51  --inst_restr_to_given                   false
% 5.78/1.51  --inst_activity_threshold               500
% 5.78/1.51  --inst_out_proof                        true
% 5.78/1.51  
% 5.78/1.51  ------ Resolution Options
% 5.78/1.51  
% 5.78/1.51  --resolution_flag                       false
% 5.78/1.51  --res_lit_sel                           adaptive
% 5.78/1.51  --res_lit_sel_side                      none
% 5.78/1.51  --res_ordering                          kbo
% 5.78/1.51  --res_to_prop_solver                    active
% 5.78/1.51  --res_prop_simpl_new                    false
% 5.78/1.51  --res_prop_simpl_given                  true
% 5.78/1.51  --res_passive_queue_type                priority_queues
% 5.78/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 5.78/1.51  --res_passive_queues_freq               [15;5]
% 5.78/1.51  --res_forward_subs                      full
% 5.78/1.51  --res_backward_subs                     full
% 5.78/1.51  --res_forward_subs_resolution           true
% 5.78/1.51  --res_backward_subs_resolution          true
% 5.78/1.51  --res_orphan_elimination                true
% 5.78/1.51  --res_time_limit                        2.
% 5.78/1.51  --res_out_proof                         true
% 5.78/1.51  
% 5.78/1.51  ------ Superposition Options
% 5.78/1.51  
% 5.78/1.51  --superposition_flag                    true
% 5.78/1.51  --sup_passive_queue_type                priority_queues
% 5.78/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 5.78/1.51  --sup_passive_queues_freq               [8;1;4]
% 5.78/1.51  --demod_completeness_check              fast
% 5.78/1.51  --demod_use_ground                      true
% 5.78/1.51  --sup_to_prop_solver                    passive
% 5.78/1.51  --sup_prop_simpl_new                    true
% 5.78/1.51  --sup_prop_simpl_given                  true
% 5.78/1.51  --sup_fun_splitting                     false
% 5.78/1.51  --sup_smt_interval                      50000
% 5.78/1.51  
% 5.78/1.51  ------ Superposition Simplification Setup
% 5.78/1.51  
% 5.78/1.51  --sup_indices_passive                   []
% 5.78/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.78/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.78/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.78/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 5.78/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.78/1.51  --sup_full_bw                           [BwDemod]
% 5.78/1.51  --sup_immed_triv                        [TrivRules]
% 5.78/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 5.78/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.78/1.51  --sup_immed_bw_main                     []
% 5.78/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 5.78/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 5.78/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.78/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 5.78/1.51  
% 5.78/1.51  ------ Combination Options
% 5.78/1.51  
% 5.78/1.51  --comb_res_mult                         3
% 5.78/1.51  --comb_sup_mult                         2
% 5.78/1.51  --comb_inst_mult                        10
% 5.78/1.51  
% 5.78/1.51  ------ Debug Options
% 5.78/1.51  
% 5.78/1.51  --dbg_backtrace                         false
% 5.78/1.51  --dbg_dump_prop_clauses                 false
% 5.78/1.51  --dbg_dump_prop_clauses_file            -
% 5.78/1.51  --dbg_out_stat                          false
% 5.78/1.51  
% 5.78/1.51  
% 5.78/1.51  
% 5.78/1.51  
% 5.78/1.51  ------ Proving...
% 5.78/1.51  
% 5.78/1.51  
% 5.78/1.51  % SZS status Theorem for theBenchmark.p
% 5.78/1.51  
% 5.78/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 5.78/1.51  
% 5.78/1.51  fof(f11,conjecture,(
% 5.78/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 5.78/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.78/1.51  
% 5.78/1.51  fof(f12,negated_conjecture,(
% 5.78/1.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 5.78/1.51    inference(negated_conjecture,[],[f11])).
% 5.78/1.51  
% 5.78/1.51  fof(f27,plain,(
% 5.78/1.51    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 5.78/1.51    inference(ennf_transformation,[],[f12])).
% 5.78/1.51  
% 5.78/1.51  fof(f28,plain,(
% 5.78/1.51    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 5.78/1.51    inference(flattening,[],[f27])).
% 5.78/1.51  
% 5.78/1.51  fof(f30,plain,(
% 5.78/1.51    ( ! [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) != sK1 & k5_relat_1(X0,sK1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(sK1) & v2_funct_1(X0) & v1_funct_1(sK1) & v1_relat_1(sK1))) )),
% 5.78/1.51    introduced(choice_axiom,[])).
% 5.78/1.51  
% 5.78/1.51  fof(f29,plain,(
% 5.78/1.51    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0)) & k2_relat_1(sK0) = k1_relat_1(X1) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 5.78/1.51    introduced(choice_axiom,[])).
% 5.78/1.51  
% 5.78/1.51  fof(f31,plain,(
% 5.78/1.51    (k2_funct_1(sK0) != sK1 & k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) & k2_relat_1(sK0) = k1_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 5.78/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).
% 5.78/1.51  
% 5.78/1.51  fof(f48,plain,(
% 5.78/1.51    v1_relat_1(sK1)),
% 5.78/1.51    inference(cnf_transformation,[],[f31])).
% 5.78/1.51  
% 5.78/1.51  fof(f46,plain,(
% 5.78/1.51    v1_relat_1(sK0)),
% 5.78/1.51    inference(cnf_transformation,[],[f31])).
% 5.78/1.51  
% 5.78/1.51  fof(f1,axiom,(
% 5.78/1.51    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 5.78/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.78/1.51  
% 5.78/1.51  fof(f13,plain,(
% 5.78/1.51    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 5.78/1.51    inference(ennf_transformation,[],[f1])).
% 5.78/1.51  
% 5.78/1.51  fof(f32,plain,(
% 5.78/1.51    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 5.78/1.51    inference(cnf_transformation,[],[f13])).
% 5.78/1.51  
% 5.78/1.51  fof(f3,axiom,(
% 5.78/1.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 5.78/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.78/1.51  
% 5.78/1.51  fof(f15,plain,(
% 5.78/1.51    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 5.78/1.51    inference(ennf_transformation,[],[f3])).
% 5.78/1.51  
% 5.78/1.51  fof(f35,plain,(
% 5.78/1.51    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 5.78/1.51    inference(cnf_transformation,[],[f15])).
% 5.78/1.51  
% 5.78/1.51  fof(f10,axiom,(
% 5.78/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 5.78/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.78/1.51  
% 5.78/1.51  fof(f25,plain,(
% 5.78/1.51    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 5.78/1.51    inference(ennf_transformation,[],[f10])).
% 5.78/1.51  
% 5.78/1.51  fof(f26,plain,(
% 5.78/1.51    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 5.78/1.51    inference(flattening,[],[f25])).
% 5.78/1.51  
% 5.78/1.51  fof(f45,plain,(
% 5.78/1.51    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.78/1.51    inference(cnf_transformation,[],[f26])).
% 5.78/1.51  
% 5.78/1.51  fof(f50,plain,(
% 5.78/1.51    v2_funct_1(sK0)),
% 5.78/1.51    inference(cnf_transformation,[],[f31])).
% 5.78/1.51  
% 5.78/1.51  fof(f47,plain,(
% 5.78/1.51    v1_funct_1(sK0)),
% 5.78/1.51    inference(cnf_transformation,[],[f31])).
% 5.78/1.51  
% 5.78/1.51  fof(f7,axiom,(
% 5.78/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 5.78/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.78/1.51  
% 5.78/1.51  fof(f19,plain,(
% 5.78/1.51    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 5.78/1.51    inference(ennf_transformation,[],[f7])).
% 5.78/1.51  
% 5.78/1.51  fof(f20,plain,(
% 5.78/1.51    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 5.78/1.51    inference(flattening,[],[f19])).
% 5.78/1.51  
% 5.78/1.51  fof(f40,plain,(
% 5.78/1.51    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.78/1.51    inference(cnf_transformation,[],[f20])).
% 5.78/1.51  
% 5.78/1.51  fof(f52,plain,(
% 5.78/1.51    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))),
% 5.78/1.51    inference(cnf_transformation,[],[f31])).
% 5.78/1.51  
% 5.78/1.51  fof(f9,axiom,(
% 5.78/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 5.78/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.78/1.51  
% 5.78/1.51  fof(f23,plain,(
% 5.78/1.51    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 5.78/1.51    inference(ennf_transformation,[],[f9])).
% 5.78/1.51  
% 5.78/1.51  fof(f24,plain,(
% 5.78/1.51    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 5.78/1.51    inference(flattening,[],[f23])).
% 5.78/1.51  
% 5.78/1.51  fof(f43,plain,(
% 5.78/1.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.78/1.51    inference(cnf_transformation,[],[f24])).
% 5.78/1.51  
% 5.78/1.51  fof(f51,plain,(
% 5.78/1.51    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 5.78/1.51    inference(cnf_transformation,[],[f31])).
% 5.78/1.51  
% 5.78/1.51  fof(f49,plain,(
% 5.78/1.51    v1_funct_1(sK1)),
% 5.78/1.51    inference(cnf_transformation,[],[f31])).
% 5.78/1.51  
% 5.78/1.51  fof(f4,axiom,(
% 5.78/1.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 5.78/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.78/1.51  
% 5.78/1.51  fof(f36,plain,(
% 5.78/1.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 5.78/1.51    inference(cnf_transformation,[],[f4])).
% 5.78/1.51  
% 5.78/1.51  fof(f5,axiom,(
% 5.78/1.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 5.78/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.78/1.51  
% 5.78/1.51  fof(f16,plain,(
% 5.78/1.51    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 5.78/1.51    inference(ennf_transformation,[],[f5])).
% 5.78/1.51  
% 5.78/1.51  fof(f17,plain,(
% 5.78/1.51    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 5.78/1.51    inference(flattening,[],[f16])).
% 5.78/1.51  
% 5.78/1.51  fof(f38,plain,(
% 5.78/1.51    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 5.78/1.51    inference(cnf_transformation,[],[f17])).
% 5.78/1.51  
% 5.78/1.51  fof(f6,axiom,(
% 5.78/1.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 5.78/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.78/1.51  
% 5.78/1.51  fof(f18,plain,(
% 5.78/1.51    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 5.78/1.51    inference(ennf_transformation,[],[f6])).
% 5.78/1.51  
% 5.78/1.51  fof(f39,plain,(
% 5.78/1.51    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 5.78/1.51    inference(cnf_transformation,[],[f18])).
% 5.78/1.51  
% 5.78/1.51  fof(f2,axiom,(
% 5.78/1.51    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 5.78/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.78/1.51  
% 5.78/1.51  fof(f14,plain,(
% 5.78/1.51    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 5.78/1.51    inference(ennf_transformation,[],[f2])).
% 5.78/1.51  
% 5.78/1.51  fof(f34,plain,(
% 5.78/1.51    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 5.78/1.51    inference(cnf_transformation,[],[f14])).
% 5.78/1.51  
% 5.78/1.51  fof(f53,plain,(
% 5.78/1.51    k2_funct_1(sK0) != sK1),
% 5.78/1.51    inference(cnf_transformation,[],[f31])).
% 5.78/1.51  
% 5.78/1.51  cnf(c_19,negated_conjecture,
% 5.78/1.51      ( v1_relat_1(sK1) ),
% 5.78/1.51      inference(cnf_transformation,[],[f48]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_649,plain,
% 5.78/1.51      ( v1_relat_1(sK1) = iProver_top ),
% 5.78/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_21,negated_conjecture,
% 5.78/1.51      ( v1_relat_1(sK0) ),
% 5.78/1.51      inference(cnf_transformation,[],[f46]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_647,plain,
% 5.78/1.51      ( v1_relat_1(sK0) = iProver_top ),
% 5.78/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_0,plain,
% 5.78/1.51      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 5.78/1.51      inference(cnf_transformation,[],[f32]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_659,plain,
% 5.78/1.51      ( v1_relat_1(X0) != iProver_top
% 5.78/1.51      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 5.78/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_3,plain,
% 5.78/1.51      ( ~ v1_relat_1(X0)
% 5.78/1.51      | ~ v1_relat_1(X1)
% 5.78/1.51      | ~ v1_relat_1(X2)
% 5.78/1.51      | k5_relat_1(k5_relat_1(X0,X2),X1) = k5_relat_1(X0,k5_relat_1(X2,X1)) ),
% 5.78/1.51      inference(cnf_transformation,[],[f35]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_656,plain,
% 5.78/1.51      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 5.78/1.51      | v1_relat_1(X0) != iProver_top
% 5.78/1.51      | v1_relat_1(X2) != iProver_top
% 5.78/1.51      | v1_relat_1(X1) != iProver_top ),
% 5.78/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_2128,plain,
% 5.78/1.51      ( k5_relat_1(k4_relat_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k4_relat_1(X0),X1),X2)
% 5.78/1.51      | v1_relat_1(X0) != iProver_top
% 5.78/1.51      | v1_relat_1(X1) != iProver_top
% 5.78/1.51      | v1_relat_1(X2) != iProver_top ),
% 5.78/1.51      inference(superposition,[status(thm)],[c_659,c_656]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_7918,plain,
% 5.78/1.51      ( k5_relat_1(k5_relat_1(k4_relat_1(sK0),X0),X1) = k5_relat_1(k4_relat_1(sK0),k5_relat_1(X0,X1))
% 5.78/1.51      | v1_relat_1(X0) != iProver_top
% 5.78/1.51      | v1_relat_1(X1) != iProver_top ),
% 5.78/1.51      inference(superposition,[status(thm)],[c_647,c_2128]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_9472,plain,
% 5.78/1.51      ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k5_relat_1(k4_relat_1(sK0),sK0),X0)
% 5.78/1.51      | v1_relat_1(X0) != iProver_top ),
% 5.78/1.51      inference(superposition,[status(thm)],[c_647,c_7918]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_12,plain,
% 5.78/1.51      ( ~ v1_funct_1(X0)
% 5.78/1.51      | ~ v2_funct_1(X0)
% 5.78/1.51      | ~ v1_relat_1(X0)
% 5.78/1.51      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
% 5.78/1.51      inference(cnf_transformation,[],[f45]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_17,negated_conjecture,
% 5.78/1.51      ( v2_funct_1(sK0) ),
% 5.78/1.51      inference(cnf_transformation,[],[f50]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_246,plain,
% 5.78/1.51      ( ~ v1_funct_1(X0)
% 5.78/1.51      | ~ v1_relat_1(X0)
% 5.78/1.51      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
% 5.78/1.51      | sK0 != X0 ),
% 5.78/1.51      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_247,plain,
% 5.78/1.51      ( ~ v1_funct_1(sK0)
% 5.78/1.51      | ~ v1_relat_1(sK0)
% 5.78/1.51      | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 5.78/1.51      inference(unflattening,[status(thm)],[c_246]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_20,negated_conjecture,
% 5.78/1.51      ( v1_funct_1(sK0) ),
% 5.78/1.51      inference(cnf_transformation,[],[f47]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_31,plain,
% 5.78/1.51      ( ~ v1_funct_1(sK0)
% 5.78/1.51      | ~ v2_funct_1(sK0)
% 5.78/1.51      | ~ v1_relat_1(sK0)
% 5.78/1.51      | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 5.78/1.51      inference(instantiation,[status(thm)],[c_12]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_249,plain,
% 5.78/1.51      ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 5.78/1.51      inference(global_propositional_subsumption,
% 5.78/1.51                [status(thm)],
% 5.78/1.51                [c_247,c_21,c_20,c_17,c_31]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_8,plain,
% 5.78/1.51      ( ~ v1_funct_1(X0)
% 5.78/1.51      | ~ v2_funct_1(X0)
% 5.78/1.51      | ~ v1_relat_1(X0)
% 5.78/1.51      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 5.78/1.51      inference(cnf_transformation,[],[f40]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_254,plain,
% 5.78/1.51      ( ~ v1_funct_1(X0)
% 5.78/1.51      | ~ v1_relat_1(X0)
% 5.78/1.51      | k2_funct_1(X0) = k4_relat_1(X0)
% 5.78/1.51      | sK0 != X0 ),
% 5.78/1.51      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_255,plain,
% 5.78/1.51      ( ~ v1_funct_1(sK0)
% 5.78/1.51      | ~ v1_relat_1(sK0)
% 5.78/1.51      | k2_funct_1(sK0) = k4_relat_1(sK0) ),
% 5.78/1.51      inference(unflattening,[status(thm)],[c_254]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_43,plain,
% 5.78/1.51      ( ~ v1_funct_1(sK0)
% 5.78/1.51      | ~ v2_funct_1(sK0)
% 5.78/1.51      | ~ v1_relat_1(sK0)
% 5.78/1.51      | k2_funct_1(sK0) = k4_relat_1(sK0) ),
% 5.78/1.51      inference(instantiation,[status(thm)],[c_8]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_257,plain,
% 5.78/1.51      ( k2_funct_1(sK0) = k4_relat_1(sK0) ),
% 5.78/1.51      inference(global_propositional_subsumption,
% 5.78/1.51                [status(thm)],
% 5.78/1.51                [c_255,c_21,c_20,c_17,c_43]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_681,plain,
% 5.78/1.51      ( k5_relat_1(k4_relat_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 5.78/1.51      inference(light_normalisation,[status(thm)],[c_249,c_257]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_9475,plain,
% 5.78/1.51      ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)
% 5.78/1.51      | v1_relat_1(X0) != iProver_top ),
% 5.78/1.51      inference(light_normalisation,[status(thm)],[c_9472,c_681]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_12613,plain,
% 5.78/1.51      ( k5_relat_1(k4_relat_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) ),
% 5.78/1.51      inference(superposition,[status(thm)],[c_649,c_9475]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_15,negated_conjecture,
% 5.78/1.51      ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
% 5.78/1.51      inference(cnf_transformation,[],[f52]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_11,plain,
% 5.78/1.51      ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 5.78/1.51      | ~ v1_funct_1(X1)
% 5.78/1.51      | ~ v1_funct_1(X0)
% 5.78/1.51      | ~ v1_relat_1(X1)
% 5.78/1.51      | ~ v1_relat_1(X0)
% 5.78/1.51      | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
% 5.78/1.51      inference(cnf_transformation,[],[f43]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_651,plain,
% 5.78/1.51      ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
% 5.78/1.51      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 5.78/1.51      | v1_funct_1(X0) != iProver_top
% 5.78/1.51      | v1_funct_1(X1) != iProver_top
% 5.78/1.51      | v1_relat_1(X0) != iProver_top
% 5.78/1.51      | v1_relat_1(X1) != iProver_top ),
% 5.78/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_880,plain,
% 5.78/1.51      ( k1_relat_1(k6_relat_1(k1_relat_1(sK0))) != k1_relat_1(sK0)
% 5.78/1.51      | r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) = iProver_top
% 5.78/1.51      | v1_funct_1(sK1) != iProver_top
% 5.78/1.51      | v1_funct_1(sK0) != iProver_top
% 5.78/1.51      | v1_relat_1(sK1) != iProver_top
% 5.78/1.51      | v1_relat_1(sK0) != iProver_top ),
% 5.78/1.51      inference(superposition,[status(thm)],[c_15,c_651]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_16,negated_conjecture,
% 5.78/1.51      ( k2_relat_1(sK0) = k1_relat_1(sK1) ),
% 5.78/1.51      inference(cnf_transformation,[],[f51]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_881,plain,
% 5.78/1.51      ( k1_relat_1(k6_relat_1(k1_relat_1(sK0))) != k1_relat_1(sK0)
% 5.78/1.51      | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top
% 5.78/1.51      | v1_funct_1(sK1) != iProver_top
% 5.78/1.51      | v1_funct_1(sK0) != iProver_top
% 5.78/1.51      | v1_relat_1(sK1) != iProver_top
% 5.78/1.51      | v1_relat_1(sK0) != iProver_top ),
% 5.78/1.51      inference(light_normalisation,[status(thm)],[c_880,c_16]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_22,plain,
% 5.78/1.51      ( v1_relat_1(sK0) = iProver_top ),
% 5.78/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_23,plain,
% 5.78/1.51      ( v1_funct_1(sK0) = iProver_top ),
% 5.78/1.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_24,plain,
% 5.78/1.51      ( v1_relat_1(sK1) = iProver_top ),
% 5.78/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_18,negated_conjecture,
% 5.78/1.51      ( v1_funct_1(sK1) ),
% 5.78/1.51      inference(cnf_transformation,[],[f49]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_25,plain,
% 5.78/1.51      ( v1_funct_1(sK1) = iProver_top ),
% 5.78/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_5,plain,
% 5.78/1.51      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 5.78/1.51      inference(cnf_transformation,[],[f36]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_952,plain,
% 5.78/1.51      ( k1_relat_1(k6_relat_1(k1_relat_1(X0))) = k1_relat_1(X0) ),
% 5.78/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_954,plain,
% 5.78/1.51      ( k1_relat_1(k6_relat_1(k1_relat_1(sK0))) = k1_relat_1(sK0) ),
% 5.78/1.51      inference(instantiation,[status(thm)],[c_952]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_1053,plain,
% 5.78/1.51      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top ),
% 5.78/1.51      inference(global_propositional_subsumption,
% 5.78/1.51                [status(thm)],
% 5.78/1.51                [c_881,c_22,c_23,c_24,c_25,c_954]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_6,plain,
% 5.78/1.51      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 5.78/1.51      | ~ v1_relat_1(X0)
% 5.78/1.51      | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
% 5.78/1.51      inference(cnf_transformation,[],[f38]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_655,plain,
% 5.78/1.51      ( k5_relat_1(k6_relat_1(X0),X1) = X1
% 5.78/1.51      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 5.78/1.51      | v1_relat_1(X1) != iProver_top ),
% 5.78/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_1666,plain,
% 5.78/1.51      ( k5_relat_1(k6_relat_1(X0),sK1) = sK1
% 5.78/1.51      | r1_tarski(k2_relat_1(sK0),X0) != iProver_top
% 5.78/1.51      | v1_relat_1(sK1) != iProver_top ),
% 5.78/1.51      inference(superposition,[status(thm)],[c_16,c_655]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_1706,plain,
% 5.78/1.51      ( r1_tarski(k2_relat_1(sK0),X0) != iProver_top
% 5.78/1.51      | k5_relat_1(k6_relat_1(X0),sK1) = sK1 ),
% 5.78/1.51      inference(global_propositional_subsumption,
% 5.78/1.51                [status(thm)],
% 5.78/1.51                [c_1666,c_24]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_1707,plain,
% 5.78/1.51      ( k5_relat_1(k6_relat_1(X0),sK1) = sK1
% 5.78/1.51      | r1_tarski(k2_relat_1(sK0),X0) != iProver_top ),
% 5.78/1.51      inference(renaming,[status(thm)],[c_1706]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_1714,plain,
% 5.78/1.51      ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) = sK1 ),
% 5.78/1.51      inference(superposition,[status(thm)],[c_1053,c_1707]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_7,plain,
% 5.78/1.51      ( ~ v1_relat_1(X0)
% 5.78/1.51      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 5.78/1.51      inference(cnf_transformation,[],[f39]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_654,plain,
% 5.78/1.51      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 5.78/1.51      | v1_relat_1(X0) != iProver_top ),
% 5.78/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_1525,plain,
% 5.78/1.51      ( k5_relat_1(k4_relat_1(X0),k6_relat_1(k2_relat_1(k4_relat_1(X0)))) = k4_relat_1(X0)
% 5.78/1.51      | v1_relat_1(X0) != iProver_top ),
% 5.78/1.51      inference(superposition,[status(thm)],[c_659,c_654]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_3542,plain,
% 5.78/1.51      ( k5_relat_1(k4_relat_1(sK0),k6_relat_1(k2_relat_1(k4_relat_1(sK0)))) = k4_relat_1(sK0) ),
% 5.78/1.51      inference(superposition,[status(thm)],[c_647,c_1525]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_1,plain,
% 5.78/1.51      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 5.78/1.51      inference(cnf_transformation,[],[f34]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_658,plain,
% 5.78/1.51      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 5.78/1.51      | v1_relat_1(X0) != iProver_top ),
% 5.78/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_1317,plain,
% 5.78/1.51      ( k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0) ),
% 5.78/1.51      inference(superposition,[status(thm)],[c_647,c_658]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_3544,plain,
% 5.78/1.51      ( k5_relat_1(k4_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k4_relat_1(sK0) ),
% 5.78/1.51      inference(light_normalisation,[status(thm)],[c_3542,c_1317]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_12618,plain,
% 5.78/1.51      ( k4_relat_1(sK0) = sK1 ),
% 5.78/1.51      inference(light_normalisation,
% 5.78/1.51                [status(thm)],
% 5.78/1.51                [c_12613,c_15,c_1714,c_3544]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_14,negated_conjecture,
% 5.78/1.51      ( k2_funct_1(sK0) != sK1 ),
% 5.78/1.51      inference(cnf_transformation,[],[f53]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(c_672,plain,
% 5.78/1.51      ( k4_relat_1(sK0) != sK1 ),
% 5.78/1.51      inference(light_normalisation,[status(thm)],[c_14,c_257]) ).
% 5.78/1.51  
% 5.78/1.51  cnf(contradiction,plain,
% 5.78/1.51      ( $false ),
% 5.78/1.51      inference(minisat,[status(thm)],[c_12618,c_672]) ).
% 5.78/1.51  
% 5.78/1.51  
% 5.78/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 5.78/1.51  
% 5.78/1.51  ------                               Statistics
% 5.78/1.51  
% 5.78/1.51  ------ General
% 5.78/1.51  
% 5.78/1.51  abstr_ref_over_cycles:                  0
% 5.78/1.51  abstr_ref_under_cycles:                 0
% 5.78/1.51  gc_basic_clause_elim:                   0
% 5.78/1.51  forced_gc_time:                         0
% 5.78/1.51  parsing_time:                           0.011
% 5.78/1.51  unif_index_cands_time:                  0.
% 5.78/1.51  unif_index_add_time:                    0.
% 5.78/1.51  orderings_time:                         0.
% 5.78/1.51  out_proof_time:                         0.011
% 5.78/1.51  total_time:                             0.526
% 5.78/1.51  num_of_symbols:                         43
% 5.78/1.51  num_of_terms:                           11572
% 5.78/1.51  
% 5.78/1.51  ------ Preprocessing
% 5.78/1.51  
% 5.78/1.51  num_of_splits:                          0
% 5.78/1.51  num_of_split_atoms:                     0
% 5.78/1.51  num_of_reused_defs:                     0
% 5.78/1.51  num_eq_ax_congr_red:                    1
% 5.78/1.51  num_of_sem_filtered_clauses:            1
% 5.78/1.51  num_of_subtypes:                        0
% 5.78/1.51  monotx_restored_types:                  0
% 5.78/1.51  sat_num_of_epr_types:                   0
% 5.78/1.51  sat_num_of_non_cyclic_types:            0
% 5.78/1.51  sat_guarded_non_collapsed_types:        0
% 5.78/1.51  num_pure_diseq_elim:                    0
% 5.78/1.51  simp_replaced_by:                       0
% 5.78/1.51  res_preprocessed:                       108
% 5.78/1.51  prep_upred:                             0
% 5.78/1.51  prep_unflattend:                        5
% 5.78/1.51  smt_new_axioms:                         0
% 5.78/1.51  pred_elim_cands:                        3
% 5.78/1.51  pred_elim:                              1
% 5.78/1.51  pred_elim_cl:                           1
% 5.78/1.51  pred_elim_cycles:                       4
% 5.78/1.51  merged_defs:                            0
% 5.78/1.51  merged_defs_ncl:                        0
% 5.78/1.51  bin_hyper_res:                          0
% 5.78/1.51  prep_cycles:                            4
% 5.78/1.51  pred_elim_time:                         0.003
% 5.78/1.51  splitting_time:                         0.
% 5.78/1.51  sem_filter_time:                        0.
% 5.78/1.51  monotx_time:                            0.
% 5.78/1.51  subtype_inf_time:                       0.
% 5.78/1.51  
% 5.78/1.51  ------ Problem properties
% 5.78/1.51  
% 5.78/1.51  clauses:                                21
% 5.78/1.51  conjectures:                            7
% 5.78/1.51  epr:                                    4
% 5.78/1.51  horn:                                   21
% 5.78/1.51  ground:                                 10
% 5.78/1.51  unary:                                  12
% 5.78/1.51  binary:                                 4
% 5.78/1.51  lits:                                   39
% 5.78/1.51  lits_eq:                                14
% 5.78/1.51  fd_pure:                                0
% 5.78/1.51  fd_pseudo:                              0
% 5.78/1.51  fd_cond:                                0
% 5.78/1.51  fd_pseudo_cond:                         0
% 5.78/1.51  ac_symbols:                             0
% 5.78/1.51  
% 5.78/1.51  ------ Propositional Solver
% 5.78/1.51  
% 5.78/1.51  prop_solver_calls:                      28
% 5.78/1.51  prop_fast_solver_calls:                 879
% 5.78/1.51  smt_solver_calls:                       0
% 5.78/1.51  smt_fast_solver_calls:                  0
% 5.78/1.51  prop_num_of_clauses:                    4181
% 5.78/1.51  prop_preprocess_simplified:             9351
% 5.78/1.51  prop_fo_subsumed:                       51
% 5.78/1.51  prop_solver_time:                       0.
% 5.78/1.51  smt_solver_time:                        0.
% 5.78/1.51  smt_fast_solver_time:                   0.
% 5.78/1.51  prop_fast_solver_time:                  0.
% 5.78/1.51  prop_unsat_core_time:                   0.
% 5.78/1.51  
% 5.78/1.51  ------ QBF
% 5.78/1.51  
% 5.78/1.51  qbf_q_res:                              0
% 5.78/1.51  qbf_num_tautologies:                    0
% 5.78/1.51  qbf_prep_cycles:                        0
% 5.78/1.51  
% 5.78/1.51  ------ BMC1
% 5.78/1.51  
% 5.78/1.51  bmc1_current_bound:                     -1
% 5.78/1.51  bmc1_last_solved_bound:                 -1
% 5.78/1.51  bmc1_unsat_core_size:                   -1
% 5.78/1.51  bmc1_unsat_core_parents_size:           -1
% 5.78/1.51  bmc1_merge_next_fun:                    0
% 5.78/1.51  bmc1_unsat_core_clauses_time:           0.
% 5.78/1.51  
% 5.78/1.51  ------ Instantiation
% 5.78/1.51  
% 5.78/1.51  inst_num_of_clauses:                    2299
% 5.78/1.51  inst_num_in_passive:                    362
% 5.78/1.51  inst_num_in_active:                     787
% 5.78/1.51  inst_num_in_unprocessed:                1150
% 5.78/1.51  inst_num_of_loops:                      810
% 5.78/1.51  inst_num_of_learning_restarts:          0
% 5.78/1.51  inst_num_moves_active_passive:          17
% 5.78/1.51  inst_lit_activity:                      0
% 5.78/1.51  inst_lit_activity_moves:                0
% 5.78/1.51  inst_num_tautologies:                   0
% 5.78/1.51  inst_num_prop_implied:                  0
% 5.78/1.51  inst_num_existing_simplified:           0
% 5.78/1.51  inst_num_eq_res_simplified:             0
% 5.78/1.51  inst_num_child_elim:                    0
% 5.78/1.51  inst_num_of_dismatching_blockings:      2654
% 5.78/1.51  inst_num_of_non_proper_insts:           3246
% 5.78/1.51  inst_num_of_duplicates:                 0
% 5.78/1.51  inst_inst_num_from_inst_to_res:         0
% 5.78/1.51  inst_dismatching_checking_time:         0.
% 5.78/1.51  
% 5.78/1.51  ------ Resolution
% 5.78/1.51  
% 5.78/1.51  res_num_of_clauses:                     0
% 5.78/1.51  res_num_in_passive:                     0
% 5.78/1.51  res_num_in_active:                      0
% 5.78/1.51  res_num_of_loops:                       112
% 5.78/1.51  res_forward_subset_subsumed:            319
% 5.78/1.51  res_backward_subset_subsumed:           8
% 5.78/1.51  res_forward_subsumed:                   0
% 5.78/1.51  res_backward_subsumed:                  0
% 5.78/1.51  res_forward_subsumption_resolution:     0
% 5.78/1.51  res_backward_subsumption_resolution:    0
% 5.78/1.51  res_clause_to_clause_subsumption:       766
% 5.78/1.51  res_orphan_elimination:                 0
% 5.78/1.51  res_tautology_del:                      374
% 5.78/1.51  res_num_eq_res_simplified:              0
% 5.78/1.51  res_num_sel_changes:                    0
% 5.78/1.51  res_moves_from_active_to_pass:          0
% 5.78/1.51  
% 5.78/1.51  ------ Superposition
% 5.78/1.51  
% 5.78/1.51  sup_time_total:                         0.
% 5.78/1.51  sup_time_generating:                    0.
% 5.78/1.51  sup_time_sim_full:                      0.
% 5.78/1.51  sup_time_sim_immed:                     0.
% 5.78/1.51  
% 5.78/1.51  sup_num_of_clauses:                     252
% 5.78/1.51  sup_num_in_active:                      158
% 5.78/1.51  sup_num_in_passive:                     94
% 5.78/1.51  sup_num_of_loops:                       160
% 5.78/1.51  sup_fw_superposition:                   186
% 5.78/1.51  sup_bw_superposition:                   67
% 5.78/1.51  sup_immediate_simplified:               79
% 5.78/1.51  sup_given_eliminated:                   1
% 5.78/1.51  comparisons_done:                       0
% 5.78/1.51  comparisons_avoided:                    0
% 5.78/1.51  
% 5.78/1.51  ------ Simplifications
% 5.78/1.51  
% 5.78/1.51  
% 5.78/1.51  sim_fw_subset_subsumed:                 2
% 5.78/1.51  sim_bw_subset_subsumed:                 0
% 5.78/1.51  sim_fw_subsumed:                        13
% 5.78/1.51  sim_bw_subsumed:                        0
% 5.78/1.51  sim_fw_subsumption_res:                 0
% 5.78/1.51  sim_bw_subsumption_res:                 0
% 5.78/1.51  sim_tautology_del:                      0
% 5.78/1.51  sim_eq_tautology_del:                   4
% 5.78/1.51  sim_eq_res_simp:                        5
% 5.78/1.51  sim_fw_demodulated:                     19
% 5.78/1.51  sim_bw_demodulated:                     5
% 5.78/1.51  sim_light_normalised:                   74
% 5.78/1.51  sim_joinable_taut:                      0
% 5.78/1.51  sim_joinable_simp:                      0
% 5.78/1.51  sim_ac_normalised:                      0
% 5.78/1.51  sim_smt_subsumption:                    0
% 5.78/1.51  
%------------------------------------------------------------------------------
