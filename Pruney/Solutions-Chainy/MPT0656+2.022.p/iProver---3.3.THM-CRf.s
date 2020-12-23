%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:48 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 417 expanded)
%              Number of clauses        :   74 ( 112 expanded)
%              Number of leaves         :   11 ( 107 expanded)
%              Depth                    :   17
%              Number of atoms          :  398 (2573 expanded)
%              Number of equality atoms :  203 (1031 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k1_relat_1(X1) = k2_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
                & k1_relat_1(X1) = k2_relat_1(X0)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k1_relat_1(X1) = k2_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k1_relat_1(X1) = k2_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k1_relat_1(X1) = k2_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k2_funct_1(X0) != sK1
        & k5_relat_1(X0,sK1) = k6_relat_1(k1_relat_1(X0))
        & k1_relat_1(sK1) = k2_relat_1(X0)
        & v2_funct_1(X0)
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & k1_relat_1(X1) = k2_relat_1(X0)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0))
          & k1_relat_1(X1) = k2_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k2_funct_1(sK0) != sK1
    & k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))
    & k1_relat_1(sK1) = k2_relat_1(sK0)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).

fof(f42,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    k1_relat_1(sK1) = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_561,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_559,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_560,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_564,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_568,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1524,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_564,c_568])).

cnf(c_5188,plain,
    ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_560,c_1524])).

cnf(c_20,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6483,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5188,c_20])).

cnf(c_6484,plain,
    ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6483])).

cnf(c_6492,plain,
    ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK0),sK0),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_559,c_6484])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,negated_conjecture,
    ( v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_221,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_222,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_29,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_224,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_222,c_19,c_18,c_15,c_29])).

cnf(c_6495,plain,
    ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6492,c_224])).

cnf(c_6523,plain,
    ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) ),
    inference(superposition,[status(thm)],[c_561,c_6495])).

cnf(c_13,negated_conjecture,
    ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_566,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_893,plain,
    ( k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) = sK0 ),
    inference(superposition,[status(thm)],[c_559,c_566])).

cnf(c_7,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_563,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1293,plain,
    ( r1_tarski(k2_relat_1(sK0),k1_relat_1(k6_relat_1(k2_relat_1(sK0)))) = iProver_top
    | v1_funct_1(k6_relat_1(k2_relat_1(sK0))) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(k6_relat_1(k2_relat_1(sK0))) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_893,c_563])).

cnf(c_2,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1311,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top
    | v1_funct_1(k6_relat_1(k2_relat_1(sK0))) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(k6_relat_1(k2_relat_1(sK0))) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1293,c_2])).

cnf(c_21,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_40,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_42,plain,
    ( v1_funct_1(sK0) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_43,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_45,plain,
    ( v1_funct_1(k2_funct_1(sK0)) = iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_213,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_214,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_26,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_216,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_214,c_19,c_18,c_15,c_26])).

cnf(c_1291,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(sK0))) != k1_relat_1(sK0)
    | r1_tarski(k2_relat_1(sK0),k1_relat_1(k2_funct_1(sK0))) = iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_216,c_563])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_229,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_230,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_32,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_232,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_230,c_19,c_18,c_15,c_32])).

cnf(c_1337,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(sK0))) != k1_relat_1(sK0)
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1291,c_232])).

cnf(c_1338,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1337,c_2])).

cnf(c_1339,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top
    | v1_funct_1(k2_funct_1(sK0)) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(k2_funct_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1338])).

cnf(c_1630,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1311,c_20,c_21,c_42,c_45,c_1339])).

cnf(c_14,negated_conjecture,
    ( k1_relat_1(sK1) = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_567,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1153,plain,
    ( k5_relat_1(k6_relat_1(X0),sK1) = sK1
    | r1_tarski(k2_relat_1(sK0),X0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_567])).

cnf(c_22,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1183,plain,
    ( r1_tarski(k2_relat_1(sK0),X0) != iProver_top
    | k5_relat_1(k6_relat_1(X0),sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1153,c_22])).

cnf(c_1184,plain,
    ( k5_relat_1(k6_relat_1(X0),sK1) = sK1
    | r1_tarski(k2_relat_1(sK0),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1183])).

cnf(c_1637,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_1630,c_1184])).

cnf(c_978,plain,
    ( k5_relat_1(k2_funct_1(X0),k6_relat_1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_564,c_566])).

cnf(c_2202,plain,
    ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) = k2_funct_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_560,c_978])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_237,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_15])).

cnf(c_238,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_35,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_240,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_238,c_19,c_18,c_15,c_35])).

cnf(c_2205,plain,
    ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k2_funct_1(sK0)
    | v1_relat_1(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2202,c_240])).

cnf(c_2509,plain,
    ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k2_funct_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2205,c_20])).

cnf(c_6528,plain,
    ( k2_funct_1(sK0) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_6523,c_13,c_1637,c_2509])).

cnf(c_12,negated_conjecture,
    ( k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6528,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:00:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.11/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.11/0.99  
% 3.11/0.99  ------  iProver source info
% 3.11/0.99  
% 3.11/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.11/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.11/0.99  git: non_committed_changes: false
% 3.11/0.99  git: last_make_outside_of_git: false
% 3.11/0.99  
% 3.11/0.99  ------ 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options
% 3.11/0.99  
% 3.11/0.99  --out_options                           all
% 3.11/0.99  --tptp_safe_out                         true
% 3.11/0.99  --problem_path                          ""
% 3.11/0.99  --include_path                          ""
% 3.11/0.99  --clausifier                            res/vclausify_rel
% 3.11/0.99  --clausifier_options                    --mode clausify
% 3.11/0.99  --stdin                                 false
% 3.11/0.99  --stats_out                             all
% 3.11/0.99  
% 3.11/0.99  ------ General Options
% 3.11/0.99  
% 3.11/0.99  --fof                                   false
% 3.11/0.99  --time_out_real                         305.
% 3.11/0.99  --time_out_virtual                      -1.
% 3.11/0.99  --symbol_type_check                     false
% 3.11/0.99  --clausify_out                          false
% 3.11/0.99  --sig_cnt_out                           false
% 3.11/0.99  --trig_cnt_out                          false
% 3.11/0.99  --trig_cnt_out_tolerance                1.
% 3.11/0.99  --trig_cnt_out_sk_spl                   false
% 3.11/0.99  --abstr_cl_out                          false
% 3.11/0.99  
% 3.11/0.99  ------ Global Options
% 3.11/0.99  
% 3.11/0.99  --schedule                              default
% 3.11/0.99  --add_important_lit                     false
% 3.11/0.99  --prop_solver_per_cl                    1000
% 3.11/0.99  --min_unsat_core                        false
% 3.11/0.99  --soft_assumptions                      false
% 3.11/0.99  --soft_lemma_size                       3
% 3.11/0.99  --prop_impl_unit_size                   0
% 3.11/0.99  --prop_impl_unit                        []
% 3.11/0.99  --share_sel_clauses                     true
% 3.11/0.99  --reset_solvers                         false
% 3.11/0.99  --bc_imp_inh                            [conj_cone]
% 3.11/0.99  --conj_cone_tolerance                   3.
% 3.11/0.99  --extra_neg_conj                        none
% 3.11/0.99  --large_theory_mode                     true
% 3.11/0.99  --prolific_symb_bound                   200
% 3.11/0.99  --lt_threshold                          2000
% 3.11/0.99  --clause_weak_htbl                      true
% 3.11/0.99  --gc_record_bc_elim                     false
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing Options
% 3.11/0.99  
% 3.11/0.99  --preprocessing_flag                    true
% 3.11/0.99  --time_out_prep_mult                    0.1
% 3.11/0.99  --splitting_mode                        input
% 3.11/0.99  --splitting_grd                         true
% 3.11/0.99  --splitting_cvd                         false
% 3.11/0.99  --splitting_cvd_svl                     false
% 3.11/0.99  --splitting_nvd                         32
% 3.11/0.99  --sub_typing                            true
% 3.11/0.99  --prep_gs_sim                           true
% 3.11/0.99  --prep_unflatten                        true
% 3.11/0.99  --prep_res_sim                          true
% 3.11/0.99  --prep_upred                            true
% 3.11/0.99  --prep_sem_filter                       exhaustive
% 3.11/0.99  --prep_sem_filter_out                   false
% 3.11/0.99  --pred_elim                             true
% 3.11/0.99  --res_sim_input                         true
% 3.11/0.99  --eq_ax_congr_red                       true
% 3.11/0.99  --pure_diseq_elim                       true
% 3.11/0.99  --brand_transform                       false
% 3.11/0.99  --non_eq_to_eq                          false
% 3.11/0.99  --prep_def_merge                        true
% 3.11/0.99  --prep_def_merge_prop_impl              false
% 3.11/0.99  --prep_def_merge_mbd                    true
% 3.11/0.99  --prep_def_merge_tr_red                 false
% 3.11/0.99  --prep_def_merge_tr_cl                  false
% 3.11/0.99  --smt_preprocessing                     true
% 3.11/0.99  --smt_ac_axioms                         fast
% 3.11/0.99  --preprocessed_out                      false
% 3.11/0.99  --preprocessed_stats                    false
% 3.11/0.99  
% 3.11/0.99  ------ Abstraction refinement Options
% 3.11/0.99  
% 3.11/0.99  --abstr_ref                             []
% 3.11/0.99  --abstr_ref_prep                        false
% 3.11/0.99  --abstr_ref_until_sat                   false
% 3.11/0.99  --abstr_ref_sig_restrict                funpre
% 3.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/0.99  --abstr_ref_under                       []
% 3.11/0.99  
% 3.11/0.99  ------ SAT Options
% 3.11/0.99  
% 3.11/0.99  --sat_mode                              false
% 3.11/0.99  --sat_fm_restart_options                ""
% 3.11/0.99  --sat_gr_def                            false
% 3.11/0.99  --sat_epr_types                         true
% 3.11/0.99  --sat_non_cyclic_types                  false
% 3.11/0.99  --sat_finite_models                     false
% 3.11/0.99  --sat_fm_lemmas                         false
% 3.11/0.99  --sat_fm_prep                           false
% 3.11/0.99  --sat_fm_uc_incr                        true
% 3.11/0.99  --sat_out_model                         small
% 3.11/0.99  --sat_out_clauses                       false
% 3.11/0.99  
% 3.11/0.99  ------ QBF Options
% 3.11/0.99  
% 3.11/0.99  --qbf_mode                              false
% 3.11/0.99  --qbf_elim_univ                         false
% 3.11/0.99  --qbf_dom_inst                          none
% 3.11/0.99  --qbf_dom_pre_inst                      false
% 3.11/0.99  --qbf_sk_in                             false
% 3.11/0.99  --qbf_pred_elim                         true
% 3.11/0.99  --qbf_split                             512
% 3.11/0.99  
% 3.11/0.99  ------ BMC1 Options
% 3.11/0.99  
% 3.11/0.99  --bmc1_incremental                      false
% 3.11/0.99  --bmc1_axioms                           reachable_all
% 3.11/0.99  --bmc1_min_bound                        0
% 3.11/0.99  --bmc1_max_bound                        -1
% 3.11/0.99  --bmc1_max_bound_default                -1
% 3.11/0.99  --bmc1_symbol_reachability              true
% 3.11/0.99  --bmc1_property_lemmas                  false
% 3.11/0.99  --bmc1_k_induction                      false
% 3.11/0.99  --bmc1_non_equiv_states                 false
% 3.11/0.99  --bmc1_deadlock                         false
% 3.11/0.99  --bmc1_ucm                              false
% 3.11/0.99  --bmc1_add_unsat_core                   none
% 3.11/0.99  --bmc1_unsat_core_children              false
% 3.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/0.99  --bmc1_out_stat                         full
% 3.11/0.99  --bmc1_ground_init                      false
% 3.11/0.99  --bmc1_pre_inst_next_state              false
% 3.11/0.99  --bmc1_pre_inst_state                   false
% 3.11/0.99  --bmc1_pre_inst_reach_state             false
% 3.11/0.99  --bmc1_out_unsat_core                   false
% 3.11/0.99  --bmc1_aig_witness_out                  false
% 3.11/0.99  --bmc1_verbose                          false
% 3.11/0.99  --bmc1_dump_clauses_tptp                false
% 3.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.11/0.99  --bmc1_dump_file                        -
% 3.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.11/0.99  --bmc1_ucm_extend_mode                  1
% 3.11/0.99  --bmc1_ucm_init_mode                    2
% 3.11/0.99  --bmc1_ucm_cone_mode                    none
% 3.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.11/0.99  --bmc1_ucm_relax_model                  4
% 3.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/0.99  --bmc1_ucm_layered_model                none
% 3.11/0.99  --bmc1_ucm_max_lemma_size               10
% 3.11/0.99  
% 3.11/0.99  ------ AIG Options
% 3.11/0.99  
% 3.11/0.99  --aig_mode                              false
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation Options
% 3.11/0.99  
% 3.11/0.99  --instantiation_flag                    true
% 3.11/0.99  --inst_sos_flag                         false
% 3.11/0.99  --inst_sos_phase                        true
% 3.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel_side                     num_symb
% 3.11/0.99  --inst_solver_per_active                1400
% 3.11/0.99  --inst_solver_calls_frac                1.
% 3.11/0.99  --inst_passive_queue_type               priority_queues
% 3.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/0.99  --inst_passive_queues_freq              [25;2]
% 3.11/0.99  --inst_dismatching                      true
% 3.11/0.99  --inst_eager_unprocessed_to_passive     true
% 3.11/0.99  --inst_prop_sim_given                   true
% 3.11/0.99  --inst_prop_sim_new                     false
% 3.11/0.99  --inst_subs_new                         false
% 3.11/0.99  --inst_eq_res_simp                      false
% 3.11/0.99  --inst_subs_given                       false
% 3.11/0.99  --inst_orphan_elimination               true
% 3.11/0.99  --inst_learning_loop_flag               true
% 3.11/0.99  --inst_learning_start                   3000
% 3.11/0.99  --inst_learning_factor                  2
% 3.11/0.99  --inst_start_prop_sim_after_learn       3
% 3.11/0.99  --inst_sel_renew                        solver
% 3.11/0.99  --inst_lit_activity_flag                true
% 3.11/0.99  --inst_restr_to_given                   false
% 3.11/0.99  --inst_activity_threshold               500
% 3.11/0.99  --inst_out_proof                        true
% 3.11/0.99  
% 3.11/0.99  ------ Resolution Options
% 3.11/0.99  
% 3.11/0.99  --resolution_flag                       true
% 3.11/0.99  --res_lit_sel                           adaptive
% 3.11/0.99  --res_lit_sel_side                      none
% 3.11/0.99  --res_ordering                          kbo
% 3.11/0.99  --res_to_prop_solver                    active
% 3.11/0.99  --res_prop_simpl_new                    false
% 3.11/0.99  --res_prop_simpl_given                  true
% 3.11/0.99  --res_passive_queue_type                priority_queues
% 3.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/0.99  --res_passive_queues_freq               [15;5]
% 3.11/0.99  --res_forward_subs                      full
% 3.11/0.99  --res_backward_subs                     full
% 3.11/0.99  --res_forward_subs_resolution           true
% 3.11/0.99  --res_backward_subs_resolution          true
% 3.11/0.99  --res_orphan_elimination                true
% 3.11/0.99  --res_time_limit                        2.
% 3.11/0.99  --res_out_proof                         true
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Options
% 3.11/0.99  
% 3.11/0.99  --superposition_flag                    true
% 3.11/0.99  --sup_passive_queue_type                priority_queues
% 3.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.11/0.99  --demod_completeness_check              fast
% 3.11/0.99  --demod_use_ground                      true
% 3.11/0.99  --sup_to_prop_solver                    passive
% 3.11/0.99  --sup_prop_simpl_new                    true
% 3.11/0.99  --sup_prop_simpl_given                  true
% 3.11/0.99  --sup_fun_splitting                     false
% 3.11/0.99  --sup_smt_interval                      50000
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Simplification Setup
% 3.11/0.99  
% 3.11/0.99  --sup_indices_passive                   []
% 3.11/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_full_bw                           [BwDemod]
% 3.11/0.99  --sup_immed_triv                        [TrivRules]
% 3.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_immed_bw_main                     []
% 3.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  
% 3.11/0.99  ------ Combination Options
% 3.11/0.99  
% 3.11/0.99  --comb_res_mult                         3
% 3.11/0.99  --comb_sup_mult                         2
% 3.11/0.99  --comb_inst_mult                        10
% 3.11/0.99  
% 3.11/0.99  ------ Debug Options
% 3.11/0.99  
% 3.11/0.99  --dbg_backtrace                         false
% 3.11/0.99  --dbg_dump_prop_clauses                 false
% 3.11/0.99  --dbg_dump_prop_clauses_file            -
% 3.11/0.99  --dbg_out_stat                          false
% 3.11/0.99  ------ Parsing...
% 3.11/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.11/0.99  ------ Proving...
% 3.11/0.99  ------ Problem Properties 
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  clauses                                 19
% 3.11/0.99  conjectures                             7
% 3.11/0.99  EPR                                     4
% 3.11/0.99  Horn                                    19
% 3.11/0.99  unary                                   13
% 3.11/0.99  binary                                  1
% 3.11/0.99  lits                                    34
% 3.11/0.99  lits eq                                 13
% 3.11/0.99  fd_pure                                 0
% 3.11/0.99  fd_pseudo                               0
% 3.11/0.99  fd_cond                                 0
% 3.11/0.99  fd_pseudo_cond                          0
% 3.11/0.99  AC symbols                              0
% 3.11/0.99  
% 3.11/0.99  ------ Schedule dynamic 5 is on 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  ------ 
% 3.11/0.99  Current options:
% 3.11/0.99  ------ 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options
% 3.11/0.99  
% 3.11/0.99  --out_options                           all
% 3.11/0.99  --tptp_safe_out                         true
% 3.11/0.99  --problem_path                          ""
% 3.11/0.99  --include_path                          ""
% 3.11/0.99  --clausifier                            res/vclausify_rel
% 3.11/0.99  --clausifier_options                    --mode clausify
% 3.11/0.99  --stdin                                 false
% 3.11/0.99  --stats_out                             all
% 3.11/0.99  
% 3.11/0.99  ------ General Options
% 3.11/0.99  
% 3.11/0.99  --fof                                   false
% 3.11/0.99  --time_out_real                         305.
% 3.11/0.99  --time_out_virtual                      -1.
% 3.11/0.99  --symbol_type_check                     false
% 3.11/0.99  --clausify_out                          false
% 3.11/0.99  --sig_cnt_out                           false
% 3.11/0.99  --trig_cnt_out                          false
% 3.11/0.99  --trig_cnt_out_tolerance                1.
% 3.11/0.99  --trig_cnt_out_sk_spl                   false
% 3.11/0.99  --abstr_cl_out                          false
% 3.11/0.99  
% 3.11/0.99  ------ Global Options
% 3.11/0.99  
% 3.11/0.99  --schedule                              default
% 3.11/0.99  --add_important_lit                     false
% 3.11/0.99  --prop_solver_per_cl                    1000
% 3.11/0.99  --min_unsat_core                        false
% 3.11/0.99  --soft_assumptions                      false
% 3.11/0.99  --soft_lemma_size                       3
% 3.11/0.99  --prop_impl_unit_size                   0
% 3.11/0.99  --prop_impl_unit                        []
% 3.11/0.99  --share_sel_clauses                     true
% 3.11/0.99  --reset_solvers                         false
% 3.11/0.99  --bc_imp_inh                            [conj_cone]
% 3.11/0.99  --conj_cone_tolerance                   3.
% 3.11/0.99  --extra_neg_conj                        none
% 3.11/0.99  --large_theory_mode                     true
% 3.11/0.99  --prolific_symb_bound                   200
% 3.11/0.99  --lt_threshold                          2000
% 3.11/0.99  --clause_weak_htbl                      true
% 3.11/0.99  --gc_record_bc_elim                     false
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing Options
% 3.11/0.99  
% 3.11/0.99  --preprocessing_flag                    true
% 3.11/0.99  --time_out_prep_mult                    0.1
% 3.11/0.99  --splitting_mode                        input
% 3.11/0.99  --splitting_grd                         true
% 3.11/0.99  --splitting_cvd                         false
% 3.11/0.99  --splitting_cvd_svl                     false
% 3.11/0.99  --splitting_nvd                         32
% 3.11/0.99  --sub_typing                            true
% 3.11/0.99  --prep_gs_sim                           true
% 3.11/0.99  --prep_unflatten                        true
% 3.11/0.99  --prep_res_sim                          true
% 3.11/0.99  --prep_upred                            true
% 3.11/0.99  --prep_sem_filter                       exhaustive
% 3.11/0.99  --prep_sem_filter_out                   false
% 3.11/0.99  --pred_elim                             true
% 3.11/0.99  --res_sim_input                         true
% 3.11/0.99  --eq_ax_congr_red                       true
% 3.11/0.99  --pure_diseq_elim                       true
% 3.11/0.99  --brand_transform                       false
% 3.11/0.99  --non_eq_to_eq                          false
% 3.11/0.99  --prep_def_merge                        true
% 3.11/0.99  --prep_def_merge_prop_impl              false
% 3.11/0.99  --prep_def_merge_mbd                    true
% 3.11/0.99  --prep_def_merge_tr_red                 false
% 3.11/0.99  --prep_def_merge_tr_cl                  false
% 3.11/0.99  --smt_preprocessing                     true
% 3.11/0.99  --smt_ac_axioms                         fast
% 3.11/0.99  --preprocessed_out                      false
% 3.11/0.99  --preprocessed_stats                    false
% 3.11/0.99  
% 3.11/0.99  ------ Abstraction refinement Options
% 3.11/0.99  
% 3.11/0.99  --abstr_ref                             []
% 3.11/0.99  --abstr_ref_prep                        false
% 3.11/0.99  --abstr_ref_until_sat                   false
% 3.11/0.99  --abstr_ref_sig_restrict                funpre
% 3.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/0.99  --abstr_ref_under                       []
% 3.11/0.99  
% 3.11/0.99  ------ SAT Options
% 3.11/0.99  
% 3.11/0.99  --sat_mode                              false
% 3.11/0.99  --sat_fm_restart_options                ""
% 3.11/0.99  --sat_gr_def                            false
% 3.11/0.99  --sat_epr_types                         true
% 3.11/0.99  --sat_non_cyclic_types                  false
% 3.11/0.99  --sat_finite_models                     false
% 3.11/0.99  --sat_fm_lemmas                         false
% 3.11/0.99  --sat_fm_prep                           false
% 3.11/0.99  --sat_fm_uc_incr                        true
% 3.11/0.99  --sat_out_model                         small
% 3.11/0.99  --sat_out_clauses                       false
% 3.11/0.99  
% 3.11/0.99  ------ QBF Options
% 3.11/0.99  
% 3.11/0.99  --qbf_mode                              false
% 3.11/0.99  --qbf_elim_univ                         false
% 3.11/0.99  --qbf_dom_inst                          none
% 3.11/0.99  --qbf_dom_pre_inst                      false
% 3.11/0.99  --qbf_sk_in                             false
% 3.11/0.99  --qbf_pred_elim                         true
% 3.11/0.99  --qbf_split                             512
% 3.11/0.99  
% 3.11/0.99  ------ BMC1 Options
% 3.11/0.99  
% 3.11/0.99  --bmc1_incremental                      false
% 3.11/0.99  --bmc1_axioms                           reachable_all
% 3.11/0.99  --bmc1_min_bound                        0
% 3.11/0.99  --bmc1_max_bound                        -1
% 3.11/0.99  --bmc1_max_bound_default                -1
% 3.11/0.99  --bmc1_symbol_reachability              true
% 3.11/0.99  --bmc1_property_lemmas                  false
% 3.11/0.99  --bmc1_k_induction                      false
% 3.11/0.99  --bmc1_non_equiv_states                 false
% 3.11/0.99  --bmc1_deadlock                         false
% 3.11/0.99  --bmc1_ucm                              false
% 3.11/0.99  --bmc1_add_unsat_core                   none
% 3.11/0.99  --bmc1_unsat_core_children              false
% 3.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/0.99  --bmc1_out_stat                         full
% 3.11/0.99  --bmc1_ground_init                      false
% 3.11/0.99  --bmc1_pre_inst_next_state              false
% 3.11/0.99  --bmc1_pre_inst_state                   false
% 3.11/0.99  --bmc1_pre_inst_reach_state             false
% 3.11/0.99  --bmc1_out_unsat_core                   false
% 3.11/0.99  --bmc1_aig_witness_out                  false
% 3.11/0.99  --bmc1_verbose                          false
% 3.11/0.99  --bmc1_dump_clauses_tptp                false
% 3.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.11/0.99  --bmc1_dump_file                        -
% 3.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.11/0.99  --bmc1_ucm_extend_mode                  1
% 3.11/0.99  --bmc1_ucm_init_mode                    2
% 3.11/0.99  --bmc1_ucm_cone_mode                    none
% 3.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.11/0.99  --bmc1_ucm_relax_model                  4
% 3.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/0.99  --bmc1_ucm_layered_model                none
% 3.11/0.99  --bmc1_ucm_max_lemma_size               10
% 3.11/0.99  
% 3.11/0.99  ------ AIG Options
% 3.11/0.99  
% 3.11/0.99  --aig_mode                              false
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation Options
% 3.11/0.99  
% 3.11/0.99  --instantiation_flag                    true
% 3.11/0.99  --inst_sos_flag                         false
% 3.11/0.99  --inst_sos_phase                        true
% 3.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel_side                     none
% 3.11/0.99  --inst_solver_per_active                1400
% 3.11/0.99  --inst_solver_calls_frac                1.
% 3.11/0.99  --inst_passive_queue_type               priority_queues
% 3.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/0.99  --inst_passive_queues_freq              [25;2]
% 3.11/0.99  --inst_dismatching                      true
% 3.11/0.99  --inst_eager_unprocessed_to_passive     true
% 3.11/0.99  --inst_prop_sim_given                   true
% 3.11/0.99  --inst_prop_sim_new                     false
% 3.11/0.99  --inst_subs_new                         false
% 3.11/0.99  --inst_eq_res_simp                      false
% 3.11/0.99  --inst_subs_given                       false
% 3.11/0.99  --inst_orphan_elimination               true
% 3.11/0.99  --inst_learning_loop_flag               true
% 3.11/0.99  --inst_learning_start                   3000
% 3.11/0.99  --inst_learning_factor                  2
% 3.11/0.99  --inst_start_prop_sim_after_learn       3
% 3.11/0.99  --inst_sel_renew                        solver
% 3.11/0.99  --inst_lit_activity_flag                true
% 3.11/0.99  --inst_restr_to_given                   false
% 3.11/0.99  --inst_activity_threshold               500
% 3.11/0.99  --inst_out_proof                        true
% 3.11/0.99  
% 3.11/0.99  ------ Resolution Options
% 3.11/0.99  
% 3.11/0.99  --resolution_flag                       false
% 3.11/0.99  --res_lit_sel                           adaptive
% 3.11/0.99  --res_lit_sel_side                      none
% 3.11/0.99  --res_ordering                          kbo
% 3.11/0.99  --res_to_prop_solver                    active
% 3.11/0.99  --res_prop_simpl_new                    false
% 3.11/0.99  --res_prop_simpl_given                  true
% 3.11/0.99  --res_passive_queue_type                priority_queues
% 3.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/0.99  --res_passive_queues_freq               [15;5]
% 3.11/0.99  --res_forward_subs                      full
% 3.11/0.99  --res_backward_subs                     full
% 3.11/0.99  --res_forward_subs_resolution           true
% 3.11/0.99  --res_backward_subs_resolution          true
% 3.11/0.99  --res_orphan_elimination                true
% 3.11/0.99  --res_time_limit                        2.
% 3.11/0.99  --res_out_proof                         true
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Options
% 3.11/0.99  
% 3.11/0.99  --superposition_flag                    true
% 3.11/0.99  --sup_passive_queue_type                priority_queues
% 3.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.11/0.99  --demod_completeness_check              fast
% 3.11/0.99  --demod_use_ground                      true
% 3.11/0.99  --sup_to_prop_solver                    passive
% 3.11/0.99  --sup_prop_simpl_new                    true
% 3.11/0.99  --sup_prop_simpl_given                  true
% 3.11/0.99  --sup_fun_splitting                     false
% 3.11/0.99  --sup_smt_interval                      50000
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Simplification Setup
% 3.11/0.99  
% 3.11/0.99  --sup_indices_passive                   []
% 3.11/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_full_bw                           [BwDemod]
% 3.11/0.99  --sup_immed_triv                        [TrivRules]
% 3.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_immed_bw_main                     []
% 3.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  
% 3.11/0.99  ------ Combination Options
% 3.11/0.99  
% 3.11/0.99  --comb_res_mult                         3
% 3.11/0.99  --comb_sup_mult                         2
% 3.11/0.99  --comb_inst_mult                        10
% 3.11/0.99  
% 3.11/0.99  ------ Debug Options
% 3.11/0.99  
% 3.11/0.99  --dbg_backtrace                         false
% 3.11/0.99  --dbg_dump_prop_clauses                 false
% 3.11/0.99  --dbg_dump_prop_clauses_file            -
% 3.11/0.99  --dbg_out_stat                          false
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  ------ Proving...
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  % SZS status Theorem for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  fof(f9,conjecture,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f10,negated_conjecture,(
% 3.11/0.99    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.11/0.99    inference(negated_conjecture,[],[f9])).
% 3.11/0.99  
% 3.11/0.99  fof(f23,plain,(
% 3.11/0.99    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f10])).
% 3.11/0.99  
% 3.11/0.99  fof(f24,plain,(
% 3.11/0.99    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.11/0.99    inference(flattening,[],[f23])).
% 3.11/0.99  
% 3.11/0.99  fof(f26,plain,(
% 3.11/0.99    ( ! [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) != sK1 & k5_relat_1(X0,sK1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(sK1) = k2_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(sK1) & v1_relat_1(sK1))) )),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f25,plain,(
% 3.11/0.99    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0)) & k1_relat_1(X1) = k2_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f27,plain,(
% 3.11/0.99    (k2_funct_1(sK0) != sK1 & k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) & k1_relat_1(sK1) = k2_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 3.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).
% 3.11/0.99  
% 3.11/0.99  fof(f42,plain,(
% 3.11/0.99    v1_relat_1(sK1)),
% 3.11/0.99    inference(cnf_transformation,[],[f27])).
% 3.11/0.99  
% 3.11/0.99  fof(f40,plain,(
% 3.11/0.99    v1_relat_1(sK0)),
% 3.11/0.99    inference(cnf_transformation,[],[f27])).
% 3.11/0.99  
% 3.11/0.99  fof(f41,plain,(
% 3.11/0.99    v1_funct_1(sK0)),
% 3.11/0.99    inference(cnf_transformation,[],[f27])).
% 3.11/0.99  
% 3.11/0.99  fof(f5,axiom,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f15,plain,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f5])).
% 3.11/0.99  
% 3.11/0.99  fof(f16,plain,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.11/0.99    inference(flattening,[],[f15])).
% 3.11/0.99  
% 3.11/0.99  fof(f33,plain,(
% 3.11/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f16])).
% 3.11/0.99  
% 3.11/0.99  fof(f1,axiom,(
% 3.11/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f11,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.11/0.99    inference(ennf_transformation,[],[f1])).
% 3.11/0.99  
% 3.11/0.99  fof(f28,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f11])).
% 3.11/0.99  
% 3.11/0.99  fof(f8,axiom,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f21,plain,(
% 3.11/0.99    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f8])).
% 3.11/0.99  
% 3.11/0.99  fof(f22,plain,(
% 3.11/0.99    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.11/0.99    inference(flattening,[],[f21])).
% 3.11/0.99  
% 3.11/0.99  fof(f39,plain,(
% 3.11/0.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f22])).
% 3.11/0.99  
% 3.11/0.99  fof(f44,plain,(
% 3.11/0.99    v2_funct_1(sK0)),
% 3.11/0.99    inference(cnf_transformation,[],[f27])).
% 3.11/0.99  
% 3.11/0.99  fof(f46,plain,(
% 3.11/0.99    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))),
% 3.11/0.99    inference(cnf_transformation,[],[f27])).
% 3.11/0.99  
% 3.11/0.99  fof(f4,axiom,(
% 3.11/0.99    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f14,plain,(
% 3.11/0.99    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.11/0.99    inference(ennf_transformation,[],[f4])).
% 3.11/0.99  
% 3.11/0.99  fof(f32,plain,(
% 3.11/0.99    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f14])).
% 3.11/0.99  
% 3.11/0.99  fof(f6,axiom,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f17,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.11/0.99    inference(ennf_transformation,[],[f6])).
% 3.11/0.99  
% 3.11/0.99  fof(f18,plain,(
% 3.11/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.11/0.99    inference(flattening,[],[f17])).
% 3.11/0.99  
% 3.11/0.99  fof(f35,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f18])).
% 3.11/0.99  
% 3.11/0.99  fof(f2,axiom,(
% 3.11/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f29,plain,(
% 3.11/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.11/0.99    inference(cnf_transformation,[],[f2])).
% 3.11/0.99  
% 3.11/0.99  fof(f34,plain,(
% 3.11/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f16])).
% 3.11/0.99  
% 3.11/0.99  fof(f38,plain,(
% 3.11/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f22])).
% 3.11/0.99  
% 3.11/0.99  fof(f7,axiom,(
% 3.11/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/1.00  
% 3.11/1.00  fof(f19,plain,(
% 3.11/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.11/1.00    inference(ennf_transformation,[],[f7])).
% 3.11/1.00  
% 3.11/1.00  fof(f20,plain,(
% 3.11/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.11/1.00    inference(flattening,[],[f19])).
% 3.11/1.00  
% 3.11/1.00  fof(f36,plain,(
% 3.11/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/1.00    inference(cnf_transformation,[],[f20])).
% 3.11/1.00  
% 3.11/1.00  fof(f45,plain,(
% 3.11/1.00    k1_relat_1(sK1) = k2_relat_1(sK0)),
% 3.11/1.00    inference(cnf_transformation,[],[f27])).
% 3.11/1.00  
% 3.11/1.00  fof(f3,axiom,(
% 3.11/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/1.00  
% 3.11/1.00  fof(f12,plain,(
% 3.11/1.00    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.11/1.00    inference(ennf_transformation,[],[f3])).
% 3.11/1.00  
% 3.11/1.00  fof(f13,plain,(
% 3.11/1.00    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.11/1.00    inference(flattening,[],[f12])).
% 3.11/1.00  
% 3.11/1.00  fof(f31,plain,(
% 3.11/1.00    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.11/1.00    inference(cnf_transformation,[],[f13])).
% 3.11/1.00  
% 3.11/1.00  fof(f37,plain,(
% 3.11/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/1.00    inference(cnf_transformation,[],[f20])).
% 3.11/1.00  
% 3.11/1.00  fof(f47,plain,(
% 3.11/1.00    k2_funct_1(sK0) != sK1),
% 3.11/1.00    inference(cnf_transformation,[],[f27])).
% 3.11/1.00  
% 3.11/1.00  cnf(c_17,negated_conjecture,
% 3.11/1.00      ( v1_relat_1(sK1) ),
% 3.11/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_561,plain,
% 3.11/1.00      ( v1_relat_1(sK1) = iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_19,negated_conjecture,
% 3.11/1.00      ( v1_relat_1(sK0) ),
% 3.11/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_559,plain,
% 3.11/1.00      ( v1_relat_1(sK0) = iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_18,negated_conjecture,
% 3.11/1.00      ( v1_funct_1(sK0) ),
% 3.11/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_560,plain,
% 3.11/1.00      ( v1_funct_1(sK0) = iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6,plain,
% 3.11/1.00      ( ~ v1_funct_1(X0)
% 3.11/1.00      | ~ v1_relat_1(X0)
% 3.11/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 3.11/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_564,plain,
% 3.11/1.00      ( v1_funct_1(X0) != iProver_top
% 3.11/1.00      | v1_relat_1(X0) != iProver_top
% 3.11/1.00      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_0,plain,
% 3.11/1.00      ( ~ v1_relat_1(X0)
% 3.11/1.00      | ~ v1_relat_1(X1)
% 3.11/1.00      | ~ v1_relat_1(X2)
% 3.11/1.00      | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
% 3.11/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_568,plain,
% 3.11/1.00      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 3.11/1.00      | v1_relat_1(X2) != iProver_top
% 3.11/1.00      | v1_relat_1(X1) != iProver_top
% 3.11/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_1524,plain,
% 3.11/1.00      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 3.11/1.00      | v1_funct_1(X0) != iProver_top
% 3.11/1.00      | v1_relat_1(X0) != iProver_top
% 3.11/1.00      | v1_relat_1(X1) != iProver_top
% 3.11/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_564,c_568]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_5188,plain,
% 3.11/1.00      ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0),X1)
% 3.11/1.00      | v1_relat_1(X0) != iProver_top
% 3.11/1.00      | v1_relat_1(X1) != iProver_top
% 3.11/1.00      | v1_relat_1(sK0) != iProver_top ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_560,c_1524]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_20,plain,
% 3.11/1.00      ( v1_relat_1(sK0) = iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6483,plain,
% 3.11/1.00      ( v1_relat_1(X1) != iProver_top
% 3.11/1.00      | v1_relat_1(X0) != iProver_top
% 3.11/1.00      | k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0),X1) ),
% 3.11/1.00      inference(global_propositional_subsumption,
% 3.11/1.00                [status(thm)],
% 3.11/1.00                [c_5188,c_20]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6484,plain,
% 3.11/1.00      ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK0),X0),X1)
% 3.11/1.00      | v1_relat_1(X0) != iProver_top
% 3.11/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.11/1.00      inference(renaming,[status(thm)],[c_6483]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6492,plain,
% 3.11/1.00      ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK0),sK0),X0)
% 3.11/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_559,c_6484]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_10,plain,
% 3.11/1.00      ( ~ v2_funct_1(X0)
% 3.11/1.00      | ~ v1_funct_1(X0)
% 3.11/1.00      | ~ v1_relat_1(X0)
% 3.11/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
% 3.11/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_15,negated_conjecture,
% 3.11/1.00      ( v2_funct_1(sK0) ),
% 3.11/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_221,plain,
% 3.11/1.00      ( ~ v1_funct_1(X0)
% 3.11/1.00      | ~ v1_relat_1(X0)
% 3.11/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
% 3.11/1.00      | sK0 != X0 ),
% 3.11/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_222,plain,
% 3.11/1.00      ( ~ v1_funct_1(sK0)
% 3.11/1.00      | ~ v1_relat_1(sK0)
% 3.11/1.00      | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 3.11/1.00      inference(unflattening,[status(thm)],[c_221]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_29,plain,
% 3.11/1.00      ( ~ v2_funct_1(sK0)
% 3.11/1.00      | ~ v1_funct_1(sK0)
% 3.11/1.00      | ~ v1_relat_1(sK0)
% 3.11/1.00      | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 3.11/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_224,plain,
% 3.11/1.00      ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
% 3.11/1.00      inference(global_propositional_subsumption,
% 3.11/1.00                [status(thm)],
% 3.11/1.00                [c_222,c_19,c_18,c_15,c_29]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6495,plain,
% 3.11/1.00      ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,X0)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X0)
% 3.11/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.11/1.00      inference(light_normalisation,[status(thm)],[c_6492,c_224]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6523,plain,
% 3.11/1.00      ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_561,c_6495]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_13,negated_conjecture,
% 3.11/1.00      ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
% 3.11/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_4,plain,
% 3.11/1.00      ( ~ v1_relat_1(X0)
% 3.11/1.00      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 3.11/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_566,plain,
% 3.11/1.00      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 3.11/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_893,plain,
% 3.11/1.00      ( k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) = sK0 ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_559,c_566]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_7,plain,
% 3.11/1.00      ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 3.11/1.00      | ~ v1_funct_1(X1)
% 3.11/1.00      | ~ v1_funct_1(X0)
% 3.11/1.00      | ~ v1_relat_1(X0)
% 3.11/1.00      | ~ v1_relat_1(X1)
% 3.11/1.00      | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
% 3.11/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_563,plain,
% 3.11/1.00      ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
% 3.11/1.00      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 3.11/1.00      | v1_funct_1(X0) != iProver_top
% 3.11/1.00      | v1_funct_1(X1) != iProver_top
% 3.11/1.00      | v1_relat_1(X0) != iProver_top
% 3.11/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_1293,plain,
% 3.11/1.00      ( r1_tarski(k2_relat_1(sK0),k1_relat_1(k6_relat_1(k2_relat_1(sK0)))) = iProver_top
% 3.11/1.00      | v1_funct_1(k6_relat_1(k2_relat_1(sK0))) != iProver_top
% 3.11/1.00      | v1_funct_1(sK0) != iProver_top
% 3.11/1.00      | v1_relat_1(k6_relat_1(k2_relat_1(sK0))) != iProver_top
% 3.11/1.00      | v1_relat_1(sK0) != iProver_top ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_893,c_563]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2,plain,
% 3.11/1.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.11/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_1311,plain,
% 3.11/1.00      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top
% 3.11/1.00      | v1_funct_1(k6_relat_1(k2_relat_1(sK0))) != iProver_top
% 3.11/1.00      | v1_funct_1(sK0) != iProver_top
% 3.11/1.00      | v1_relat_1(k6_relat_1(k2_relat_1(sK0))) != iProver_top
% 3.11/1.00      | v1_relat_1(sK0) != iProver_top ),
% 3.11/1.00      inference(demodulation,[status(thm)],[c_1293,c_2]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_21,plain,
% 3.11/1.00      ( v1_funct_1(sK0) = iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_40,plain,
% 3.11/1.00      ( v1_funct_1(X0) != iProver_top
% 3.11/1.00      | v1_relat_1(X0) != iProver_top
% 3.11/1.00      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_42,plain,
% 3.11/1.00      ( v1_funct_1(sK0) != iProver_top
% 3.11/1.00      | v1_relat_1(k2_funct_1(sK0)) = iProver_top
% 3.11/1.00      | v1_relat_1(sK0) != iProver_top ),
% 3.11/1.00      inference(instantiation,[status(thm)],[c_40]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_5,plain,
% 3.11/1.00      ( ~ v1_funct_1(X0)
% 3.11/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.11/1.00      | ~ v1_relat_1(X0) ),
% 3.11/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_43,plain,
% 3.11/1.00      ( v1_funct_1(X0) != iProver_top
% 3.11/1.00      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.11/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_45,plain,
% 3.11/1.00      ( v1_funct_1(k2_funct_1(sK0)) = iProver_top
% 3.11/1.00      | v1_funct_1(sK0) != iProver_top
% 3.11/1.00      | v1_relat_1(sK0) != iProver_top ),
% 3.11/1.00      inference(instantiation,[status(thm)],[c_43]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_11,plain,
% 3.11/1.00      ( ~ v2_funct_1(X0)
% 3.11/1.00      | ~ v1_funct_1(X0)
% 3.11/1.00      | ~ v1_relat_1(X0)
% 3.11/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 3.11/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_213,plain,
% 3.11/1.00      ( ~ v1_funct_1(X0)
% 3.11/1.00      | ~ v1_relat_1(X0)
% 3.11/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
% 3.11/1.00      | sK0 != X0 ),
% 3.11/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_214,plain,
% 3.11/1.00      ( ~ v1_funct_1(sK0)
% 3.11/1.00      | ~ v1_relat_1(sK0)
% 3.11/1.00      | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
% 3.11/1.00      inference(unflattening,[status(thm)],[c_213]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_26,plain,
% 3.11/1.00      ( ~ v2_funct_1(sK0)
% 3.11/1.00      | ~ v1_funct_1(sK0)
% 3.11/1.00      | ~ v1_relat_1(sK0)
% 3.11/1.00      | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
% 3.11/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_216,plain,
% 3.11/1.00      ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
% 3.11/1.00      inference(global_propositional_subsumption,
% 3.11/1.00                [status(thm)],
% 3.11/1.00                [c_214,c_19,c_18,c_15,c_26]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_1291,plain,
% 3.11/1.00      ( k1_relat_1(k6_relat_1(k1_relat_1(sK0))) != k1_relat_1(sK0)
% 3.11/1.00      | r1_tarski(k2_relat_1(sK0),k1_relat_1(k2_funct_1(sK0))) = iProver_top
% 3.11/1.00      | v1_funct_1(k2_funct_1(sK0)) != iProver_top
% 3.11/1.00      | v1_funct_1(sK0) != iProver_top
% 3.11/1.00      | v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 3.11/1.00      | v1_relat_1(sK0) != iProver_top ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_216,c_563]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_9,plain,
% 3.11/1.00      ( ~ v2_funct_1(X0)
% 3.11/1.00      | ~ v1_funct_1(X0)
% 3.11/1.00      | ~ v1_relat_1(X0)
% 3.11/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.11/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_229,plain,
% 3.11/1.00      ( ~ v1_funct_1(X0)
% 3.11/1.00      | ~ v1_relat_1(X0)
% 3.11/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.11/1.00      | sK0 != X0 ),
% 3.11/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_230,plain,
% 3.11/1.00      ( ~ v1_funct_1(sK0)
% 3.11/1.00      | ~ v1_relat_1(sK0)
% 3.11/1.00      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 3.11/1.00      inference(unflattening,[status(thm)],[c_229]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_32,plain,
% 3.11/1.00      ( ~ v2_funct_1(sK0)
% 3.11/1.00      | ~ v1_funct_1(sK0)
% 3.11/1.00      | ~ v1_relat_1(sK0)
% 3.11/1.00      | k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 3.11/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_232,plain,
% 3.11/1.00      ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
% 3.11/1.00      inference(global_propositional_subsumption,
% 3.11/1.00                [status(thm)],
% 3.11/1.00                [c_230,c_19,c_18,c_15,c_32]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_1337,plain,
% 3.11/1.00      ( k1_relat_1(k6_relat_1(k1_relat_1(sK0))) != k1_relat_1(sK0)
% 3.11/1.00      | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top
% 3.11/1.00      | v1_funct_1(k2_funct_1(sK0)) != iProver_top
% 3.11/1.00      | v1_funct_1(sK0) != iProver_top
% 3.11/1.00      | v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 3.11/1.00      | v1_relat_1(sK0) != iProver_top ),
% 3.11/1.00      inference(light_normalisation,[status(thm)],[c_1291,c_232]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_1338,plain,
% 3.11/1.00      ( k1_relat_1(sK0) != k1_relat_1(sK0)
% 3.11/1.00      | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top
% 3.11/1.00      | v1_funct_1(k2_funct_1(sK0)) != iProver_top
% 3.11/1.00      | v1_funct_1(sK0) != iProver_top
% 3.11/1.00      | v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 3.11/1.00      | v1_relat_1(sK0) != iProver_top ),
% 3.11/1.00      inference(demodulation,[status(thm)],[c_1337,c_2]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_1339,plain,
% 3.11/1.00      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top
% 3.11/1.00      | v1_funct_1(k2_funct_1(sK0)) != iProver_top
% 3.11/1.00      | v1_funct_1(sK0) != iProver_top
% 3.11/1.00      | v1_relat_1(k2_funct_1(sK0)) != iProver_top
% 3.11/1.00      | v1_relat_1(sK0) != iProver_top ),
% 3.11/1.00      inference(equality_resolution_simp,[status(thm)],[c_1338]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_1630,plain,
% 3.11/1.00      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top ),
% 3.11/1.00      inference(global_propositional_subsumption,
% 3.11/1.00                [status(thm)],
% 3.11/1.00                [c_1311,c_20,c_21,c_42,c_45,c_1339]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_14,negated_conjecture,
% 3.11/1.00      ( k1_relat_1(sK1) = k2_relat_1(sK0) ),
% 3.11/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_3,plain,
% 3.11/1.00      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.11/1.00      | ~ v1_relat_1(X0)
% 3.11/1.00      | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
% 3.11/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_567,plain,
% 3.11/1.00      ( k5_relat_1(k6_relat_1(X0),X1) = X1
% 3.11/1.00      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 3.11/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_1153,plain,
% 3.11/1.00      ( k5_relat_1(k6_relat_1(X0),sK1) = sK1
% 3.11/1.00      | r1_tarski(k2_relat_1(sK0),X0) != iProver_top
% 3.11/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_14,c_567]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_22,plain,
% 3.11/1.00      ( v1_relat_1(sK1) = iProver_top ),
% 3.11/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_1183,plain,
% 3.11/1.00      ( r1_tarski(k2_relat_1(sK0),X0) != iProver_top
% 3.11/1.00      | k5_relat_1(k6_relat_1(X0),sK1) = sK1 ),
% 3.11/1.00      inference(global_propositional_subsumption,
% 3.11/1.00                [status(thm)],
% 3.11/1.00                [c_1153,c_22]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_1184,plain,
% 3.11/1.00      ( k5_relat_1(k6_relat_1(X0),sK1) = sK1
% 3.11/1.00      | r1_tarski(k2_relat_1(sK0),X0) != iProver_top ),
% 3.11/1.00      inference(renaming,[status(thm)],[c_1183]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_1637,plain,
% 3.11/1.00      ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),sK1) = sK1 ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_1630,c_1184]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_978,plain,
% 3.11/1.00      ( k5_relat_1(k2_funct_1(X0),k6_relat_1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
% 3.11/1.00      | v1_funct_1(X0) != iProver_top
% 3.11/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_564,c_566]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2202,plain,
% 3.11/1.00      ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) = k2_funct_1(sK0)
% 3.11/1.00      | v1_relat_1(sK0) != iProver_top ),
% 3.11/1.00      inference(superposition,[status(thm)],[c_560,c_978]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_8,plain,
% 3.11/1.00      ( ~ v2_funct_1(X0)
% 3.11/1.00      | ~ v1_funct_1(X0)
% 3.11/1.00      | ~ v1_relat_1(X0)
% 3.11/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.11/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_237,plain,
% 3.11/1.00      ( ~ v1_funct_1(X0)
% 3.11/1.00      | ~ v1_relat_1(X0)
% 3.11/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.11/1.00      | sK0 != X0 ),
% 3.11/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_15]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_238,plain,
% 3.11/1.00      ( ~ v1_funct_1(sK0)
% 3.11/1.00      | ~ v1_relat_1(sK0)
% 3.11/1.00      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 3.11/1.00      inference(unflattening,[status(thm)],[c_237]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_35,plain,
% 3.11/1.00      ( ~ v2_funct_1(sK0)
% 3.11/1.00      | ~ v1_funct_1(sK0)
% 3.11/1.00      | ~ v1_relat_1(sK0)
% 3.11/1.00      | k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 3.11/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_240,plain,
% 3.11/1.00      ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
% 3.11/1.00      inference(global_propositional_subsumption,
% 3.11/1.00                [status(thm)],
% 3.11/1.00                [c_238,c_19,c_18,c_15,c_35]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2205,plain,
% 3.11/1.00      ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k2_funct_1(sK0)
% 3.11/1.00      | v1_relat_1(sK0) != iProver_top ),
% 3.11/1.00      inference(light_normalisation,[status(thm)],[c_2202,c_240]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_2509,plain,
% 3.11/1.00      ( k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k2_funct_1(sK0) ),
% 3.11/1.00      inference(global_propositional_subsumption,
% 3.11/1.00                [status(thm)],
% 3.11/1.00                [c_2205,c_20]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_6528,plain,
% 3.11/1.00      ( k2_funct_1(sK0) = sK1 ),
% 3.11/1.00      inference(light_normalisation,
% 3.11/1.00                [status(thm)],
% 3.11/1.00                [c_6523,c_13,c_1637,c_2509]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(c_12,negated_conjecture,
% 3.11/1.00      ( k2_funct_1(sK0) != sK1 ),
% 3.11/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.11/1.00  
% 3.11/1.00  cnf(contradiction,plain,
% 3.11/1.00      ( $false ),
% 3.11/1.00      inference(minisat,[status(thm)],[c_6528,c_12]) ).
% 3.11/1.00  
% 3.11/1.00  
% 3.11/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.11/1.00  
% 3.11/1.00  ------                               Statistics
% 3.11/1.00  
% 3.11/1.00  ------ General
% 3.11/1.00  
% 3.11/1.00  abstr_ref_over_cycles:                  0
% 3.11/1.00  abstr_ref_under_cycles:                 0
% 3.11/1.00  gc_basic_clause_elim:                   0
% 3.11/1.00  forced_gc_time:                         0
% 3.11/1.00  parsing_time:                           0.009
% 3.11/1.00  unif_index_cands_time:                  0.
% 3.11/1.00  unif_index_add_time:                    0.
% 3.11/1.00  orderings_time:                         0.
% 3.11/1.00  out_proof_time:                         0.009
% 3.11/1.00  total_time:                             0.211
% 3.11/1.00  num_of_symbols:                         42
% 3.11/1.00  num_of_terms:                           5874
% 3.11/1.00  
% 3.11/1.00  ------ Preprocessing
% 3.11/1.00  
% 3.11/1.00  num_of_splits:                          0
% 3.11/1.00  num_of_split_atoms:                     0
% 3.11/1.00  num_of_reused_defs:                     0
% 3.11/1.00  num_eq_ax_congr_red:                    0
% 3.11/1.00  num_of_sem_filtered_clauses:            1
% 3.11/1.00  num_of_subtypes:                        0
% 3.11/1.00  monotx_restored_types:                  0
% 3.11/1.00  sat_num_of_epr_types:                   0
% 3.11/1.00  sat_num_of_non_cyclic_types:            0
% 3.11/1.00  sat_guarded_non_collapsed_types:        0
% 3.11/1.00  num_pure_diseq_elim:                    0
% 3.11/1.00  simp_replaced_by:                       0
% 3.11/1.00  res_preprocessed:                       98
% 3.11/1.00  prep_upred:                             0
% 3.11/1.00  prep_unflattend:                        6
% 3.11/1.00  smt_new_axioms:                         0
% 3.11/1.00  pred_elim_cands:                        3
% 3.11/1.00  pred_elim:                              1
% 3.11/1.00  pred_elim_cl:                           1
% 3.11/1.00  pred_elim_cycles:                       4
% 3.11/1.00  merged_defs:                            0
% 3.11/1.00  merged_defs_ncl:                        0
% 3.11/1.00  bin_hyper_res:                          0
% 3.11/1.00  prep_cycles:                            4
% 3.11/1.00  pred_elim_time:                         0.003
% 3.11/1.00  splitting_time:                         0.
% 3.11/1.00  sem_filter_time:                        0.
% 3.11/1.00  monotx_time:                            0.
% 3.11/1.00  subtype_inf_time:                       0.
% 3.11/1.00  
% 3.11/1.00  ------ Problem properties
% 3.11/1.00  
% 3.11/1.00  clauses:                                19
% 3.11/1.00  conjectures:                            7
% 3.11/1.00  epr:                                    4
% 3.11/1.00  horn:                                   19
% 3.11/1.00  ground:                                 11
% 3.11/1.00  unary:                                  13
% 3.11/1.00  binary:                                 1
% 3.11/1.00  lits:                                   34
% 3.11/1.00  lits_eq:                                13
% 3.11/1.00  fd_pure:                                0
% 3.11/1.00  fd_pseudo:                              0
% 3.11/1.00  fd_cond:                                0
% 3.11/1.00  fd_pseudo_cond:                         0
% 3.11/1.00  ac_symbols:                             0
% 3.11/1.00  
% 3.11/1.00  ------ Propositional Solver
% 3.11/1.00  
% 3.11/1.00  prop_solver_calls:                      28
% 3.11/1.00  prop_fast_solver_calls:                 783
% 3.11/1.00  smt_solver_calls:                       0
% 3.11/1.00  smt_fast_solver_calls:                  0
% 3.11/1.00  prop_num_of_clauses:                    2119
% 3.11/1.00  prop_preprocess_simplified:             6081
% 3.11/1.00  prop_fo_subsumed:                       68
% 3.11/1.00  prop_solver_time:                       0.
% 3.11/1.00  smt_solver_time:                        0.
% 3.11/1.00  smt_fast_solver_time:                   0.
% 3.11/1.00  prop_fast_solver_time:                  0.
% 3.11/1.00  prop_unsat_core_time:                   0.
% 3.11/1.00  
% 3.11/1.00  ------ QBF
% 3.11/1.00  
% 3.11/1.00  qbf_q_res:                              0
% 3.11/1.00  qbf_num_tautologies:                    0
% 3.11/1.00  qbf_prep_cycles:                        0
% 3.11/1.00  
% 3.11/1.00  ------ BMC1
% 3.11/1.00  
% 3.11/1.00  bmc1_current_bound:                     -1
% 3.11/1.00  bmc1_last_solved_bound:                 -1
% 3.11/1.00  bmc1_unsat_core_size:                   -1
% 3.11/1.00  bmc1_unsat_core_parents_size:           -1
% 3.11/1.00  bmc1_merge_next_fun:                    0
% 3.11/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.11/1.00  
% 3.11/1.00  ------ Instantiation
% 3.11/1.00  
% 3.11/1.00  inst_num_of_clauses:                    1208
% 3.11/1.00  inst_num_in_passive:                    550
% 3.11/1.00  inst_num_in_active:                     501
% 3.11/1.00  inst_num_in_unprocessed:                162
% 3.11/1.00  inst_num_of_loops:                      510
% 3.11/1.00  inst_num_of_learning_restarts:          0
% 3.11/1.00  inst_num_moves_active_passive:          7
% 3.11/1.00  inst_lit_activity:                      0
% 3.11/1.00  inst_lit_activity_moves:                0
% 3.11/1.00  inst_num_tautologies:                   0
% 3.11/1.00  inst_num_prop_implied:                  0
% 3.11/1.00  inst_num_existing_simplified:           0
% 3.11/1.00  inst_num_eq_res_simplified:             0
% 3.11/1.00  inst_num_child_elim:                    0
% 3.11/1.00  inst_num_of_dismatching_blockings:      924
% 3.11/1.00  inst_num_of_non_proper_insts:           1503
% 3.11/1.00  inst_num_of_duplicates:                 0
% 3.11/1.00  inst_inst_num_from_inst_to_res:         0
% 3.11/1.00  inst_dismatching_checking_time:         0.
% 3.11/1.00  
% 3.11/1.00  ------ Resolution
% 3.11/1.00  
% 3.11/1.00  res_num_of_clauses:                     0
% 3.11/1.00  res_num_in_passive:                     0
% 3.11/1.00  res_num_in_active:                      0
% 3.11/1.00  res_num_of_loops:                       102
% 3.11/1.00  res_forward_subset_subsumed:            155
% 3.11/1.00  res_backward_subset_subsumed:           10
% 3.11/1.00  res_forward_subsumed:                   0
% 3.11/1.00  res_backward_subsumed:                  0
% 3.11/1.00  res_forward_subsumption_resolution:     0
% 3.11/1.00  res_backward_subsumption_resolution:    0
% 3.11/1.00  res_clause_to_clause_subsumption:       333
% 3.11/1.00  res_orphan_elimination:                 0
% 3.11/1.00  res_tautology_del:                      236
% 3.11/1.00  res_num_eq_res_simplified:              0
% 3.11/1.00  res_num_sel_changes:                    0
% 3.11/1.00  res_moves_from_active_to_pass:          0
% 3.11/1.00  
% 3.11/1.00  ------ Superposition
% 3.11/1.00  
% 3.11/1.00  sup_time_total:                         0.
% 3.11/1.00  sup_time_generating:                    0.
% 3.11/1.00  sup_time_sim_full:                      0.
% 3.11/1.00  sup_time_sim_immed:                     0.
% 3.11/1.00  
% 3.11/1.00  sup_num_of_clauses:                     134
% 3.11/1.00  sup_num_in_active:                      101
% 3.11/1.00  sup_num_in_passive:                     33
% 3.11/1.00  sup_num_of_loops:                       101
% 3.11/1.00  sup_fw_superposition:                   82
% 3.11/1.00  sup_bw_superposition:                   44
% 3.11/1.00  sup_immediate_simplified:               37
% 3.11/1.00  sup_given_eliminated:                   1
% 3.11/1.00  comparisons_done:                       0
% 3.11/1.00  comparisons_avoided:                    0
% 3.11/1.00  
% 3.11/1.00  ------ Simplifications
% 3.11/1.00  
% 3.11/1.00  
% 3.11/1.00  sim_fw_subset_subsumed:                 0
% 3.11/1.00  sim_bw_subset_subsumed:                 3
% 3.11/1.00  sim_fw_subsumed:                        5
% 3.11/1.00  sim_bw_subsumed:                        0
% 3.11/1.00  sim_fw_subsumption_res:                 0
% 3.11/1.00  sim_bw_subsumption_res:                 0
% 3.11/1.00  sim_tautology_del:                      0
% 3.11/1.00  sim_eq_tautology_del:                   0
% 3.11/1.00  sim_eq_res_simp:                        6
% 3.11/1.00  sim_fw_demodulated:                     15
% 3.11/1.00  sim_bw_demodulated:                     3
% 3.11/1.00  sim_light_normalised:                   31
% 3.11/1.00  sim_joinable_taut:                      0
% 3.11/1.00  sim_joinable_simp:                      0
% 3.11/1.00  sim_ac_normalised:                      0
% 3.11/1.00  sim_smt_subsumption:                    0
% 3.11/1.00  
%------------------------------------------------------------------------------
