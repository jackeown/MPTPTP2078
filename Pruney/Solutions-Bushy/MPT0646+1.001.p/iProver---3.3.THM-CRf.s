%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0646+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:48 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   49 (  93 expanded)
%              Number of clauses        :   24 (  25 expanded)
%              Number of leaves         :    7 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  182 ( 472 expanded)
%              Number of equality atoms :   61 ( 117 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ? [X1] :
              ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & v1_funct_1(X1)
              & v1_relat_1(X1) )
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,sK1)
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ? [X1] :
            ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK0)
      & ? [X1] :
          ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ~ v2_funct_1(sK0)
    & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14,f13])).

fof(f26,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f27,plain,(
    ~ v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f23,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_7,negated_conjecture,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_2,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_3,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_105,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X1,X0))
    | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_2,c_3])).

cnf(c_367,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_105])).

cnf(c_667,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(sK0))) != k1_relat_1(sK0)
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v2_funct_1(k5_relat_1(sK0,sK1)) != iProver_top
    | v2_funct_1(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_367])).

cnf(c_668,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(sK0))) != k1_relat_1(sK0)
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v2_funct_1(k6_relat_1(k1_relat_1(sK0))) != iProver_top
    | v2_funct_1(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_667,c_7])).

cnf(c_5,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_669,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v2_funct_1(k6_relat_1(k1_relat_1(sK0))) != iProver_top
    | v2_funct_1(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_668,c_5])).

cnf(c_670,plain,
    ( v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK0) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v2_funct_1(k6_relat_1(k1_relat_1(sK0))) != iProver_top
    | v2_funct_1(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_669])).

cnf(c_0,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_544,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_545,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_6,negated_conjecture,
    ( ~ v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_16,plain,
    ( v2_funct_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_15,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_14,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_13,plain,
    ( v1_funct_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_12,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_670,c_545,c_16,c_15,c_14,c_13,c_12])).


%------------------------------------------------------------------------------
