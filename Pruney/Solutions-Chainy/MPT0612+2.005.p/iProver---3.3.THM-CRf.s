%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:57 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 121 expanded)
%              Number of clauses        :   40 (  44 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :   15
%              Number of atoms          :  190 ( 282 expanded)
%              Number of equality atoms :   79 ( 111 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f31])).

fof(f47,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k6_subset_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f29])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f44,f43])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_384,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_390,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(X0,k7_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_386,plain,
    ( k7_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(X0,k7_relat_1(X0,X2))
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_686,plain,
    ( k7_relat_1(X0,k6_subset_1(k2_xboole_0(k1_relat_1(X0),X1),X2)) = k6_subset_1(X0,k7_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_390,c_386])).

cnf(c_2154,plain,
    ( k7_relat_1(sK4,k6_subset_1(k2_xboole_0(k1_relat_1(sK4),X0),X1)) = k6_subset_1(sK4,k7_relat_1(sK4,X1)) ),
    inference(superposition,[status(thm)],[c_384,c_686])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_385,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k6_subset_1(X1,X2))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_389,plain,
    ( r1_xboole_0(X0,k6_subset_1(X1,X2)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_395,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_393,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_977,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_395,c_393])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_391,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_996,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_977,c_391])).

cnf(c_1073,plain,
    ( k1_setfam_1(k2_tarski(X0,k6_subset_1(X1,X2))) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_389,c_996])).

cnf(c_1186,plain,
    ( k1_setfam_1(k2_tarski(sK2,k6_subset_1(X0,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_385,c_1073])).

cnf(c_8,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_388,plain,
    ( k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1333,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(X0,X1))) = k7_relat_1(k7_relat_1(sK4,X0),X1) ),
    inference(superposition,[status(thm)],[c_384,c_388])).

cnf(c_1799,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(X0,X1))) = k7_relat_1(k7_relat_1(sK4,X1),X0) ),
    inference(superposition,[status(thm)],[c_8,c_1333])).

cnf(c_1982,plain,
    ( k7_relat_1(k7_relat_1(sK4,k6_subset_1(X0,sK3)),sK2) = k7_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1186,c_1799])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_387,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_639,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_384,c_387])).

cnf(c_1992,plain,
    ( k7_relat_1(k7_relat_1(sK4,k6_subset_1(X0,sK3)),sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1982,c_639])).

cnf(c_2432,plain,
    ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2154,c_1992])).

cnf(c_134,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_513,plain,
    ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_514,plain,
    ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_133,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_150,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2432,c_514,c_150,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.26/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.01  
% 3.26/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.26/1.01  
% 3.26/1.01  ------  iProver source info
% 3.26/1.01  
% 3.26/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.26/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.26/1.01  git: non_committed_changes: false
% 3.26/1.01  git: last_make_outside_of_git: false
% 3.26/1.01  
% 3.26/1.01  ------ 
% 3.26/1.01  ------ Parsing...
% 3.26/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.26/1.01  
% 3.26/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.26/1.01  
% 3.26/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.26/1.01  
% 3.26/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.26/1.01  ------ Proving...
% 3.26/1.01  ------ Problem Properties 
% 3.26/1.01  
% 3.26/1.01  
% 3.26/1.01  clauses                                 15
% 3.26/1.01  conjectures                             3
% 3.26/1.01  EPR                                     4
% 3.26/1.01  Horn                                    13
% 3.26/1.01  unary                                   5
% 3.26/1.01  binary                                  8
% 3.26/1.01  lits                                    27
% 3.26/1.01  lits eq                                 6
% 3.26/1.01  fd_pure                                 0
% 3.26/1.01  fd_pseudo                               0
% 3.26/1.01  fd_cond                                 1
% 3.26/1.01  fd_pseudo_cond                          0
% 3.26/1.01  AC symbols                              0
% 3.26/1.01  
% 3.26/1.01  ------ Input Options Time Limit: Unbounded
% 3.26/1.01  
% 3.26/1.01  
% 3.26/1.01  ------ 
% 3.26/1.01  Current options:
% 3.26/1.01  ------ 
% 3.26/1.01  
% 3.26/1.01  
% 3.26/1.01  
% 3.26/1.01  
% 3.26/1.01  ------ Proving...
% 3.26/1.01  
% 3.26/1.01  
% 3.26/1.01  % SZS status Theorem for theBenchmark.p
% 3.26/1.01  
% 3.26/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.26/1.01  
% 3.26/1.01  fof(f12,conjecture,(
% 3.26/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 3.26/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.01  
% 3.26/1.01  fof(f13,negated_conjecture,(
% 3.26/1.01    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 3.26/1.01    inference(negated_conjecture,[],[f12])).
% 3.26/1.01  
% 3.26/1.01  fof(f23,plain,(
% 3.26/1.01    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 3.26/1.01    inference(ennf_transformation,[],[f13])).
% 3.26/1.01  
% 3.26/1.01  fof(f24,plain,(
% 3.26/1.01    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 3.26/1.01    inference(flattening,[],[f23])).
% 3.26/1.01  
% 3.26/1.01  fof(f31,plain,(
% 3.26/1.01    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) & r1_tarski(sK2,sK3) & v1_relat_1(sK4))),
% 3.26/1.01    introduced(choice_axiom,[])).
% 3.26/1.01  
% 3.26/1.01  fof(f32,plain,(
% 3.26/1.01    k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) & r1_tarski(sK2,sK3) & v1_relat_1(sK4)),
% 3.26/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f31])).
% 3.26/1.01  
% 3.26/1.01  fof(f47,plain,(
% 3.26/1.01    v1_relat_1(sK4)),
% 3.26/1.01    inference(cnf_transformation,[],[f32])).
% 3.26/1.01  
% 3.26/1.01  fof(f4,axiom,(
% 3.26/1.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.26/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.01  
% 3.26/1.01  fof(f39,plain,(
% 3.26/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.26/1.01    inference(cnf_transformation,[],[f4])).
% 3.26/1.01  
% 3.26/1.01  fof(f11,axiom,(
% 3.26/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 3.26/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.01  
% 3.26/1.01  fof(f21,plain,(
% 3.26/1.01    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 3.26/1.01    inference(ennf_transformation,[],[f11])).
% 3.26/1.01  
% 3.26/1.01  fof(f22,plain,(
% 3.26/1.01    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.26/1.01    inference(flattening,[],[f21])).
% 3.26/1.01  
% 3.26/1.01  fof(f46,plain,(
% 3.26/1.01    ( ! [X2,X0,X1] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.26/1.01    inference(cnf_transformation,[],[f22])).
% 3.26/1.01  
% 3.26/1.01  fof(f48,plain,(
% 3.26/1.01    r1_tarski(sK2,sK3)),
% 3.26/1.01    inference(cnf_transformation,[],[f32])).
% 3.26/1.01  
% 3.26/1.01  fof(f5,axiom,(
% 3.26/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 3.26/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.01  
% 3.26/1.01  fof(f18,plain,(
% 3.26/1.01    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.26/1.01    inference(ennf_transformation,[],[f5])).
% 3.26/1.01  
% 3.26/1.01  fof(f40,plain,(
% 3.26/1.01    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.26/1.01    inference(cnf_transformation,[],[f18])).
% 3.26/1.01  
% 3.26/1.01  fof(f7,axiom,(
% 3.26/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.26/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.01  
% 3.26/1.01  fof(f42,plain,(
% 3.26/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.26/1.01    inference(cnf_transformation,[],[f7])).
% 3.26/1.01  
% 3.26/1.01  fof(f52,plain,(
% 3.26/1.01    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k6_subset_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.26/1.01    inference(definition_unfolding,[],[f40,f42])).
% 3.26/1.01  
% 3.26/1.01  fof(f1,axiom,(
% 3.26/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.26/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.01  
% 3.26/1.01  fof(f15,plain,(
% 3.26/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.26/1.01    inference(ennf_transformation,[],[f1])).
% 3.26/1.01  
% 3.26/1.01  fof(f25,plain,(
% 3.26/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.26/1.01    inference(nnf_transformation,[],[f15])).
% 3.26/1.01  
% 3.26/1.01  fof(f26,plain,(
% 3.26/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.26/1.01    inference(rectify,[],[f25])).
% 3.26/1.01  
% 3.26/1.01  fof(f27,plain,(
% 3.26/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.26/1.01    introduced(choice_axiom,[])).
% 3.26/1.01  
% 3.26/1.01  fof(f28,plain,(
% 3.26/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.26/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.26/1.01  
% 3.26/1.01  fof(f34,plain,(
% 3.26/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.26/1.01    inference(cnf_transformation,[],[f28])).
% 3.26/1.01  
% 3.26/1.01  fof(f2,axiom,(
% 3.26/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.26/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.01  
% 3.26/1.01  fof(f14,plain,(
% 3.26/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.26/1.01    inference(rectify,[],[f2])).
% 3.26/1.01  
% 3.26/1.01  fof(f16,plain,(
% 3.26/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.26/1.01    inference(ennf_transformation,[],[f14])).
% 3.26/1.01  
% 3.26/1.01  fof(f29,plain,(
% 3.26/1.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.26/1.01    introduced(choice_axiom,[])).
% 3.26/1.01  
% 3.26/1.01  fof(f30,plain,(
% 3.26/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.26/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f29])).
% 3.26/1.01  
% 3.26/1.01  fof(f37,plain,(
% 3.26/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.26/1.01    inference(cnf_transformation,[],[f30])).
% 3.26/1.01  
% 3.26/1.01  fof(f8,axiom,(
% 3.26/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.26/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.01  
% 3.26/1.01  fof(f43,plain,(
% 3.26/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.26/1.01    inference(cnf_transformation,[],[f8])).
% 3.26/1.01  
% 3.26/1.01  fof(f50,plain,(
% 3.26/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 3.26/1.01    inference(definition_unfolding,[],[f37,f43])).
% 3.26/1.01  
% 3.26/1.01  fof(f3,axiom,(
% 3.26/1.01    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.26/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.01  
% 3.26/1.01  fof(f17,plain,(
% 3.26/1.01    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.26/1.01    inference(ennf_transformation,[],[f3])).
% 3.26/1.01  
% 3.26/1.01  fof(f38,plain,(
% 3.26/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.26/1.01    inference(cnf_transformation,[],[f17])).
% 3.26/1.01  
% 3.26/1.01  fof(f6,axiom,(
% 3.26/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.26/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.01  
% 3.26/1.01  fof(f41,plain,(
% 3.26/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.26/1.01    inference(cnf_transformation,[],[f6])).
% 3.26/1.01  
% 3.26/1.01  fof(f9,axiom,(
% 3.26/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 3.26/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.01  
% 3.26/1.01  fof(f19,plain,(
% 3.26/1.01    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.26/1.01    inference(ennf_transformation,[],[f9])).
% 3.26/1.01  
% 3.26/1.01  fof(f44,plain,(
% 3.26/1.01    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.26/1.01    inference(cnf_transformation,[],[f19])).
% 3.26/1.01  
% 3.26/1.01  fof(f53,plain,(
% 3.26/1.01    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X2)) )),
% 3.26/1.01    inference(definition_unfolding,[],[f44,f43])).
% 3.26/1.01  
% 3.26/1.01  fof(f10,axiom,(
% 3.26/1.01    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 3.26/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.01  
% 3.26/1.01  fof(f20,plain,(
% 3.26/1.01    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 3.26/1.01    inference(ennf_transformation,[],[f10])).
% 3.26/1.01  
% 3.26/1.01  fof(f45,plain,(
% 3.26/1.01    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 3.26/1.01    inference(cnf_transformation,[],[f20])).
% 3.26/1.01  
% 3.26/1.01  fof(f49,plain,(
% 3.26/1.01    k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2)),
% 3.26/1.01    inference(cnf_transformation,[],[f32])).
% 3.26/1.01  
% 3.26/1.01  cnf(c_14,negated_conjecture,
% 3.26/1.01      ( v1_relat_1(sK4) ),
% 3.26/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_384,plain,
% 3.26/1.01      ( v1_relat_1(sK4) = iProver_top ),
% 3.26/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_6,plain,
% 3.26/1.01      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.26/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_390,plain,
% 3.26/1.01      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.26/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_11,plain,
% 3.26/1.01      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.26/1.01      | ~ v1_relat_1(X0)
% 3.26/1.01      | k7_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(X0,k7_relat_1(X0,X2)) ),
% 3.26/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_386,plain,
% 3.26/1.01      ( k7_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(X0,k7_relat_1(X0,X2))
% 3.26/1.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.26/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.26/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_686,plain,
% 3.26/1.01      ( k7_relat_1(X0,k6_subset_1(k2_xboole_0(k1_relat_1(X0),X1),X2)) = k6_subset_1(X0,k7_relat_1(X0,X2))
% 3.26/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.26/1.01      inference(superposition,[status(thm)],[c_390,c_386]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_2154,plain,
% 3.26/1.01      ( k7_relat_1(sK4,k6_subset_1(k2_xboole_0(k1_relat_1(sK4),X0),X1)) = k6_subset_1(sK4,k7_relat_1(sK4,X1)) ),
% 3.26/1.01      inference(superposition,[status(thm)],[c_384,c_686]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_13,negated_conjecture,
% 3.26/1.01      ( r1_tarski(sK2,sK3) ),
% 3.26/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_385,plain,
% 3.26/1.01      ( r1_tarski(sK2,sK3) = iProver_top ),
% 3.26/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_7,plain,
% 3.26/1.01      ( r1_xboole_0(X0,k6_subset_1(X1,X2)) | ~ r1_tarski(X0,X2) ),
% 3.26/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_389,plain,
% 3.26/1.01      ( r1_xboole_0(X0,k6_subset_1(X1,X2)) = iProver_top
% 3.26/1.01      | r1_tarski(X0,X2) != iProver_top ),
% 3.26/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_1,plain,
% 3.26/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.26/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_395,plain,
% 3.26/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.26/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.26/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_3,plain,
% 3.26/1.01      ( ~ r1_xboole_0(X0,X1)
% 3.26/1.01      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ),
% 3.26/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_393,plain,
% 3.26/1.01      ( r1_xboole_0(X0,X1) != iProver_top
% 3.26/1.01      | r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) != iProver_top ),
% 3.26/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_977,plain,
% 3.26/1.01      ( r1_xboole_0(X0,X1) != iProver_top
% 3.26/1.01      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top ),
% 3.26/1.01      inference(superposition,[status(thm)],[c_395,c_393]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_5,plain,
% 3.26/1.01      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.26/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_391,plain,
% 3.26/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.26/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_996,plain,
% 3.26/1.01      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 3.26/1.01      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.26/1.01      inference(superposition,[status(thm)],[c_977,c_391]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_1073,plain,
% 3.26/1.01      ( k1_setfam_1(k2_tarski(X0,k6_subset_1(X1,X2))) = k1_xboole_0
% 3.26/1.01      | r1_tarski(X0,X2) != iProver_top ),
% 3.26/1.01      inference(superposition,[status(thm)],[c_389,c_996]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_1186,plain,
% 3.26/1.01      ( k1_setfam_1(k2_tarski(sK2,k6_subset_1(X0,sK3))) = k1_xboole_0 ),
% 3.26/1.01      inference(superposition,[status(thm)],[c_385,c_1073]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_8,plain,
% 3.26/1.01      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.26/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_9,plain,
% 3.26/1.01      ( ~ v1_relat_1(X0)
% 3.26/1.01      | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 3.26/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_388,plain,
% 3.26/1.01      ( k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 3.26/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.26/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_1333,plain,
% 3.26/1.01      ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(X0,X1))) = k7_relat_1(k7_relat_1(sK4,X0),X1) ),
% 3.26/1.01      inference(superposition,[status(thm)],[c_384,c_388]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_1799,plain,
% 3.26/1.01      ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(X0,X1))) = k7_relat_1(k7_relat_1(sK4,X1),X0) ),
% 3.26/1.01      inference(superposition,[status(thm)],[c_8,c_1333]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_1982,plain,
% 3.26/1.01      ( k7_relat_1(k7_relat_1(sK4,k6_subset_1(X0,sK3)),sK2) = k7_relat_1(sK4,k1_xboole_0) ),
% 3.26/1.01      inference(superposition,[status(thm)],[c_1186,c_1799]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_10,plain,
% 3.26/1.01      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.26/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_387,plain,
% 3.26/1.01      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 3.26/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.26/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_639,plain,
% 3.26/1.01      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 3.26/1.01      inference(superposition,[status(thm)],[c_384,c_387]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_1992,plain,
% 3.26/1.01      ( k7_relat_1(k7_relat_1(sK4,k6_subset_1(X0,sK3)),sK2) = k1_xboole_0 ),
% 3.26/1.01      inference(light_normalisation,[status(thm)],[c_1982,c_639]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_2432,plain,
% 3.26/1.01      ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) = k1_xboole_0 ),
% 3.26/1.01      inference(superposition,[status(thm)],[c_2154,c_1992]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_134,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_513,plain,
% 3.26/1.01      ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) != X0
% 3.26/1.01      | k1_xboole_0 != X0
% 3.26/1.01      | k1_xboole_0 = k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
% 3.26/1.01      inference(instantiation,[status(thm)],[c_134]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_514,plain,
% 3.26/1.01      ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) != k1_xboole_0
% 3.26/1.01      | k1_xboole_0 = k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2)
% 3.26/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.26/1.01      inference(instantiation,[status(thm)],[c_513]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_133,plain,( X0 = X0 ),theory(equality) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_150,plain,
% 3.26/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 3.26/1.01      inference(instantiation,[status(thm)],[c_133]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(c_12,negated_conjecture,
% 3.26/1.01      ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
% 3.26/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.26/1.01  
% 3.26/1.01  cnf(contradiction,plain,
% 3.26/1.01      ( $false ),
% 3.26/1.01      inference(minisat,[status(thm)],[c_2432,c_514,c_150,c_12]) ).
% 3.26/1.01  
% 3.26/1.01  
% 3.26/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.26/1.01  
% 3.26/1.01  ------                               Statistics
% 3.26/1.01  
% 3.26/1.01  ------ Selected
% 3.26/1.01  
% 3.26/1.01  total_time:                             0.124
% 3.26/1.01  
%------------------------------------------------------------------------------
