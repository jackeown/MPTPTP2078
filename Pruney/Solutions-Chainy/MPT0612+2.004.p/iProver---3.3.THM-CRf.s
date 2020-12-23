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
% DateTime   : Thu Dec  3 11:48:57 EST 2020

% Result     : Theorem 54.63s
% Output     : CNFRefutation 54.63s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 241 expanded)
%              Number of clauses        :   68 (  98 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :  239 ( 506 expanded)
%              Number of equality atoms :  116 ( 230 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f34])).

fof(f54,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f63,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f48,f56])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f40,f49])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f50,f49])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_177,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_610,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_177])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_182,plain,
    ( k5_xboole_0(X0_44,k1_setfam_1(k2_tarski(X0_44,X1_44))) = k6_subset_1(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_9,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_184,plain,
    ( r1_xboole_0(k5_xboole_0(X0_44,k1_setfam_1(k2_tarski(X0_44,X1_44))),X1_44) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_606,plain,
    ( r1_xboole_0(k5_xboole_0(X0_44,k1_setfam_1(k2_tarski(X0_44,X1_44))),X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_184])).

cnf(c_623,plain,
    ( r1_xboole_0(k6_subset_1(X0_44,X1_44),X1_44) = iProver_top ),
    inference(demodulation,[status(thm)],[c_182,c_606])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_189,plain,
    ( ~ r1_xboole_0(X0_44,X1_44)
    | k1_setfam_1(k2_tarski(X0_44,X1_44)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_602,plain,
    ( k1_setfam_1(k2_tarski(X0_44,X1_44)) = k1_xboole_0
    | r1_xboole_0(X0_44,X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_189])).

cnf(c_1232,plain,
    ( k1_setfam_1(k2_tarski(k6_subset_1(X0_44,X1_44),X1_44)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_623,c_602])).

cnf(c_10,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_183,plain,
    ( k2_tarski(X0_44,X1_44) = k2_tarski(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_190,plain,
    ( r1_xboole_0(X0_44,X1_44)
    | k1_setfam_1(k2_tarski(X0_44,X1_44)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_601,plain,
    ( k1_setfam_1(k2_tarski(X0_44,X1_44)) != k1_xboole_0
    | r1_xboole_0(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_1041,plain,
    ( k1_setfam_1(k2_tarski(X0_44,X1_44)) != k1_xboole_0
    | r1_xboole_0(X1_44,X0_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_183,c_601])).

cnf(c_2179,plain,
    ( r1_xboole_0(X0_44,k6_subset_1(X1_44,X0_44)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_1041])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_185,plain,
    ( ~ r1_xboole_0(X0_44,X1_44)
    | r1_xboole_0(X2_44,X1_44)
    | ~ r1_tarski(X2_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_605,plain,
    ( r1_xboole_0(X0_44,X1_44) != iProver_top
    | r1_xboole_0(X2_44,X1_44) = iProver_top
    | r1_tarski(X2_44,X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_185])).

cnf(c_2520,plain,
    ( r1_xboole_0(X0_44,k6_subset_1(X1_44,X2_44)) = iProver_top
    | r1_tarski(X0_44,X2_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_2179,c_605])).

cnf(c_8827,plain,
    ( k1_setfam_1(k2_tarski(X0_44,k6_subset_1(X1_44,X2_44))) = k1_xboole_0
    | r1_tarski(X0_44,X2_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_2520,c_602])).

cnf(c_13482,plain,
    ( k1_setfam_1(k2_tarski(sK2,k6_subset_1(X0_44,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_610,c_8827])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_176,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_611,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_176])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_181,plain,
    ( ~ v1_relat_1(X0_44)
    | k7_relat_1(X0_44,k1_setfam_1(k2_tarski(X1_44,X2_44))) = k7_relat_1(k7_relat_1(X0_44,X1_44),X2_44) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_607,plain,
    ( k7_relat_1(X0_44,k1_setfam_1(k2_tarski(X1_44,X2_44))) = k7_relat_1(k7_relat_1(X0_44,X1_44),X2_44)
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_181])).

cnf(c_1797,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(X0_44,X1_44))) = k7_relat_1(k7_relat_1(sK4,X0_44),X1_44) ),
    inference(superposition,[status(thm)],[c_611,c_607])).

cnf(c_13764,plain,
    ( k7_relat_1(k7_relat_1(sK4,sK2),k6_subset_1(X0_44,sK3)) = k7_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_13482,c_1797])).

cnf(c_7,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_186,plain,
    ( k1_setfam_1(k2_tarski(X0_44,k1_xboole_0)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_746,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0_44)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_183,c_186])).

cnf(c_1040,plain,
    ( r1_xboole_0(k1_xboole_0,X0_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_746,c_601])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_180,plain,
    ( ~ r1_xboole_0(X0_44,k1_relat_1(X1_44))
    | ~ v1_relat_1(X1_44)
    | k7_relat_1(X1_44,X0_44) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_608,plain,
    ( k7_relat_1(X0_44,X1_44) = k1_xboole_0
    | r1_xboole_0(X1_44,k1_relat_1(X0_44)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_2032,plain,
    ( k7_relat_1(X0_44,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_608])).

cnf(c_4300,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_611,c_2032])).

cnf(c_13793,plain,
    ( k7_relat_1(k7_relat_1(sK4,sK2),k6_subset_1(X0_44,sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13764,c_4300])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_192,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X0_44)
    | r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_599,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X0_44) = iProver_top
    | r1_tarski(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_193,plain,
    ( ~ r2_hidden(sK0(X0_44,X1_44),X1_44)
    | r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_598,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X1_44) != iProver_top
    | r1_tarski(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_943,plain,
    ( r1_tarski(X0_44,X0_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_599,c_598])).

cnf(c_14,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(X0,k7_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_179,plain,
    ( ~ r1_tarski(k1_relat_1(X0_44),X1_44)
    | ~ v1_relat_1(X0_44)
    | k7_relat_1(X0_44,k6_subset_1(X1_44,X2_44)) = k6_subset_1(X0_44,k7_relat_1(X0_44,X2_44)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_609,plain,
    ( k7_relat_1(X0_44,k6_subset_1(X1_44,X2_44)) = k6_subset_1(X0_44,k7_relat_1(X0_44,X2_44))
    | r1_tarski(k1_relat_1(X0_44),X1_44) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_179])).

cnf(c_1909,plain,
    ( k7_relat_1(X0_44,k6_subset_1(k1_relat_1(X0_44),X1_44)) = k6_subset_1(X0_44,k7_relat_1(X0_44,X1_44))
    | v1_relat_1(X0_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_943,c_609])).

cnf(c_5687,plain,
    ( k7_relat_1(sK4,k6_subset_1(k1_relat_1(sK4),X0_44)) = k6_subset_1(sK4,k7_relat_1(sK4,X0_44)) ),
    inference(superposition,[status(thm)],[c_611,c_1909])).

cnf(c_4650,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(X0_44,X1_44))) = k7_relat_1(k7_relat_1(sK4,X1_44),X0_44) ),
    inference(superposition,[status(thm)],[c_183,c_1797])).

cnf(c_4713,plain,
    ( k7_relat_1(k7_relat_1(sK4,X0_44),X1_44) = k7_relat_1(k7_relat_1(sK4,X1_44),X0_44) ),
    inference(superposition,[status(thm)],[c_4650,c_1797])).

cnf(c_8236,plain,
    ( k7_relat_1(k7_relat_1(sK4,X0_44),k6_subset_1(k1_relat_1(sK4),X1_44)) = k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,X1_44)),X0_44) ),
    inference(superposition,[status(thm)],[c_5687,c_4713])).

cnf(c_235861,plain,
    ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13793,c_8236])).

cnf(c_198,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_743,plain,
    ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) != X0_44
    | k1_xboole_0 != X0_44
    | k1_xboole_0 = k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_198])).

cnf(c_744,plain,
    ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_178,negated_conjecture,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_195,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_219,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_235861,c_744,c_178,c_219])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 09:48:47 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.33  % Running in FOF mode
% 54.63/7.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 54.63/7.48  
% 54.63/7.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 54.63/7.48  
% 54.63/7.48  ------  iProver source info
% 54.63/7.48  
% 54.63/7.48  git: date: 2020-06-30 10:37:57 +0100
% 54.63/7.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 54.63/7.48  git: non_committed_changes: false
% 54.63/7.48  git: last_make_outside_of_git: false
% 54.63/7.48  
% 54.63/7.48  ------ 
% 54.63/7.48  
% 54.63/7.48  ------ Input Options
% 54.63/7.48  
% 54.63/7.48  --out_options                           all
% 54.63/7.48  --tptp_safe_out                         true
% 54.63/7.48  --problem_path                          ""
% 54.63/7.48  --include_path                          ""
% 54.63/7.48  --clausifier                            res/vclausify_rel
% 54.63/7.48  --clausifier_options                    --mode clausify
% 54.63/7.48  --stdin                                 false
% 54.63/7.48  --stats_out                             sel
% 54.63/7.48  
% 54.63/7.48  ------ General Options
% 54.63/7.48  
% 54.63/7.48  --fof                                   false
% 54.63/7.48  --time_out_real                         604.99
% 54.63/7.48  --time_out_virtual                      -1.
% 54.63/7.48  --symbol_type_check                     false
% 54.63/7.48  --clausify_out                          false
% 54.63/7.48  --sig_cnt_out                           false
% 54.63/7.48  --trig_cnt_out                          false
% 54.63/7.48  --trig_cnt_out_tolerance                1.
% 54.63/7.48  --trig_cnt_out_sk_spl                   false
% 54.63/7.48  --abstr_cl_out                          false
% 54.63/7.48  
% 54.63/7.48  ------ Global Options
% 54.63/7.48  
% 54.63/7.48  --schedule                              none
% 54.63/7.48  --add_important_lit                     false
% 54.63/7.48  --prop_solver_per_cl                    1000
% 54.63/7.48  --min_unsat_core                        false
% 54.63/7.48  --soft_assumptions                      false
% 54.63/7.48  --soft_lemma_size                       3
% 54.63/7.48  --prop_impl_unit_size                   0
% 54.63/7.48  --prop_impl_unit                        []
% 54.63/7.48  --share_sel_clauses                     true
% 54.63/7.48  --reset_solvers                         false
% 54.63/7.48  --bc_imp_inh                            [conj_cone]
% 54.63/7.48  --conj_cone_tolerance                   3.
% 54.63/7.48  --extra_neg_conj                        none
% 54.63/7.48  --large_theory_mode                     true
% 54.63/7.48  --prolific_symb_bound                   200
% 54.63/7.48  --lt_threshold                          2000
% 54.63/7.48  --clause_weak_htbl                      true
% 54.63/7.48  --gc_record_bc_elim                     false
% 54.63/7.48  
% 54.63/7.48  ------ Preprocessing Options
% 54.63/7.48  
% 54.63/7.48  --preprocessing_flag                    true
% 54.63/7.48  --time_out_prep_mult                    0.1
% 54.63/7.48  --splitting_mode                        input
% 54.63/7.48  --splitting_grd                         true
% 54.63/7.48  --splitting_cvd                         false
% 54.63/7.48  --splitting_cvd_svl                     false
% 54.63/7.48  --splitting_nvd                         32
% 54.63/7.48  --sub_typing                            true
% 54.63/7.48  --prep_gs_sim                           false
% 54.63/7.48  --prep_unflatten                        true
% 54.63/7.48  --prep_res_sim                          true
% 54.63/7.48  --prep_upred                            true
% 54.63/7.48  --prep_sem_filter                       exhaustive
% 54.63/7.48  --prep_sem_filter_out                   false
% 54.63/7.48  --pred_elim                             false
% 54.63/7.48  --res_sim_input                         true
% 54.63/7.48  --eq_ax_congr_red                       true
% 54.63/7.48  --pure_diseq_elim                       true
% 54.63/7.48  --brand_transform                       false
% 54.63/7.48  --non_eq_to_eq                          false
% 54.63/7.48  --prep_def_merge                        true
% 54.63/7.48  --prep_def_merge_prop_impl              false
% 54.63/7.48  --prep_def_merge_mbd                    true
% 54.63/7.48  --prep_def_merge_tr_red                 false
% 54.63/7.48  --prep_def_merge_tr_cl                  false
% 54.63/7.48  --smt_preprocessing                     true
% 54.63/7.48  --smt_ac_axioms                         fast
% 54.63/7.48  --preprocessed_out                      false
% 54.63/7.48  --preprocessed_stats                    false
% 54.63/7.48  
% 54.63/7.48  ------ Abstraction refinement Options
% 54.63/7.48  
% 54.63/7.48  --abstr_ref                             []
% 54.63/7.48  --abstr_ref_prep                        false
% 54.63/7.48  --abstr_ref_until_sat                   false
% 54.63/7.48  --abstr_ref_sig_restrict                funpre
% 54.63/7.48  --abstr_ref_af_restrict_to_split_sk     false
% 54.63/7.48  --abstr_ref_under                       []
% 54.63/7.48  
% 54.63/7.48  ------ SAT Options
% 54.63/7.48  
% 54.63/7.48  --sat_mode                              false
% 54.63/7.48  --sat_fm_restart_options                ""
% 54.63/7.48  --sat_gr_def                            false
% 54.63/7.48  --sat_epr_types                         true
% 54.63/7.48  --sat_non_cyclic_types                  false
% 54.63/7.48  --sat_finite_models                     false
% 54.63/7.48  --sat_fm_lemmas                         false
% 54.63/7.48  --sat_fm_prep                           false
% 54.63/7.48  --sat_fm_uc_incr                        true
% 54.63/7.48  --sat_out_model                         small
% 54.63/7.48  --sat_out_clauses                       false
% 54.63/7.48  
% 54.63/7.48  ------ QBF Options
% 54.63/7.48  
% 54.63/7.48  --qbf_mode                              false
% 54.63/7.48  --qbf_elim_univ                         false
% 54.63/7.48  --qbf_dom_inst                          none
% 54.63/7.48  --qbf_dom_pre_inst                      false
% 54.63/7.48  --qbf_sk_in                             false
% 54.63/7.48  --qbf_pred_elim                         true
% 54.63/7.48  --qbf_split                             512
% 54.63/7.48  
% 54.63/7.48  ------ BMC1 Options
% 54.63/7.48  
% 54.63/7.48  --bmc1_incremental                      false
% 54.63/7.48  --bmc1_axioms                           reachable_all
% 54.63/7.48  --bmc1_min_bound                        0
% 54.63/7.48  --bmc1_max_bound                        -1
% 54.63/7.48  --bmc1_max_bound_default                -1
% 54.63/7.48  --bmc1_symbol_reachability              true
% 54.63/7.48  --bmc1_property_lemmas                  false
% 54.63/7.48  --bmc1_k_induction                      false
% 54.63/7.48  --bmc1_non_equiv_states                 false
% 54.63/7.48  --bmc1_deadlock                         false
% 54.63/7.48  --bmc1_ucm                              false
% 54.63/7.48  --bmc1_add_unsat_core                   none
% 54.63/7.48  --bmc1_unsat_core_children              false
% 54.63/7.48  --bmc1_unsat_core_extrapolate_axioms    false
% 54.63/7.48  --bmc1_out_stat                         full
% 54.63/7.48  --bmc1_ground_init                      false
% 54.63/7.48  --bmc1_pre_inst_next_state              false
% 54.63/7.48  --bmc1_pre_inst_state                   false
% 54.63/7.48  --bmc1_pre_inst_reach_state             false
% 54.63/7.48  --bmc1_out_unsat_core                   false
% 54.63/7.48  --bmc1_aig_witness_out                  false
% 54.63/7.48  --bmc1_verbose                          false
% 54.63/7.48  --bmc1_dump_clauses_tptp                false
% 54.63/7.48  --bmc1_dump_unsat_core_tptp             false
% 54.63/7.48  --bmc1_dump_file                        -
% 54.63/7.48  --bmc1_ucm_expand_uc_limit              128
% 54.63/7.48  --bmc1_ucm_n_expand_iterations          6
% 54.63/7.48  --bmc1_ucm_extend_mode                  1
% 54.63/7.48  --bmc1_ucm_init_mode                    2
% 54.63/7.48  --bmc1_ucm_cone_mode                    none
% 54.63/7.48  --bmc1_ucm_reduced_relation_type        0
% 54.63/7.48  --bmc1_ucm_relax_model                  4
% 54.63/7.48  --bmc1_ucm_full_tr_after_sat            true
% 54.63/7.48  --bmc1_ucm_expand_neg_assumptions       false
% 54.63/7.48  --bmc1_ucm_layered_model                none
% 54.63/7.48  --bmc1_ucm_max_lemma_size               10
% 54.63/7.48  
% 54.63/7.48  ------ AIG Options
% 54.63/7.48  
% 54.63/7.48  --aig_mode                              false
% 54.63/7.48  
% 54.63/7.48  ------ Instantiation Options
% 54.63/7.48  
% 54.63/7.48  --instantiation_flag                    true
% 54.63/7.48  --inst_sos_flag                         false
% 54.63/7.48  --inst_sos_phase                        true
% 54.63/7.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 54.63/7.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 54.63/7.48  --inst_lit_sel_side                     num_symb
% 54.63/7.48  --inst_solver_per_active                1400
% 54.63/7.48  --inst_solver_calls_frac                1.
% 54.63/7.48  --inst_passive_queue_type               priority_queues
% 54.63/7.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 54.63/7.48  --inst_passive_queues_freq              [25;2]
% 54.63/7.48  --inst_dismatching                      true
% 54.63/7.48  --inst_eager_unprocessed_to_passive     true
% 54.63/7.48  --inst_prop_sim_given                   true
% 54.63/7.48  --inst_prop_sim_new                     false
% 54.63/7.48  --inst_subs_new                         false
% 54.63/7.48  --inst_eq_res_simp                      false
% 54.63/7.48  --inst_subs_given                       false
% 54.63/7.48  --inst_orphan_elimination               true
% 54.63/7.48  --inst_learning_loop_flag               true
% 54.63/7.48  --inst_learning_start                   3000
% 54.63/7.48  --inst_learning_factor                  2
% 54.63/7.48  --inst_start_prop_sim_after_learn       3
% 54.63/7.48  --inst_sel_renew                        solver
% 54.63/7.48  --inst_lit_activity_flag                true
% 54.63/7.48  --inst_restr_to_given                   false
% 54.63/7.48  --inst_activity_threshold               500
% 54.63/7.48  --inst_out_proof                        true
% 54.63/7.48  
% 54.63/7.48  ------ Resolution Options
% 54.63/7.48  
% 54.63/7.48  --resolution_flag                       true
% 54.63/7.48  --res_lit_sel                           adaptive
% 54.63/7.48  --res_lit_sel_side                      none
% 54.63/7.48  --res_ordering                          kbo
% 54.63/7.48  --res_to_prop_solver                    active
% 54.63/7.48  --res_prop_simpl_new                    false
% 54.63/7.48  --res_prop_simpl_given                  true
% 54.63/7.48  --res_passive_queue_type                priority_queues
% 54.63/7.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 54.63/7.48  --res_passive_queues_freq               [15;5]
% 54.63/7.48  --res_forward_subs                      full
% 54.63/7.48  --res_backward_subs                     full
% 54.63/7.48  --res_forward_subs_resolution           true
% 54.63/7.48  --res_backward_subs_resolution          true
% 54.63/7.48  --res_orphan_elimination                true
% 54.63/7.48  --res_time_limit                        2.
% 54.63/7.48  --res_out_proof                         true
% 54.63/7.48  
% 54.63/7.48  ------ Superposition Options
% 54.63/7.48  
% 54.63/7.48  --superposition_flag                    true
% 54.63/7.48  --sup_passive_queue_type                priority_queues
% 54.63/7.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 54.63/7.48  --sup_passive_queues_freq               [1;4]
% 54.63/7.48  --demod_completeness_check              fast
% 54.63/7.48  --demod_use_ground                      true
% 54.63/7.48  --sup_to_prop_solver                    passive
% 54.63/7.48  --sup_prop_simpl_new                    true
% 54.63/7.48  --sup_prop_simpl_given                  true
% 54.63/7.48  --sup_fun_splitting                     false
% 54.63/7.48  --sup_smt_interval                      50000
% 54.63/7.48  
% 54.63/7.48  ------ Superposition Simplification Setup
% 54.63/7.48  
% 54.63/7.48  --sup_indices_passive                   []
% 54.63/7.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.63/7.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.63/7.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.63/7.48  --sup_full_triv                         [TrivRules;PropSubs]
% 54.63/7.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.63/7.48  --sup_full_bw                           [BwDemod]
% 54.63/7.48  --sup_immed_triv                        [TrivRules]
% 54.63/7.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 54.63/7.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.63/7.48  --sup_immed_bw_main                     []
% 54.63/7.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 54.63/7.48  --sup_input_triv                        [Unflattening;TrivRules]
% 54.63/7.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.63/7.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 54.63/7.48  
% 54.63/7.48  ------ Combination Options
% 54.63/7.48  
% 54.63/7.48  --comb_res_mult                         3
% 54.63/7.48  --comb_sup_mult                         2
% 54.63/7.48  --comb_inst_mult                        10
% 54.63/7.48  
% 54.63/7.48  ------ Debug Options
% 54.63/7.48  
% 54.63/7.48  --dbg_backtrace                         false
% 54.63/7.48  --dbg_dump_prop_clauses                 false
% 54.63/7.48  --dbg_dump_prop_clauses_file            -
% 54.63/7.48  --dbg_out_stat                          false
% 54.63/7.48  ------ Parsing...
% 54.63/7.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 54.63/7.48  
% 54.63/7.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 54.63/7.48  
% 54.63/7.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 54.63/7.48  
% 54.63/7.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 54.63/7.48  ------ Proving...
% 54.63/7.48  ------ Problem Properties 
% 54.63/7.48  
% 54.63/7.48  
% 54.63/7.48  clauses                                 18
% 54.63/7.48  conjectures                             3
% 54.63/7.48  EPR                                     4
% 54.63/7.48  Horn                                    16
% 54.63/7.48  unary                                   7
% 54.63/7.48  binary                                  7
% 54.63/7.48  lits                                    33
% 54.63/7.48  lits eq                                 9
% 54.63/7.48  fd_pure                                 0
% 54.63/7.48  fd_pseudo                               0
% 54.63/7.48  fd_cond                                 0
% 54.63/7.48  fd_pseudo_cond                          0
% 54.63/7.48  AC symbols                              0
% 54.63/7.48  
% 54.63/7.48  ------ Input Options Time Limit: Unbounded
% 54.63/7.48  
% 54.63/7.48  
% 54.63/7.48  ------ 
% 54.63/7.48  Current options:
% 54.63/7.48  ------ 
% 54.63/7.48  
% 54.63/7.48  ------ Input Options
% 54.63/7.48  
% 54.63/7.48  --out_options                           all
% 54.63/7.48  --tptp_safe_out                         true
% 54.63/7.48  --problem_path                          ""
% 54.63/7.48  --include_path                          ""
% 54.63/7.48  --clausifier                            res/vclausify_rel
% 54.63/7.48  --clausifier_options                    --mode clausify
% 54.63/7.48  --stdin                                 false
% 54.63/7.48  --stats_out                             sel
% 54.63/7.48  
% 54.63/7.48  ------ General Options
% 54.63/7.48  
% 54.63/7.48  --fof                                   false
% 54.63/7.48  --time_out_real                         604.99
% 54.63/7.48  --time_out_virtual                      -1.
% 54.63/7.48  --symbol_type_check                     false
% 54.63/7.48  --clausify_out                          false
% 54.63/7.48  --sig_cnt_out                           false
% 54.63/7.48  --trig_cnt_out                          false
% 54.63/7.48  --trig_cnt_out_tolerance                1.
% 54.63/7.48  --trig_cnt_out_sk_spl                   false
% 54.63/7.48  --abstr_cl_out                          false
% 54.63/7.48  
% 54.63/7.48  ------ Global Options
% 54.63/7.48  
% 54.63/7.48  --schedule                              none
% 54.63/7.48  --add_important_lit                     false
% 54.63/7.48  --prop_solver_per_cl                    1000
% 54.63/7.48  --min_unsat_core                        false
% 54.63/7.48  --soft_assumptions                      false
% 54.63/7.48  --soft_lemma_size                       3
% 54.63/7.48  --prop_impl_unit_size                   0
% 54.63/7.48  --prop_impl_unit                        []
% 54.63/7.48  --share_sel_clauses                     true
% 54.63/7.48  --reset_solvers                         false
% 54.63/7.48  --bc_imp_inh                            [conj_cone]
% 54.63/7.48  --conj_cone_tolerance                   3.
% 54.63/7.48  --extra_neg_conj                        none
% 54.63/7.48  --large_theory_mode                     true
% 54.63/7.48  --prolific_symb_bound                   200
% 54.63/7.48  --lt_threshold                          2000
% 54.63/7.48  --clause_weak_htbl                      true
% 54.63/7.48  --gc_record_bc_elim                     false
% 54.63/7.48  
% 54.63/7.48  ------ Preprocessing Options
% 54.63/7.48  
% 54.63/7.48  --preprocessing_flag                    true
% 54.63/7.48  --time_out_prep_mult                    0.1
% 54.63/7.48  --splitting_mode                        input
% 54.63/7.48  --splitting_grd                         true
% 54.63/7.48  --splitting_cvd                         false
% 54.63/7.48  --splitting_cvd_svl                     false
% 54.63/7.48  --splitting_nvd                         32
% 54.63/7.48  --sub_typing                            true
% 54.63/7.48  --prep_gs_sim                           false
% 54.63/7.48  --prep_unflatten                        true
% 54.63/7.48  --prep_res_sim                          true
% 54.63/7.48  --prep_upred                            true
% 54.63/7.48  --prep_sem_filter                       exhaustive
% 54.63/7.48  --prep_sem_filter_out                   false
% 54.63/7.48  --pred_elim                             false
% 54.63/7.48  --res_sim_input                         true
% 54.63/7.48  --eq_ax_congr_red                       true
% 54.63/7.48  --pure_diseq_elim                       true
% 54.63/7.48  --brand_transform                       false
% 54.63/7.48  --non_eq_to_eq                          false
% 54.63/7.48  --prep_def_merge                        true
% 54.63/7.48  --prep_def_merge_prop_impl              false
% 54.63/7.48  --prep_def_merge_mbd                    true
% 54.63/7.48  --prep_def_merge_tr_red                 false
% 54.63/7.48  --prep_def_merge_tr_cl                  false
% 54.63/7.48  --smt_preprocessing                     true
% 54.63/7.48  --smt_ac_axioms                         fast
% 54.63/7.48  --preprocessed_out                      false
% 54.63/7.48  --preprocessed_stats                    false
% 54.63/7.48  
% 54.63/7.48  ------ Abstraction refinement Options
% 54.63/7.48  
% 54.63/7.48  --abstr_ref                             []
% 54.63/7.48  --abstr_ref_prep                        false
% 54.63/7.48  --abstr_ref_until_sat                   false
% 54.63/7.48  --abstr_ref_sig_restrict                funpre
% 54.63/7.48  --abstr_ref_af_restrict_to_split_sk     false
% 54.63/7.48  --abstr_ref_under                       []
% 54.63/7.48  
% 54.63/7.48  ------ SAT Options
% 54.63/7.48  
% 54.63/7.48  --sat_mode                              false
% 54.63/7.48  --sat_fm_restart_options                ""
% 54.63/7.48  --sat_gr_def                            false
% 54.63/7.48  --sat_epr_types                         true
% 54.63/7.48  --sat_non_cyclic_types                  false
% 54.63/7.48  --sat_finite_models                     false
% 54.63/7.48  --sat_fm_lemmas                         false
% 54.63/7.48  --sat_fm_prep                           false
% 54.63/7.48  --sat_fm_uc_incr                        true
% 54.63/7.48  --sat_out_model                         small
% 54.63/7.48  --sat_out_clauses                       false
% 54.63/7.48  
% 54.63/7.48  ------ QBF Options
% 54.63/7.48  
% 54.63/7.48  --qbf_mode                              false
% 54.63/7.48  --qbf_elim_univ                         false
% 54.63/7.48  --qbf_dom_inst                          none
% 54.63/7.48  --qbf_dom_pre_inst                      false
% 54.63/7.48  --qbf_sk_in                             false
% 54.63/7.48  --qbf_pred_elim                         true
% 54.63/7.48  --qbf_split                             512
% 54.63/7.48  
% 54.63/7.48  ------ BMC1 Options
% 54.63/7.48  
% 54.63/7.48  --bmc1_incremental                      false
% 54.63/7.48  --bmc1_axioms                           reachable_all
% 54.63/7.48  --bmc1_min_bound                        0
% 54.63/7.48  --bmc1_max_bound                        -1
% 54.63/7.48  --bmc1_max_bound_default                -1
% 54.63/7.48  --bmc1_symbol_reachability              true
% 54.63/7.48  --bmc1_property_lemmas                  false
% 54.63/7.48  --bmc1_k_induction                      false
% 54.63/7.48  --bmc1_non_equiv_states                 false
% 54.63/7.48  --bmc1_deadlock                         false
% 54.63/7.48  --bmc1_ucm                              false
% 54.63/7.48  --bmc1_add_unsat_core                   none
% 54.63/7.48  --bmc1_unsat_core_children              false
% 54.63/7.48  --bmc1_unsat_core_extrapolate_axioms    false
% 54.63/7.48  --bmc1_out_stat                         full
% 54.63/7.48  --bmc1_ground_init                      false
% 54.63/7.48  --bmc1_pre_inst_next_state              false
% 54.63/7.48  --bmc1_pre_inst_state                   false
% 54.63/7.48  --bmc1_pre_inst_reach_state             false
% 54.63/7.48  --bmc1_out_unsat_core                   false
% 54.63/7.48  --bmc1_aig_witness_out                  false
% 54.63/7.48  --bmc1_verbose                          false
% 54.63/7.48  --bmc1_dump_clauses_tptp                false
% 54.63/7.48  --bmc1_dump_unsat_core_tptp             false
% 54.63/7.48  --bmc1_dump_file                        -
% 54.63/7.48  --bmc1_ucm_expand_uc_limit              128
% 54.63/7.48  --bmc1_ucm_n_expand_iterations          6
% 54.63/7.48  --bmc1_ucm_extend_mode                  1
% 54.63/7.48  --bmc1_ucm_init_mode                    2
% 54.63/7.48  --bmc1_ucm_cone_mode                    none
% 54.63/7.48  --bmc1_ucm_reduced_relation_type        0
% 54.63/7.48  --bmc1_ucm_relax_model                  4
% 54.63/7.48  --bmc1_ucm_full_tr_after_sat            true
% 54.63/7.48  --bmc1_ucm_expand_neg_assumptions       false
% 54.63/7.48  --bmc1_ucm_layered_model                none
% 54.63/7.48  --bmc1_ucm_max_lemma_size               10
% 54.63/7.48  
% 54.63/7.48  ------ AIG Options
% 54.63/7.48  
% 54.63/7.48  --aig_mode                              false
% 54.63/7.48  
% 54.63/7.48  ------ Instantiation Options
% 54.63/7.48  
% 54.63/7.48  --instantiation_flag                    true
% 54.63/7.48  --inst_sos_flag                         false
% 54.63/7.48  --inst_sos_phase                        true
% 54.63/7.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 54.63/7.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 54.63/7.48  --inst_lit_sel_side                     num_symb
% 54.63/7.48  --inst_solver_per_active                1400
% 54.63/7.48  --inst_solver_calls_frac                1.
% 54.63/7.48  --inst_passive_queue_type               priority_queues
% 54.63/7.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 54.63/7.48  --inst_passive_queues_freq              [25;2]
% 54.63/7.48  --inst_dismatching                      true
% 54.63/7.48  --inst_eager_unprocessed_to_passive     true
% 54.63/7.48  --inst_prop_sim_given                   true
% 54.63/7.48  --inst_prop_sim_new                     false
% 54.63/7.48  --inst_subs_new                         false
% 54.63/7.48  --inst_eq_res_simp                      false
% 54.63/7.48  --inst_subs_given                       false
% 54.63/7.48  --inst_orphan_elimination               true
% 54.63/7.48  --inst_learning_loop_flag               true
% 54.63/7.48  --inst_learning_start                   3000
% 54.63/7.48  --inst_learning_factor                  2
% 54.63/7.48  --inst_start_prop_sim_after_learn       3
% 54.63/7.48  --inst_sel_renew                        solver
% 54.63/7.48  --inst_lit_activity_flag                true
% 54.63/7.48  --inst_restr_to_given                   false
% 54.63/7.48  --inst_activity_threshold               500
% 54.63/7.48  --inst_out_proof                        true
% 54.63/7.48  
% 54.63/7.48  ------ Resolution Options
% 54.63/7.48  
% 54.63/7.48  --resolution_flag                       true
% 54.63/7.48  --res_lit_sel                           adaptive
% 54.63/7.48  --res_lit_sel_side                      none
% 54.63/7.48  --res_ordering                          kbo
% 54.63/7.48  --res_to_prop_solver                    active
% 54.63/7.48  --res_prop_simpl_new                    false
% 54.63/7.48  --res_prop_simpl_given                  true
% 54.63/7.48  --res_passive_queue_type                priority_queues
% 54.63/7.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 54.63/7.48  --res_passive_queues_freq               [15;5]
% 54.63/7.48  --res_forward_subs                      full
% 54.63/7.48  --res_backward_subs                     full
% 54.63/7.48  --res_forward_subs_resolution           true
% 54.63/7.48  --res_backward_subs_resolution          true
% 54.63/7.48  --res_orphan_elimination                true
% 54.63/7.48  --res_time_limit                        2.
% 54.63/7.48  --res_out_proof                         true
% 54.63/7.48  
% 54.63/7.48  ------ Superposition Options
% 54.63/7.48  
% 54.63/7.48  --superposition_flag                    true
% 54.63/7.48  --sup_passive_queue_type                priority_queues
% 54.63/7.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 54.63/7.48  --sup_passive_queues_freq               [1;4]
% 54.63/7.48  --demod_completeness_check              fast
% 54.63/7.48  --demod_use_ground                      true
% 54.63/7.48  --sup_to_prop_solver                    passive
% 54.63/7.48  --sup_prop_simpl_new                    true
% 54.63/7.48  --sup_prop_simpl_given                  true
% 54.63/7.48  --sup_fun_splitting                     false
% 54.63/7.48  --sup_smt_interval                      50000
% 54.63/7.48  
% 54.63/7.48  ------ Superposition Simplification Setup
% 54.63/7.48  
% 54.63/7.48  --sup_indices_passive                   []
% 54.63/7.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.63/7.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.63/7.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 54.63/7.48  --sup_full_triv                         [TrivRules;PropSubs]
% 54.63/7.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.63/7.48  --sup_full_bw                           [BwDemod]
% 54.63/7.48  --sup_immed_triv                        [TrivRules]
% 54.63/7.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 54.63/7.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.63/7.48  --sup_immed_bw_main                     []
% 54.63/7.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 54.63/7.48  --sup_input_triv                        [Unflattening;TrivRules]
% 54.63/7.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 54.63/7.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 54.63/7.48  
% 54.63/7.48  ------ Combination Options
% 54.63/7.48  
% 54.63/7.48  --comb_res_mult                         3
% 54.63/7.48  --comb_sup_mult                         2
% 54.63/7.48  --comb_inst_mult                        10
% 54.63/7.48  
% 54.63/7.48  ------ Debug Options
% 54.63/7.48  
% 54.63/7.48  --dbg_backtrace                         false
% 54.63/7.48  --dbg_dump_prop_clauses                 false
% 54.63/7.48  --dbg_dump_prop_clauses_file            -
% 54.63/7.48  --dbg_out_stat                          false
% 54.63/7.48  
% 54.63/7.48  
% 54.63/7.48  
% 54.63/7.48  
% 54.63/7.48  ------ Proving...
% 54.63/7.48  
% 54.63/7.48  
% 54.63/7.48  % SZS status Theorem for theBenchmark.p
% 54.63/7.48  
% 54.63/7.48  % SZS output start CNFRefutation for theBenchmark.p
% 54.63/7.48  
% 54.63/7.48  fof(f14,conjecture,(
% 54.63/7.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 54.63/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.63/7.48  
% 54.63/7.48  fof(f15,negated_conjecture,(
% 54.63/7.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 54.63/7.48    inference(negated_conjecture,[],[f14])).
% 54.63/7.48  
% 54.63/7.48  fof(f25,plain,(
% 54.63/7.48    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 54.63/7.48    inference(ennf_transformation,[],[f15])).
% 54.63/7.48  
% 54.63/7.48  fof(f26,plain,(
% 54.63/7.48    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 54.63/7.48    inference(flattening,[],[f25])).
% 54.63/7.48  
% 54.63/7.48  fof(f34,plain,(
% 54.63/7.48    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) & r1_tarski(sK2,sK3) & v1_relat_1(sK4))),
% 54.63/7.48    introduced(choice_axiom,[])).
% 54.63/7.48  
% 54.63/7.48  fof(f35,plain,(
% 54.63/7.48    k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) & r1_tarski(sK2,sK3) & v1_relat_1(sK4)),
% 54.63/7.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f34])).
% 54.63/7.48  
% 54.63/7.48  fof(f54,plain,(
% 54.63/7.48    r1_tarski(sK2,sK3)),
% 54.63/7.48    inference(cnf_transformation,[],[f35])).
% 54.63/7.48  
% 54.63/7.48  fof(f9,axiom,(
% 54.63/7.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 54.63/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.63/7.48  
% 54.63/7.48  fof(f48,plain,(
% 54.63/7.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 54.63/7.48    inference(cnf_transformation,[],[f9])).
% 54.63/7.48  
% 54.63/7.48  fof(f4,axiom,(
% 54.63/7.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 54.63/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.63/7.48  
% 54.63/7.48  fof(f43,plain,(
% 54.63/7.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 54.63/7.48    inference(cnf_transformation,[],[f4])).
% 54.63/7.48  
% 54.63/7.48  fof(f10,axiom,(
% 54.63/7.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 54.63/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.63/7.48  
% 54.63/7.48  fof(f49,plain,(
% 54.63/7.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 54.63/7.48    inference(cnf_transformation,[],[f10])).
% 54.63/7.48  
% 54.63/7.48  fof(f56,plain,(
% 54.63/7.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 54.63/7.48    inference(definition_unfolding,[],[f43,f49])).
% 54.63/7.48  
% 54.63/7.48  fof(f63,plain,(
% 54.63/7.48    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1)) )),
% 54.63/7.48    inference(definition_unfolding,[],[f48,f56])).
% 54.63/7.48  
% 54.63/7.48  fof(f7,axiom,(
% 54.63/7.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 54.63/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.63/7.48  
% 54.63/7.48  fof(f46,plain,(
% 54.63/7.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 54.63/7.48    inference(cnf_transformation,[],[f7])).
% 54.63/7.48  
% 54.63/7.48  fof(f62,plain,(
% 54.63/7.48    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X1)) )),
% 54.63/7.48    inference(definition_unfolding,[],[f46,f56])).
% 54.63/7.48  
% 54.63/7.48  fof(f2,axiom,(
% 54.63/7.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 54.63/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.63/7.48  
% 54.63/7.48  fof(f31,plain,(
% 54.63/7.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 54.63/7.48    inference(nnf_transformation,[],[f2])).
% 54.63/7.48  
% 54.63/7.48  fof(f39,plain,(
% 54.63/7.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 54.63/7.48    inference(cnf_transformation,[],[f31])).
% 54.63/7.48  
% 54.63/7.48  fof(f58,plain,(
% 54.63/7.48    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 54.63/7.48    inference(definition_unfolding,[],[f39,f49])).
% 54.63/7.48  
% 54.63/7.48  fof(f8,axiom,(
% 54.63/7.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 54.63/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.63/7.48  
% 54.63/7.48  fof(f47,plain,(
% 54.63/7.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 54.63/7.48    inference(cnf_transformation,[],[f8])).
% 54.63/7.48  
% 54.63/7.48  fof(f40,plain,(
% 54.63/7.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 54.63/7.48    inference(cnf_transformation,[],[f31])).
% 54.63/7.48  
% 54.63/7.48  fof(f57,plain,(
% 54.63/7.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 54.63/7.48    inference(definition_unfolding,[],[f40,f49])).
% 54.63/7.48  
% 54.63/7.48  fof(f6,axiom,(
% 54.63/7.48    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 54.63/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.63/7.48  
% 54.63/7.48  fof(f19,plain,(
% 54.63/7.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 54.63/7.48    inference(ennf_transformation,[],[f6])).
% 54.63/7.48  
% 54.63/7.48  fof(f20,plain,(
% 54.63/7.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 54.63/7.48    inference(flattening,[],[f19])).
% 54.63/7.48  
% 54.63/7.48  fof(f45,plain,(
% 54.63/7.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 54.63/7.48    inference(cnf_transformation,[],[f20])).
% 54.63/7.48  
% 54.63/7.48  fof(f53,plain,(
% 54.63/7.48    v1_relat_1(sK4)),
% 54.63/7.48    inference(cnf_transformation,[],[f35])).
% 54.63/7.48  
% 54.63/7.48  fof(f11,axiom,(
% 54.63/7.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 54.63/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.63/7.48  
% 54.63/7.48  fof(f21,plain,(
% 54.63/7.48    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 54.63/7.48    inference(ennf_transformation,[],[f11])).
% 54.63/7.48  
% 54.63/7.48  fof(f50,plain,(
% 54.63/7.48    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 54.63/7.48    inference(cnf_transformation,[],[f21])).
% 54.63/7.48  
% 54.63/7.48  fof(f64,plain,(
% 54.63/7.48    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X2)) )),
% 54.63/7.48    inference(definition_unfolding,[],[f50,f49])).
% 54.63/7.48  
% 54.63/7.48  fof(f5,axiom,(
% 54.63/7.48    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 54.63/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.63/7.48  
% 54.63/7.48  fof(f44,plain,(
% 54.63/7.48    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 54.63/7.48    inference(cnf_transformation,[],[f5])).
% 54.63/7.48  
% 54.63/7.48  fof(f61,plain,(
% 54.63/7.48    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 54.63/7.48    inference(definition_unfolding,[],[f44,f49])).
% 54.63/7.48  
% 54.63/7.48  fof(f12,axiom,(
% 54.63/7.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 54.63/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.63/7.48  
% 54.63/7.48  fof(f22,plain,(
% 54.63/7.48    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 54.63/7.48    inference(ennf_transformation,[],[f12])).
% 54.63/7.48  
% 54.63/7.48  fof(f51,plain,(
% 54.63/7.48    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 54.63/7.48    inference(cnf_transformation,[],[f22])).
% 54.63/7.48  
% 54.63/7.48  fof(f1,axiom,(
% 54.63/7.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 54.63/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.63/7.48  
% 54.63/7.48  fof(f17,plain,(
% 54.63/7.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 54.63/7.48    inference(ennf_transformation,[],[f1])).
% 54.63/7.48  
% 54.63/7.48  fof(f27,plain,(
% 54.63/7.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 54.63/7.48    inference(nnf_transformation,[],[f17])).
% 54.63/7.48  
% 54.63/7.48  fof(f28,plain,(
% 54.63/7.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 54.63/7.48    inference(rectify,[],[f27])).
% 54.63/7.48  
% 54.63/7.48  fof(f29,plain,(
% 54.63/7.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 54.63/7.48    introduced(choice_axiom,[])).
% 54.63/7.48  
% 54.63/7.48  fof(f30,plain,(
% 54.63/7.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 54.63/7.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 54.63/7.48  
% 54.63/7.48  fof(f37,plain,(
% 54.63/7.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 54.63/7.48    inference(cnf_transformation,[],[f30])).
% 54.63/7.48  
% 54.63/7.48  fof(f38,plain,(
% 54.63/7.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 54.63/7.48    inference(cnf_transformation,[],[f30])).
% 54.63/7.48  
% 54.63/7.48  fof(f13,axiom,(
% 54.63/7.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 54.63/7.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.63/7.48  
% 54.63/7.48  fof(f23,plain,(
% 54.63/7.48    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 54.63/7.48    inference(ennf_transformation,[],[f13])).
% 54.63/7.48  
% 54.63/7.48  fof(f24,plain,(
% 54.63/7.48    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 54.63/7.48    inference(flattening,[],[f23])).
% 54.63/7.48  
% 54.63/7.48  fof(f52,plain,(
% 54.63/7.48    ( ! [X2,X0,X1] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 54.63/7.48    inference(cnf_transformation,[],[f24])).
% 54.63/7.48  
% 54.63/7.48  fof(f55,plain,(
% 54.63/7.48    k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2)),
% 54.63/7.48    inference(cnf_transformation,[],[f35])).
% 54.63/7.48  
% 54.63/7.48  cnf(c_16,negated_conjecture,
% 54.63/7.48      ( r1_tarski(sK2,sK3) ),
% 54.63/7.48      inference(cnf_transformation,[],[f54]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_177,negated_conjecture,
% 54.63/7.48      ( r1_tarski(sK2,sK3) ),
% 54.63/7.48      inference(subtyping,[status(esa)],[c_16]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_610,plain,
% 54.63/7.48      ( r1_tarski(sK2,sK3) = iProver_top ),
% 54.63/7.48      inference(predicate_to_equality,[status(thm)],[c_177]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_11,plain,
% 54.63/7.48      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
% 54.63/7.48      inference(cnf_transformation,[],[f63]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_182,plain,
% 54.63/7.48      ( k5_xboole_0(X0_44,k1_setfam_1(k2_tarski(X0_44,X1_44))) = k6_subset_1(X0_44,X1_44) ),
% 54.63/7.48      inference(subtyping,[status(esa)],[c_11]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_9,plain,
% 54.63/7.48      ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X1) ),
% 54.63/7.48      inference(cnf_transformation,[],[f62]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_184,plain,
% 54.63/7.48      ( r1_xboole_0(k5_xboole_0(X0_44,k1_setfam_1(k2_tarski(X0_44,X1_44))),X1_44) ),
% 54.63/7.48      inference(subtyping,[status(esa)],[c_9]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_606,plain,
% 54.63/7.48      ( r1_xboole_0(k5_xboole_0(X0_44,k1_setfam_1(k2_tarski(X0_44,X1_44))),X1_44) = iProver_top ),
% 54.63/7.48      inference(predicate_to_equality,[status(thm)],[c_184]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_623,plain,
% 54.63/7.48      ( r1_xboole_0(k6_subset_1(X0_44,X1_44),X1_44) = iProver_top ),
% 54.63/7.48      inference(demodulation,[status(thm)],[c_182,c_606]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_4,plain,
% 54.63/7.48      ( ~ r1_xboole_0(X0,X1)
% 54.63/7.48      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 54.63/7.48      inference(cnf_transformation,[],[f58]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_189,plain,
% 54.63/7.48      ( ~ r1_xboole_0(X0_44,X1_44)
% 54.63/7.48      | k1_setfam_1(k2_tarski(X0_44,X1_44)) = k1_xboole_0 ),
% 54.63/7.48      inference(subtyping,[status(esa)],[c_4]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_602,plain,
% 54.63/7.48      ( k1_setfam_1(k2_tarski(X0_44,X1_44)) = k1_xboole_0
% 54.63/7.48      | r1_xboole_0(X0_44,X1_44) != iProver_top ),
% 54.63/7.48      inference(predicate_to_equality,[status(thm)],[c_189]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_1232,plain,
% 54.63/7.48      ( k1_setfam_1(k2_tarski(k6_subset_1(X0_44,X1_44),X1_44)) = k1_xboole_0 ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_623,c_602]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_10,plain,
% 54.63/7.48      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 54.63/7.48      inference(cnf_transformation,[],[f47]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_183,plain,
% 54.63/7.48      ( k2_tarski(X0_44,X1_44) = k2_tarski(X1_44,X0_44) ),
% 54.63/7.48      inference(subtyping,[status(esa)],[c_10]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_3,plain,
% 54.63/7.48      ( r1_xboole_0(X0,X1)
% 54.63/7.48      | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 54.63/7.48      inference(cnf_transformation,[],[f57]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_190,plain,
% 54.63/7.48      ( r1_xboole_0(X0_44,X1_44)
% 54.63/7.48      | k1_setfam_1(k2_tarski(X0_44,X1_44)) != k1_xboole_0 ),
% 54.63/7.48      inference(subtyping,[status(esa)],[c_3]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_601,plain,
% 54.63/7.48      ( k1_setfam_1(k2_tarski(X0_44,X1_44)) != k1_xboole_0
% 54.63/7.48      | r1_xboole_0(X0_44,X1_44) = iProver_top ),
% 54.63/7.48      inference(predicate_to_equality,[status(thm)],[c_190]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_1041,plain,
% 54.63/7.48      ( k1_setfam_1(k2_tarski(X0_44,X1_44)) != k1_xboole_0
% 54.63/7.48      | r1_xboole_0(X1_44,X0_44) = iProver_top ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_183,c_601]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_2179,plain,
% 54.63/7.48      ( r1_xboole_0(X0_44,k6_subset_1(X1_44,X0_44)) = iProver_top ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_1232,c_1041]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_8,plain,
% 54.63/7.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | ~ r1_tarski(X2,X0) ),
% 54.63/7.48      inference(cnf_transformation,[],[f45]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_185,plain,
% 54.63/7.48      ( ~ r1_xboole_0(X0_44,X1_44)
% 54.63/7.48      | r1_xboole_0(X2_44,X1_44)
% 54.63/7.48      | ~ r1_tarski(X2_44,X0_44) ),
% 54.63/7.48      inference(subtyping,[status(esa)],[c_8]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_605,plain,
% 54.63/7.48      ( r1_xboole_0(X0_44,X1_44) != iProver_top
% 54.63/7.48      | r1_xboole_0(X2_44,X1_44) = iProver_top
% 54.63/7.48      | r1_tarski(X2_44,X0_44) != iProver_top ),
% 54.63/7.48      inference(predicate_to_equality,[status(thm)],[c_185]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_2520,plain,
% 54.63/7.48      ( r1_xboole_0(X0_44,k6_subset_1(X1_44,X2_44)) = iProver_top
% 54.63/7.48      | r1_tarski(X0_44,X2_44) != iProver_top ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_2179,c_605]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_8827,plain,
% 54.63/7.48      ( k1_setfam_1(k2_tarski(X0_44,k6_subset_1(X1_44,X2_44))) = k1_xboole_0
% 54.63/7.48      | r1_tarski(X0_44,X2_44) != iProver_top ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_2520,c_602]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_13482,plain,
% 54.63/7.48      ( k1_setfam_1(k2_tarski(sK2,k6_subset_1(X0_44,sK3))) = k1_xboole_0 ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_610,c_8827]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_17,negated_conjecture,
% 54.63/7.48      ( v1_relat_1(sK4) ),
% 54.63/7.48      inference(cnf_transformation,[],[f53]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_176,negated_conjecture,
% 54.63/7.48      ( v1_relat_1(sK4) ),
% 54.63/7.48      inference(subtyping,[status(esa)],[c_17]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_611,plain,
% 54.63/7.48      ( v1_relat_1(sK4) = iProver_top ),
% 54.63/7.48      inference(predicate_to_equality,[status(thm)],[c_176]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_12,plain,
% 54.63/7.48      ( ~ v1_relat_1(X0)
% 54.63/7.48      | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 54.63/7.48      inference(cnf_transformation,[],[f64]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_181,plain,
% 54.63/7.48      ( ~ v1_relat_1(X0_44)
% 54.63/7.48      | k7_relat_1(X0_44,k1_setfam_1(k2_tarski(X1_44,X2_44))) = k7_relat_1(k7_relat_1(X0_44,X1_44),X2_44) ),
% 54.63/7.48      inference(subtyping,[status(esa)],[c_12]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_607,plain,
% 54.63/7.48      ( k7_relat_1(X0_44,k1_setfam_1(k2_tarski(X1_44,X2_44))) = k7_relat_1(k7_relat_1(X0_44,X1_44),X2_44)
% 54.63/7.48      | v1_relat_1(X0_44) != iProver_top ),
% 54.63/7.48      inference(predicate_to_equality,[status(thm)],[c_181]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_1797,plain,
% 54.63/7.48      ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(X0_44,X1_44))) = k7_relat_1(k7_relat_1(sK4,X0_44),X1_44) ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_611,c_607]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_13764,plain,
% 54.63/7.48      ( k7_relat_1(k7_relat_1(sK4,sK2),k6_subset_1(X0_44,sK3)) = k7_relat_1(sK4,k1_xboole_0) ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_13482,c_1797]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_7,plain,
% 54.63/7.48      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 54.63/7.48      inference(cnf_transformation,[],[f61]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_186,plain,
% 54.63/7.48      ( k1_setfam_1(k2_tarski(X0_44,k1_xboole_0)) = k1_xboole_0 ),
% 54.63/7.48      inference(subtyping,[status(esa)],[c_7]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_746,plain,
% 54.63/7.48      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0_44)) = k1_xboole_0 ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_183,c_186]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_1040,plain,
% 54.63/7.48      ( r1_xboole_0(k1_xboole_0,X0_44) = iProver_top ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_746,c_601]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_13,plain,
% 54.63/7.48      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 54.63/7.48      | ~ v1_relat_1(X1)
% 54.63/7.48      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 54.63/7.48      inference(cnf_transformation,[],[f51]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_180,plain,
% 54.63/7.48      ( ~ r1_xboole_0(X0_44,k1_relat_1(X1_44))
% 54.63/7.48      | ~ v1_relat_1(X1_44)
% 54.63/7.48      | k7_relat_1(X1_44,X0_44) = k1_xboole_0 ),
% 54.63/7.48      inference(subtyping,[status(esa)],[c_13]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_608,plain,
% 54.63/7.48      ( k7_relat_1(X0_44,X1_44) = k1_xboole_0
% 54.63/7.48      | r1_xboole_0(X1_44,k1_relat_1(X0_44)) != iProver_top
% 54.63/7.48      | v1_relat_1(X0_44) != iProver_top ),
% 54.63/7.48      inference(predicate_to_equality,[status(thm)],[c_180]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_2032,plain,
% 54.63/7.48      ( k7_relat_1(X0_44,k1_xboole_0) = k1_xboole_0
% 54.63/7.48      | v1_relat_1(X0_44) != iProver_top ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_1040,c_608]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_4300,plain,
% 54.63/7.48      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_611,c_2032]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_13793,plain,
% 54.63/7.48      ( k7_relat_1(k7_relat_1(sK4,sK2),k6_subset_1(X0_44,sK3)) = k1_xboole_0 ),
% 54.63/7.48      inference(light_normalisation,[status(thm)],[c_13764,c_4300]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_1,plain,
% 54.63/7.48      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 54.63/7.48      inference(cnf_transformation,[],[f37]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_192,plain,
% 54.63/7.48      ( r2_hidden(sK0(X0_44,X1_44),X0_44) | r1_tarski(X0_44,X1_44) ),
% 54.63/7.48      inference(subtyping,[status(esa)],[c_1]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_599,plain,
% 54.63/7.48      ( r2_hidden(sK0(X0_44,X1_44),X0_44) = iProver_top
% 54.63/7.48      | r1_tarski(X0_44,X1_44) = iProver_top ),
% 54.63/7.48      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_0,plain,
% 54.63/7.48      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 54.63/7.48      inference(cnf_transformation,[],[f38]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_193,plain,
% 54.63/7.48      ( ~ r2_hidden(sK0(X0_44,X1_44),X1_44) | r1_tarski(X0_44,X1_44) ),
% 54.63/7.48      inference(subtyping,[status(esa)],[c_0]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_598,plain,
% 54.63/7.48      ( r2_hidden(sK0(X0_44,X1_44),X1_44) != iProver_top
% 54.63/7.48      | r1_tarski(X0_44,X1_44) = iProver_top ),
% 54.63/7.48      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_943,plain,
% 54.63/7.48      ( r1_tarski(X0_44,X0_44) = iProver_top ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_599,c_598]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_14,plain,
% 54.63/7.48      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 54.63/7.48      | ~ v1_relat_1(X0)
% 54.63/7.48      | k7_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(X0,k7_relat_1(X0,X2)) ),
% 54.63/7.48      inference(cnf_transformation,[],[f52]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_179,plain,
% 54.63/7.48      ( ~ r1_tarski(k1_relat_1(X0_44),X1_44)
% 54.63/7.48      | ~ v1_relat_1(X0_44)
% 54.63/7.48      | k7_relat_1(X0_44,k6_subset_1(X1_44,X2_44)) = k6_subset_1(X0_44,k7_relat_1(X0_44,X2_44)) ),
% 54.63/7.48      inference(subtyping,[status(esa)],[c_14]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_609,plain,
% 54.63/7.48      ( k7_relat_1(X0_44,k6_subset_1(X1_44,X2_44)) = k6_subset_1(X0_44,k7_relat_1(X0_44,X2_44))
% 54.63/7.48      | r1_tarski(k1_relat_1(X0_44),X1_44) != iProver_top
% 54.63/7.48      | v1_relat_1(X0_44) != iProver_top ),
% 54.63/7.48      inference(predicate_to_equality,[status(thm)],[c_179]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_1909,plain,
% 54.63/7.48      ( k7_relat_1(X0_44,k6_subset_1(k1_relat_1(X0_44),X1_44)) = k6_subset_1(X0_44,k7_relat_1(X0_44,X1_44))
% 54.63/7.48      | v1_relat_1(X0_44) != iProver_top ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_943,c_609]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_5687,plain,
% 54.63/7.48      ( k7_relat_1(sK4,k6_subset_1(k1_relat_1(sK4),X0_44)) = k6_subset_1(sK4,k7_relat_1(sK4,X0_44)) ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_611,c_1909]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_4650,plain,
% 54.63/7.48      ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(X0_44,X1_44))) = k7_relat_1(k7_relat_1(sK4,X1_44),X0_44) ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_183,c_1797]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_4713,plain,
% 54.63/7.48      ( k7_relat_1(k7_relat_1(sK4,X0_44),X1_44) = k7_relat_1(k7_relat_1(sK4,X1_44),X0_44) ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_4650,c_1797]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_8236,plain,
% 54.63/7.48      ( k7_relat_1(k7_relat_1(sK4,X0_44),k6_subset_1(k1_relat_1(sK4),X1_44)) = k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,X1_44)),X0_44) ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_5687,c_4713]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_235861,plain,
% 54.63/7.48      ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) = k1_xboole_0 ),
% 54.63/7.48      inference(superposition,[status(thm)],[c_13793,c_8236]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_198,plain,
% 54.63/7.48      ( X0_44 != X1_44 | X2_44 != X1_44 | X2_44 = X0_44 ),
% 54.63/7.48      theory(equality) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_743,plain,
% 54.63/7.48      ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) != X0_44
% 54.63/7.48      | k1_xboole_0 != X0_44
% 54.63/7.48      | k1_xboole_0 = k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
% 54.63/7.48      inference(instantiation,[status(thm)],[c_198]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_744,plain,
% 54.63/7.48      ( k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) != k1_xboole_0
% 54.63/7.48      | k1_xboole_0 = k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2)
% 54.63/7.48      | k1_xboole_0 != k1_xboole_0 ),
% 54.63/7.48      inference(instantiation,[status(thm)],[c_743]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_15,negated_conjecture,
% 54.63/7.48      ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
% 54.63/7.48      inference(cnf_transformation,[],[f55]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_178,negated_conjecture,
% 54.63/7.48      ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK4,k7_relat_1(sK4,sK3)),sK2) ),
% 54.63/7.48      inference(subtyping,[status(esa)],[c_15]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_195,plain,( X0_44 = X0_44 ),theory(equality) ).
% 54.63/7.48  
% 54.63/7.48  cnf(c_219,plain,
% 54.63/7.48      ( k1_xboole_0 = k1_xboole_0 ),
% 54.63/7.48      inference(instantiation,[status(thm)],[c_195]) ).
% 54.63/7.48  
% 54.63/7.48  cnf(contradiction,plain,
% 54.63/7.48      ( $false ),
% 54.63/7.48      inference(minisat,[status(thm)],[c_235861,c_744,c_178,c_219]) ).
% 54.63/7.48  
% 54.63/7.48  
% 54.63/7.48  % SZS output end CNFRefutation for theBenchmark.p
% 54.63/7.48  
% 54.63/7.48  ------                               Statistics
% 54.63/7.48  
% 54.63/7.48  ------ Selected
% 54.63/7.48  
% 54.63/7.48  total_time:                             6.826
% 54.63/7.48  
%------------------------------------------------------------------------------
