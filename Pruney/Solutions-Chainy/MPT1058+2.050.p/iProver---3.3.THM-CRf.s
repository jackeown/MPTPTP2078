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
% DateTime   : Thu Dec  3 12:09:20 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 244 expanded)
%              Number of clauses        :   54 (  99 expanded)
%              Number of leaves         :   15 (  54 expanded)
%              Depth                    :   20
%              Number of atoms          :  242 ( 543 expanded)
%              Number of equality atoms :  111 ( 245 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30,f29])).

fof(f50,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f44,f37])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f47,f37])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_448,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_446,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_451,plain,
    ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1383,plain,
    ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_446,c_451])).

cnf(c_0,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_10,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_452,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_454,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1889,plain,
    ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_452,c_454])).

cnf(c_8,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1897,plain,
    ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1889,c_8])).

cnf(c_2181,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_452,c_1897])).

cnf(c_14,plain,
    ( k6_relat_1(k1_setfam_1(k2_tarski(X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2186,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_2181,c_8,c_14])).

cnf(c_12,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_450,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2203,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),k1_setfam_1(k2_tarski(X1,X0))),X1) = iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2186,c_450])).

cnf(c_32,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_35,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_18267,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),k1_setfam_1(k2_tarski(X1,X0))),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2203,c_32,c_35])).

cnf(c_18274,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_18267])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_456,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_18379,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_18274,c_456])).

cnf(c_13,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_449,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_20331,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18379,c_449])).

cnf(c_20379,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X0))) = iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20331,c_8,c_2186])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_47,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_20715,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20379,c_32,c_35,c_47])).

cnf(c_20722,plain,
    ( r1_tarski(k10_relat_1(sK0,X0),X1) != iProver_top
    | r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(k7_relat_1(sK0,X1),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1383,c_20715])).

cnf(c_5,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_455,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1159,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_455])).

cnf(c_1164,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1159,c_32])).

cnf(c_2192,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2186,c_1164])).

cnf(c_3647,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK0,X0),X1),k10_relat_1(sK0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1383,c_2192])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_458,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3879,plain,
    ( k10_relat_1(k7_relat_1(sK0,X0),X1) = k10_relat_1(sK0,X1)
    | r1_tarski(k10_relat_1(sK0,X1),k10_relat_1(k7_relat_1(sK0,X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3647,c_458])).

cnf(c_21364,plain,
    ( k10_relat_1(k7_relat_1(sK0,X0),X1) = k10_relat_1(sK0,X1)
    | r1_tarski(k10_relat_1(sK0,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20722,c_3879])).

cnf(c_21864,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_448,c_21364])).

cnf(c_15,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22366,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_21864,c_15])).

cnf(c_1481,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1222,plain,
    ( ~ r1_tarski(X0,k10_relat_1(sK0,sK2))
    | ~ r1_tarski(k10_relat_1(sK0,sK2),X0)
    | k10_relat_1(sK0,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1480,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2))
    | k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_1222])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22366,c_1481,c_1480])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:45:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 7.75/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.75/1.49  
% 7.75/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.75/1.49  
% 7.75/1.49  ------  iProver source info
% 7.75/1.49  
% 7.75/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.75/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.75/1.49  git: non_committed_changes: false
% 7.75/1.49  git: last_make_outside_of_git: false
% 7.75/1.49  
% 7.75/1.49  ------ 
% 7.75/1.49  ------ Parsing...
% 7.75/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.75/1.49  
% 7.75/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.75/1.49  
% 7.75/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.75/1.49  
% 7.75/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.49  ------ Proving...
% 7.75/1.49  ------ Problem Properties 
% 7.75/1.49  
% 7.75/1.49  
% 7.75/1.49  clauses                                 18
% 7.75/1.49  conjectures                             4
% 7.75/1.49  EPR                                     5
% 7.75/1.49  Horn                                    18
% 7.75/1.49  unary                                   11
% 7.75/1.49  binary                                  2
% 7.75/1.49  lits                                    32
% 7.75/1.49  lits eq                                 8
% 7.75/1.49  fd_pure                                 0
% 7.75/1.49  fd_pseudo                               0
% 7.75/1.49  fd_cond                                 0
% 7.75/1.49  fd_pseudo_cond                          1
% 7.75/1.49  AC symbols                              0
% 7.75/1.49  
% 7.75/1.49  ------ Input Options Time Limit: Unbounded
% 7.75/1.49  
% 7.75/1.49  
% 7.75/1.49  ------ 
% 7.75/1.49  Current options:
% 7.75/1.49  ------ 
% 7.75/1.49  
% 7.75/1.49  
% 7.75/1.49  
% 7.75/1.49  
% 7.75/1.49  ------ Proving...
% 7.75/1.49  
% 7.75/1.49  
% 7.75/1.49  % SZS status Theorem for theBenchmark.p
% 7.75/1.49  
% 7.75/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.75/1.49  
% 7.75/1.49  fof(f13,conjecture,(
% 7.75/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.75/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f14,negated_conjecture,(
% 7.75/1.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.75/1.49    inference(negated_conjecture,[],[f13])).
% 7.75/1.49  
% 7.75/1.49  fof(f25,plain,(
% 7.75/1.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 7.75/1.49    inference(ennf_transformation,[],[f14])).
% 7.75/1.49  
% 7.75/1.49  fof(f26,plain,(
% 7.75/1.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.75/1.49    inference(flattening,[],[f25])).
% 7.75/1.49  
% 7.75/1.49  fof(f30,plain,(
% 7.75/1.49    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2) & r1_tarski(k10_relat_1(X0,sK2),sK1))) )),
% 7.75/1.49    introduced(choice_axiom,[])).
% 7.75/1.49  
% 7.75/1.49  fof(f29,plain,(
% 7.75/1.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 7.75/1.49    introduced(choice_axiom,[])).
% 7.75/1.49  
% 7.75/1.49  fof(f31,plain,(
% 7.75/1.49    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 7.75/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30,f29])).
% 7.75/1.49  
% 7.75/1.49  fof(f50,plain,(
% 7.75/1.49    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 7.75/1.49    inference(cnf_transformation,[],[f31])).
% 7.75/1.49  
% 7.75/1.49  fof(f48,plain,(
% 7.75/1.49    v1_relat_1(sK0)),
% 7.75/1.49    inference(cnf_transformation,[],[f31])).
% 7.75/1.49  
% 7.75/1.49  fof(f9,axiom,(
% 7.75/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 7.75/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f20,plain,(
% 7.75/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.75/1.49    inference(ennf_transformation,[],[f9])).
% 7.75/1.49  
% 7.75/1.49  fof(f44,plain,(
% 7.75/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.75/1.49    inference(cnf_transformation,[],[f20])).
% 7.75/1.49  
% 7.75/1.49  fof(f4,axiom,(
% 7.75/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.75/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f37,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.75/1.49    inference(cnf_transformation,[],[f4])).
% 7.75/1.49  
% 7.75/1.49  fof(f53,plain,(
% 7.75/1.49    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.75/1.49    inference(definition_unfolding,[],[f44,f37])).
% 7.75/1.49  
% 7.75/1.49  fof(f1,axiom,(
% 7.75/1.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.75/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f15,plain,(
% 7.75/1.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.75/1.49    inference(rectify,[],[f1])).
% 7.75/1.49  
% 7.75/1.49  fof(f32,plain,(
% 7.75/1.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.75/1.49    inference(cnf_transformation,[],[f15])).
% 7.75/1.49  
% 7.75/1.49  fof(f52,plain,(
% 7.75/1.49    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 7.75/1.49    inference(definition_unfolding,[],[f32,f37])).
% 7.75/1.49  
% 7.75/1.49  fof(f8,axiom,(
% 7.75/1.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.75/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f42,plain,(
% 7.75/1.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.75/1.49    inference(cnf_transformation,[],[f8])).
% 7.75/1.49  
% 7.75/1.49  fof(f6,axiom,(
% 7.75/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 7.75/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f19,plain,(
% 7.75/1.49    ! [X0] : (! [X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.75/1.49    inference(ennf_transformation,[],[f6])).
% 7.75/1.49  
% 7.75/1.49  fof(f39,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.75/1.49    inference(cnf_transformation,[],[f19])).
% 7.75/1.49  
% 7.75/1.49  fof(f7,axiom,(
% 7.75/1.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.75/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f40,plain,(
% 7.75/1.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.75/1.49    inference(cnf_transformation,[],[f7])).
% 7.75/1.49  
% 7.75/1.49  fof(f12,axiom,(
% 7.75/1.49    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 7.75/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f47,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 7.75/1.49    inference(cnf_transformation,[],[f12])).
% 7.75/1.49  
% 7.75/1.49  fof(f54,plain,(
% 7.75/1.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_tarski(X0,X1)))) )),
% 7.75/1.49    inference(definition_unfolding,[],[f47,f37])).
% 7.75/1.49  
% 7.75/1.49  fof(f10,axiom,(
% 7.75/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 7.75/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f21,plain,(
% 7.75/1.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.75/1.49    inference(ennf_transformation,[],[f10])).
% 7.75/1.49  
% 7.75/1.49  fof(f22,plain,(
% 7.75/1.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.75/1.49    inference(flattening,[],[f21])).
% 7.75/1.49  
% 7.75/1.49  fof(f45,plain,(
% 7.75/1.49    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.75/1.49    inference(cnf_transformation,[],[f22])).
% 7.75/1.49  
% 7.75/1.49  fof(f43,plain,(
% 7.75/1.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 7.75/1.49    inference(cnf_transformation,[],[f8])).
% 7.75/1.49  
% 7.75/1.49  fof(f3,axiom,(
% 7.75/1.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.75/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f16,plain,(
% 7.75/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.75/1.49    inference(ennf_transformation,[],[f3])).
% 7.75/1.49  
% 7.75/1.49  fof(f17,plain,(
% 7.75/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.75/1.49    inference(flattening,[],[f16])).
% 7.75/1.49  
% 7.75/1.49  fof(f36,plain,(
% 7.75/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.75/1.49    inference(cnf_transformation,[],[f17])).
% 7.75/1.49  
% 7.75/1.49  fof(f11,axiom,(
% 7.75/1.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 7.75/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f23,plain,(
% 7.75/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.75/1.49    inference(ennf_transformation,[],[f11])).
% 7.75/1.49  
% 7.75/1.49  fof(f24,plain,(
% 7.75/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.75/1.49    inference(flattening,[],[f23])).
% 7.75/1.49  
% 7.75/1.49  fof(f46,plain,(
% 7.75/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.75/1.49    inference(cnf_transformation,[],[f24])).
% 7.75/1.49  
% 7.75/1.49  fof(f2,axiom,(
% 7.75/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.75/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f27,plain,(
% 7.75/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.75/1.49    inference(nnf_transformation,[],[f2])).
% 7.75/1.49  
% 7.75/1.49  fof(f28,plain,(
% 7.75/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.75/1.49    inference(flattening,[],[f27])).
% 7.75/1.49  
% 7.75/1.49  fof(f33,plain,(
% 7.75/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.75/1.49    inference(cnf_transformation,[],[f28])).
% 7.75/1.49  
% 7.75/1.49  fof(f56,plain,(
% 7.75/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.75/1.49    inference(equality_resolution,[],[f33])).
% 7.75/1.49  
% 7.75/1.49  fof(f5,axiom,(
% 7.75/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 7.75/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.49  
% 7.75/1.49  fof(f18,plain,(
% 7.75/1.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.75/1.49    inference(ennf_transformation,[],[f5])).
% 7.75/1.49  
% 7.75/1.49  fof(f38,plain,(
% 7.75/1.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.75/1.49    inference(cnf_transformation,[],[f18])).
% 7.75/1.49  
% 7.75/1.49  fof(f35,plain,(
% 7.75/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.75/1.49    inference(cnf_transformation,[],[f28])).
% 7.75/1.49  
% 7.75/1.49  fof(f51,plain,(
% 7.75/1.49    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 7.75/1.49    inference(cnf_transformation,[],[f31])).
% 7.75/1.49  
% 7.75/1.49  cnf(c_16,negated_conjecture,
% 7.75/1.49      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
% 7.75/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_448,plain,
% 7.75/1.49      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_18,negated_conjecture,
% 7.75/1.49      ( v1_relat_1(sK0) ),
% 7.75/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_446,plain,
% 7.75/1.49      ( v1_relat_1(sK0) = iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_11,plain,
% 7.75/1.49      ( ~ v1_relat_1(X0)
% 7.75/1.49      | k1_setfam_1(k2_tarski(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 7.75/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_451,plain,
% 7.75/1.49      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 7.75/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_1383,plain,
% 7.75/1.49      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_446,c_451]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_0,plain,
% 7.75/1.49      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 7.75/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_10,plain,
% 7.75/1.49      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.75/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_452,plain,
% 7.75/1.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_6,plain,
% 7.75/1.49      ( ~ v1_relat_1(X0)
% 7.75/1.49      | ~ v1_relat_1(X1)
% 7.75/1.49      | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
% 7.75/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_454,plain,
% 7.75/1.49      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
% 7.75/1.49      | v1_relat_1(X0) != iProver_top
% 7.75/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_1889,plain,
% 7.75/1.49      ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
% 7.75/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_452,c_454]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_8,plain,
% 7.75/1.49      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.75/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_1897,plain,
% 7.75/1.49      ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,X1)
% 7.75/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.49      inference(demodulation,[status(thm)],[c_1889,c_8]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_2181,plain,
% 7.75/1.49      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_452,c_1897]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_14,plain,
% 7.75/1.49      ( k6_relat_1(k1_setfam_1(k2_tarski(X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 7.75/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_2186,plain,
% 7.75/1.49      ( k10_relat_1(k6_relat_1(X0),X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 7.75/1.49      inference(demodulation,[status(thm)],[c_2181,c_8,c_14]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_12,plain,
% 7.75/1.49      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 7.75/1.49      | ~ v1_funct_1(X0)
% 7.75/1.49      | ~ v1_relat_1(X0) ),
% 7.75/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_450,plain,
% 7.75/1.49      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 7.75/1.49      | v1_funct_1(X0) != iProver_top
% 7.75/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_2203,plain,
% 7.75/1.49      ( r1_tarski(k9_relat_1(k6_relat_1(X0),k1_setfam_1(k2_tarski(X1,X0))),X1) = iProver_top
% 7.75/1.49      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 7.75/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_2186,c_450]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_32,plain,
% 7.75/1.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_9,plain,
% 7.75/1.49      ( v1_funct_1(k6_relat_1(X0)) ),
% 7.75/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_35,plain,
% 7.75/1.49      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_18267,plain,
% 7.75/1.49      ( r1_tarski(k9_relat_1(k6_relat_1(X0),k1_setfam_1(k2_tarski(X1,X0))),X1) = iProver_top ),
% 7.75/1.49      inference(global_propositional_subsumption,
% 7.75/1.49                [status(thm)],
% 7.75/1.49                [c_2203,c_32,c_35]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_18274,plain,
% 7.75/1.49      ( r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0) = iProver_top ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_0,c_18267]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_4,plain,
% 7.75/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.75/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_456,plain,
% 7.75/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.75/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.75/1.49      | r1_tarski(X0,X2) = iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_18379,plain,
% 7.75/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.75/1.49      | r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X1) = iProver_top ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_18274,c_456]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_13,plain,
% 7.75/1.49      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 7.75/1.49      | ~ r1_tarski(X0,k1_relat_1(X1))
% 7.75/1.49      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 7.75/1.49      | ~ v1_funct_1(X1)
% 7.75/1.49      | ~ v1_relat_1(X1) ),
% 7.75/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_449,plain,
% 7.75/1.49      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 7.75/1.49      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 7.75/1.49      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 7.75/1.49      | v1_funct_1(X1) != iProver_top
% 7.75/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_20331,plain,
% 7.75/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.75/1.49      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 7.75/1.49      | r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) != iProver_top
% 7.75/1.49      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 7.75/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_18379,c_449]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_20379,plain,
% 7.75/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.75/1.49      | r1_tarski(X0,X0) != iProver_top
% 7.75/1.49      | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X0))) = iProver_top
% 7.75/1.49      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 7.75/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.75/1.49      inference(light_normalisation,[status(thm)],[c_20331,c_8,c_2186]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_3,plain,
% 7.75/1.49      ( r1_tarski(X0,X0) ),
% 7.75/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_47,plain,
% 7.75/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_20715,plain,
% 7.75/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.75/1.49      | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X0))) = iProver_top ),
% 7.75/1.49      inference(global_propositional_subsumption,
% 7.75/1.49                [status(thm)],
% 7.75/1.49                [c_20379,c_32,c_35,c_47]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_20722,plain,
% 7.75/1.49      ( r1_tarski(k10_relat_1(sK0,X0),X1) != iProver_top
% 7.75/1.49      | r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(k7_relat_1(sK0,X1),X0)) = iProver_top ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_1383,c_20715]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_5,plain,
% 7.75/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.75/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_455,plain,
% 7.75/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.75/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_1159,plain,
% 7.75/1.49      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top
% 7.75/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_8,c_455]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_1164,plain,
% 7.75/1.49      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
% 7.75/1.49      inference(global_propositional_subsumption,
% 7.75/1.49                [status(thm)],
% 7.75/1.49                [c_1159,c_32]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_2192,plain,
% 7.75/1.49      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
% 7.75/1.49      inference(demodulation,[status(thm)],[c_2186,c_1164]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_3647,plain,
% 7.75/1.49      ( r1_tarski(k10_relat_1(k7_relat_1(sK0,X0),X1),k10_relat_1(sK0,X1)) = iProver_top ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_1383,c_2192]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_1,plain,
% 7.75/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.75/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_458,plain,
% 7.75/1.49      ( X0 = X1
% 7.75/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.75/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.75/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_3879,plain,
% 7.75/1.49      ( k10_relat_1(k7_relat_1(sK0,X0),X1) = k10_relat_1(sK0,X1)
% 7.75/1.49      | r1_tarski(k10_relat_1(sK0,X1),k10_relat_1(k7_relat_1(sK0,X0),X1)) != iProver_top ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_3647,c_458]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_21364,plain,
% 7.75/1.49      ( k10_relat_1(k7_relat_1(sK0,X0),X1) = k10_relat_1(sK0,X1)
% 7.75/1.49      | r1_tarski(k10_relat_1(sK0,X1),X0) != iProver_top ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_20722,c_3879]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_21864,plain,
% 7.75/1.49      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
% 7.75/1.49      inference(superposition,[status(thm)],[c_448,c_21364]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_15,negated_conjecture,
% 7.75/1.49      ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 7.75/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_22366,plain,
% 7.75/1.49      ( k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
% 7.75/1.49      inference(demodulation,[status(thm)],[c_21864,c_15]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_1481,plain,
% 7.75/1.49      ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) ),
% 7.75/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_1222,plain,
% 7.75/1.49      ( ~ r1_tarski(X0,k10_relat_1(sK0,sK2))
% 7.75/1.49      | ~ r1_tarski(k10_relat_1(sK0,sK2),X0)
% 7.75/1.49      | k10_relat_1(sK0,sK2) = X0 ),
% 7.75/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(c_1480,plain,
% 7.75/1.49      ( ~ r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2))
% 7.75/1.49      | k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
% 7.75/1.49      inference(instantiation,[status(thm)],[c_1222]) ).
% 7.75/1.49  
% 7.75/1.49  cnf(contradiction,plain,
% 7.75/1.49      ( $false ),
% 7.75/1.49      inference(minisat,[status(thm)],[c_22366,c_1481,c_1480]) ).
% 7.75/1.49  
% 7.75/1.49  
% 7.75/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.75/1.49  
% 7.75/1.49  ------                               Statistics
% 7.75/1.49  
% 7.75/1.49  ------ Selected
% 7.75/1.49  
% 7.75/1.49  total_time:                             0.809
% 7.75/1.49  
%------------------------------------------------------------------------------
