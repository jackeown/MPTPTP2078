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
% DateTime   : Thu Dec  3 11:46:37 EST 2020

% Result     : Theorem 31.90s
% Output     : CNFRefutation 31.90s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 449 expanded)
%              Number of clauses        :   69 ( 186 expanded)
%              Number of leaves         :   17 (  87 expanded)
%              Depth                    :   23
%              Number of atoms          :  279 ( 891 expanded)
%              Number of equality atoms :  109 ( 289 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f36,f55])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f35,f55,f55])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f33])).

fof(f52,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f55])).

fof(f53,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f53,f55,f55])).

cnf(c_1,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_317,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0_41,X0_41,X0_41,X1_41)),X0_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_546,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0_41,X0_41,X0_41,X1_41)),X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_0,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_318,plain,
    ( k1_setfam_1(k2_enumset1(X0_41,X0_41,X0_41,X1_41)) = k1_setfam_1(k2_enumset1(X1_41,X1_41,X1_41,X0_41)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_843,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0_41,X0_41,X0_41,X1_41)),X1_41) = iProver_top ),
    inference(superposition,[status(thm)],[c_318,c_546])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_308,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_555,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_314,plain,
    ( ~ v1_relat_1(X0_41)
    | v1_relat_1(k7_relat_1(X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_549,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k7_relat_1(X0_41,X1_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_311,plain,
    ( ~ v1_relat_1(X0_41)
    | k9_relat_1(X0_41,k1_relat_1(X0_41)) = k2_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_552,plain,
    ( k9_relat_1(X0_41,k1_relat_1(X0_41)) = k2_relat_1(X0_41)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_908,plain,
    ( k9_relat_1(k7_relat_1(X0_41,X1_41),k1_relat_1(k7_relat_1(X0_41,X1_41))) = k2_relat_1(k7_relat_1(X0_41,X1_41))
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_549,c_552])).

cnf(c_2389,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_41),k1_relat_1(k7_relat_1(sK2,X0_41))) = k2_relat_1(k7_relat_1(sK2,X0_41)) ),
    inference(superposition,[status(thm)],[c_555,c_908])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_310,plain,
    ( ~ v1_relat_1(X0_41)
    | k2_relat_1(k7_relat_1(X0_41,X1_41)) = k9_relat_1(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_553,plain,
    ( k2_relat_1(k7_relat_1(X0_41,X1_41)) = k9_relat_1(X0_41,X1_41)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_1048,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0_41)) = k9_relat_1(sK2,X0_41) ),
    inference(superposition,[status(thm)],[c_555,c_553])).

cnf(c_2395,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_41),k1_relat_1(k7_relat_1(sK2,X0_41))) = k9_relat_1(sK2,X0_41) ),
    inference(light_normalisation,[status(thm)],[c_2389,c_1048])).

cnf(c_9,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_312,plain,
    ( r1_tarski(k9_relat_1(X0_41,X1_41),k2_relat_1(X0_41))
    | ~ v1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_551,plain,
    ( r1_tarski(k9_relat_1(X0_41,X1_41),k2_relat_1(X0_41)) = iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_312])).

cnf(c_1118,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_41),X1_41),k9_relat_1(sK2,X0_41)) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0_41)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1048,c_551])).

cnf(c_2467,plain,
    ( r1_tarski(k9_relat_1(sK2,X0_41),k9_relat_1(sK2,X0_41)) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0_41)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2395,c_1118])).

cnf(c_16,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4537,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0_41))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_4538,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0_41)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4537])).

cnf(c_10350,plain,
    ( r1_tarski(k9_relat_1(sK2,X0_41),k9_relat_1(sK2,X0_41)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2467,c_16,c_4538])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_313,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(k7_relat_1(X2_41,X0_41),k7_relat_1(X2_41,X1_41))
    | ~ v1_relat_1(X2_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_550,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(k7_relat_1(X2_41,X0_41),k7_relat_1(X2_41,X1_41)) = iProver_top
    | v1_relat_1(X2_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_92,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_6,c_4])).

cnf(c_93,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_92])).

cnf(c_306,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(k2_relat_1(X0_41),k2_relat_1(X1_41))
    | ~ v1_relat_1(X1_41) ),
    inference(subtyping,[status(esa)],[c_93])).

cnf(c_557,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(k2_relat_1(X0_41),k2_relat_1(X1_41)) = iProver_top
    | v1_relat_1(X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_2188,plain,
    ( r1_tarski(k9_relat_1(sK2,X0_41),k2_relat_1(X1_41)) = iProver_top
    | r1_tarski(k7_relat_1(sK2,X0_41),X1_41) != iProver_top
    | v1_relat_1(X1_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_1048,c_557])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_315,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r1_tarski(X1_41,X2_41)
    | r1_tarski(X0_41,X2_41) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_548,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(X1_41,X2_41) != iProver_top
    | r1_tarski(X0_41,X2_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_2483,plain,
    ( r1_tarski(k9_relat_1(sK2,X0_41),X1_41) = iProver_top
    | r1_tarski(k7_relat_1(sK2,X0_41),X2_41) != iProver_top
    | r1_tarski(k2_relat_1(X2_41),X1_41) != iProver_top
    | v1_relat_1(X2_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_2188,c_548])).

cnf(c_19834,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_41),X2_41) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK2,X1_41)),X2_41) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X1_41)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_550,c_2483])).

cnf(c_19836,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X1_41),X2_41) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_41),X2_41) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X1_41)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19834,c_1048])).

cnf(c_20177,plain,
    ( v1_relat_1(k7_relat_1(sK2,X1_41)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_41),X2_41) = iProver_top
    | r1_tarski(k9_relat_1(sK2,X1_41),X2_41) != iProver_top
    | r1_tarski(X0_41,X1_41) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19836,c_16])).

cnf(c_20178,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X1_41),X2_41) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_41),X2_41) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X1_41)) != iProver_top ),
    inference(renaming,[status(thm)],[c_20177])).

cnf(c_20185,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_41),k9_relat_1(sK2,X1_41)) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X1_41)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10350,c_20178])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_316,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r1_tarski(X0_41,X2_41)
    | r1_tarski(X0_41,k1_setfam_1(k2_enumset1(X2_41,X2_41,X2_41,X1_41))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_547,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(X0_41,X2_41) != iProver_top
    | r1_tarski(X0_41,k1_setfam_1(k2_enumset1(X2_41,X2_41,X2_41,X1_41))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_309,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_554,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_983,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_547,c_554])).

cnf(c_20331,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20185,c_983])).

cnf(c_9974,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4537])).

cnf(c_9975,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK1)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9974])).

cnf(c_20469,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20331,c_16,c_9975])).

cnf(c_20470,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_20469])).

cnf(c_20475,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20185,c_20470])).

cnf(c_4540,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4538])).

cnf(c_61977,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) != iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20475,c_16,c_4540])).

cnf(c_61978,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_61977])).

cnf(c_61981,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_843,c_61978])).

cnf(c_89677,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_546,c_61981])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.90/4.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.90/4.49  
% 31.90/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.90/4.49  
% 31.90/4.49  ------  iProver source info
% 31.90/4.49  
% 31.90/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.90/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.90/4.49  git: non_committed_changes: false
% 31.90/4.49  git: last_make_outside_of_git: false
% 31.90/4.49  
% 31.90/4.49  ------ 
% 31.90/4.49  
% 31.90/4.49  ------ Input Options
% 31.90/4.49  
% 31.90/4.49  --out_options                           all
% 31.90/4.49  --tptp_safe_out                         true
% 31.90/4.49  --problem_path                          ""
% 31.90/4.49  --include_path                          ""
% 31.90/4.49  --clausifier                            res/vclausify_rel
% 31.90/4.49  --clausifier_options                    ""
% 31.90/4.49  --stdin                                 false
% 31.90/4.49  --stats_out                             all
% 31.90/4.49  
% 31.90/4.49  ------ General Options
% 31.90/4.49  
% 31.90/4.49  --fof                                   false
% 31.90/4.49  --time_out_real                         305.
% 31.90/4.49  --time_out_virtual                      -1.
% 31.90/4.49  --symbol_type_check                     false
% 31.90/4.49  --clausify_out                          false
% 31.90/4.49  --sig_cnt_out                           false
% 31.90/4.49  --trig_cnt_out                          false
% 31.90/4.49  --trig_cnt_out_tolerance                1.
% 31.90/4.49  --trig_cnt_out_sk_spl                   false
% 31.90/4.49  --abstr_cl_out                          false
% 31.90/4.49  
% 31.90/4.49  ------ Global Options
% 31.90/4.49  
% 31.90/4.49  --schedule                              default
% 31.90/4.49  --add_important_lit                     false
% 31.90/4.49  --prop_solver_per_cl                    1000
% 31.90/4.49  --min_unsat_core                        false
% 31.90/4.49  --soft_assumptions                      false
% 31.90/4.49  --soft_lemma_size                       3
% 31.90/4.49  --prop_impl_unit_size                   0
% 31.90/4.49  --prop_impl_unit                        []
% 31.90/4.49  --share_sel_clauses                     true
% 31.90/4.49  --reset_solvers                         false
% 31.90/4.49  --bc_imp_inh                            [conj_cone]
% 31.90/4.49  --conj_cone_tolerance                   3.
% 31.90/4.49  --extra_neg_conj                        none
% 31.90/4.49  --large_theory_mode                     true
% 31.90/4.49  --prolific_symb_bound                   200
% 31.90/4.49  --lt_threshold                          2000
% 31.90/4.49  --clause_weak_htbl                      true
% 31.90/4.49  --gc_record_bc_elim                     false
% 31.90/4.49  
% 31.90/4.49  ------ Preprocessing Options
% 31.90/4.49  
% 31.90/4.49  --preprocessing_flag                    true
% 31.90/4.49  --time_out_prep_mult                    0.1
% 31.90/4.49  --splitting_mode                        input
% 31.90/4.49  --splitting_grd                         true
% 31.90/4.49  --splitting_cvd                         false
% 31.90/4.49  --splitting_cvd_svl                     false
% 31.90/4.49  --splitting_nvd                         32
% 31.90/4.49  --sub_typing                            true
% 31.90/4.49  --prep_gs_sim                           true
% 31.90/4.49  --prep_unflatten                        true
% 31.90/4.49  --prep_res_sim                          true
% 31.90/4.49  --prep_upred                            true
% 31.90/4.49  --prep_sem_filter                       exhaustive
% 31.90/4.49  --prep_sem_filter_out                   false
% 31.90/4.49  --pred_elim                             true
% 31.90/4.49  --res_sim_input                         true
% 31.90/4.49  --eq_ax_congr_red                       true
% 31.90/4.49  --pure_diseq_elim                       true
% 31.90/4.49  --brand_transform                       false
% 31.90/4.49  --non_eq_to_eq                          false
% 31.90/4.49  --prep_def_merge                        true
% 31.90/4.49  --prep_def_merge_prop_impl              false
% 31.90/4.49  --prep_def_merge_mbd                    true
% 31.90/4.49  --prep_def_merge_tr_red                 false
% 31.90/4.49  --prep_def_merge_tr_cl                  false
% 31.90/4.49  --smt_preprocessing                     true
% 31.90/4.49  --smt_ac_axioms                         fast
% 31.90/4.49  --preprocessed_out                      false
% 31.90/4.49  --preprocessed_stats                    false
% 31.90/4.49  
% 31.90/4.49  ------ Abstraction refinement Options
% 31.90/4.49  
% 31.90/4.49  --abstr_ref                             []
% 31.90/4.49  --abstr_ref_prep                        false
% 31.90/4.49  --abstr_ref_until_sat                   false
% 31.90/4.49  --abstr_ref_sig_restrict                funpre
% 31.90/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.90/4.49  --abstr_ref_under                       []
% 31.90/4.49  
% 31.90/4.49  ------ SAT Options
% 31.90/4.49  
% 31.90/4.49  --sat_mode                              false
% 31.90/4.49  --sat_fm_restart_options                ""
% 31.90/4.49  --sat_gr_def                            false
% 31.90/4.49  --sat_epr_types                         true
% 31.90/4.49  --sat_non_cyclic_types                  false
% 31.90/4.49  --sat_finite_models                     false
% 31.90/4.49  --sat_fm_lemmas                         false
% 31.90/4.49  --sat_fm_prep                           false
% 31.90/4.49  --sat_fm_uc_incr                        true
% 31.90/4.49  --sat_out_model                         small
% 31.90/4.49  --sat_out_clauses                       false
% 31.90/4.49  
% 31.90/4.49  ------ QBF Options
% 31.90/4.49  
% 31.90/4.49  --qbf_mode                              false
% 31.90/4.49  --qbf_elim_univ                         false
% 31.90/4.49  --qbf_dom_inst                          none
% 31.90/4.49  --qbf_dom_pre_inst                      false
% 31.90/4.49  --qbf_sk_in                             false
% 31.90/4.49  --qbf_pred_elim                         true
% 31.90/4.49  --qbf_split                             512
% 31.90/4.49  
% 31.90/4.49  ------ BMC1 Options
% 31.90/4.49  
% 31.90/4.49  --bmc1_incremental                      false
% 31.90/4.49  --bmc1_axioms                           reachable_all
% 31.90/4.49  --bmc1_min_bound                        0
% 31.90/4.49  --bmc1_max_bound                        -1
% 31.90/4.49  --bmc1_max_bound_default                -1
% 31.90/4.49  --bmc1_symbol_reachability              true
% 31.90/4.49  --bmc1_property_lemmas                  false
% 31.90/4.49  --bmc1_k_induction                      false
% 31.90/4.49  --bmc1_non_equiv_states                 false
% 31.90/4.49  --bmc1_deadlock                         false
% 31.90/4.49  --bmc1_ucm                              false
% 31.90/4.49  --bmc1_add_unsat_core                   none
% 31.90/4.49  --bmc1_unsat_core_children              false
% 31.90/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.90/4.49  --bmc1_out_stat                         full
% 31.90/4.49  --bmc1_ground_init                      false
% 31.90/4.49  --bmc1_pre_inst_next_state              false
% 31.90/4.49  --bmc1_pre_inst_state                   false
% 31.90/4.49  --bmc1_pre_inst_reach_state             false
% 31.90/4.49  --bmc1_out_unsat_core                   false
% 31.90/4.49  --bmc1_aig_witness_out                  false
% 31.90/4.49  --bmc1_verbose                          false
% 31.90/4.49  --bmc1_dump_clauses_tptp                false
% 31.90/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.90/4.49  --bmc1_dump_file                        -
% 31.90/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.90/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.90/4.49  --bmc1_ucm_extend_mode                  1
% 31.90/4.49  --bmc1_ucm_init_mode                    2
% 31.90/4.49  --bmc1_ucm_cone_mode                    none
% 31.90/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.90/4.49  --bmc1_ucm_relax_model                  4
% 31.90/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.90/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.90/4.49  --bmc1_ucm_layered_model                none
% 31.90/4.49  --bmc1_ucm_max_lemma_size               10
% 31.90/4.49  
% 31.90/4.49  ------ AIG Options
% 31.90/4.49  
% 31.90/4.49  --aig_mode                              false
% 31.90/4.49  
% 31.90/4.49  ------ Instantiation Options
% 31.90/4.49  
% 31.90/4.49  --instantiation_flag                    true
% 31.90/4.49  --inst_sos_flag                         true
% 31.90/4.49  --inst_sos_phase                        true
% 31.90/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.90/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.90/4.49  --inst_lit_sel_side                     num_symb
% 31.90/4.49  --inst_solver_per_active                1400
% 31.90/4.49  --inst_solver_calls_frac                1.
% 31.90/4.49  --inst_passive_queue_type               priority_queues
% 31.90/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.90/4.49  --inst_passive_queues_freq              [25;2]
% 31.90/4.49  --inst_dismatching                      true
% 31.90/4.49  --inst_eager_unprocessed_to_passive     true
% 31.90/4.49  --inst_prop_sim_given                   true
% 31.90/4.49  --inst_prop_sim_new                     false
% 31.90/4.49  --inst_subs_new                         false
% 31.90/4.49  --inst_eq_res_simp                      false
% 31.90/4.49  --inst_subs_given                       false
% 31.90/4.49  --inst_orphan_elimination               true
% 31.90/4.49  --inst_learning_loop_flag               true
% 31.90/4.49  --inst_learning_start                   3000
% 31.90/4.49  --inst_learning_factor                  2
% 31.90/4.49  --inst_start_prop_sim_after_learn       3
% 31.90/4.49  --inst_sel_renew                        solver
% 31.90/4.49  --inst_lit_activity_flag                true
% 31.90/4.49  --inst_restr_to_given                   false
% 31.90/4.49  --inst_activity_threshold               500
% 31.90/4.49  --inst_out_proof                        true
% 31.90/4.49  
% 31.90/4.49  ------ Resolution Options
% 31.90/4.49  
% 31.90/4.49  --resolution_flag                       true
% 31.90/4.49  --res_lit_sel                           adaptive
% 31.90/4.49  --res_lit_sel_side                      none
% 31.90/4.49  --res_ordering                          kbo
% 31.90/4.49  --res_to_prop_solver                    active
% 31.90/4.49  --res_prop_simpl_new                    false
% 31.90/4.49  --res_prop_simpl_given                  true
% 31.90/4.49  --res_passive_queue_type                priority_queues
% 31.90/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.90/4.49  --res_passive_queues_freq               [15;5]
% 31.90/4.49  --res_forward_subs                      full
% 31.90/4.49  --res_backward_subs                     full
% 31.90/4.49  --res_forward_subs_resolution           true
% 31.90/4.49  --res_backward_subs_resolution          true
% 31.90/4.49  --res_orphan_elimination                true
% 31.90/4.49  --res_time_limit                        2.
% 31.90/4.49  --res_out_proof                         true
% 31.90/4.49  
% 31.90/4.49  ------ Superposition Options
% 31.90/4.49  
% 31.90/4.49  --superposition_flag                    true
% 31.90/4.49  --sup_passive_queue_type                priority_queues
% 31.90/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.90/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.90/4.49  --demod_completeness_check              fast
% 31.90/4.49  --demod_use_ground                      true
% 31.90/4.49  --sup_to_prop_solver                    passive
% 31.90/4.49  --sup_prop_simpl_new                    true
% 31.90/4.49  --sup_prop_simpl_given                  true
% 31.90/4.49  --sup_fun_splitting                     true
% 31.90/4.49  --sup_smt_interval                      50000
% 31.90/4.49  
% 31.90/4.49  ------ Superposition Simplification Setup
% 31.90/4.49  
% 31.90/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.90/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.90/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.90/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.90/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.90/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.90/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.90/4.49  --sup_immed_triv                        [TrivRules]
% 31.90/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.90/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.90/4.49  --sup_immed_bw_main                     []
% 31.90/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.90/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.90/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.90/4.49  --sup_input_bw                          []
% 31.90/4.49  
% 31.90/4.49  ------ Combination Options
% 31.90/4.49  
% 31.90/4.49  --comb_res_mult                         3
% 31.90/4.49  --comb_sup_mult                         2
% 31.90/4.49  --comb_inst_mult                        10
% 31.90/4.49  
% 31.90/4.49  ------ Debug Options
% 31.90/4.49  
% 31.90/4.49  --dbg_backtrace                         false
% 31.90/4.49  --dbg_dump_prop_clauses                 false
% 31.90/4.49  --dbg_dump_prop_clauses_file            -
% 31.90/4.49  --dbg_out_stat                          false
% 31.90/4.49  ------ Parsing...
% 31.90/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.90/4.49  
% 31.90/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 31.90/4.49  
% 31.90/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.90/4.49  
% 31.90/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.90/4.49  ------ Proving...
% 31.90/4.49  ------ Problem Properties 
% 31.90/4.49  
% 31.90/4.49  
% 31.90/4.49  clauses                                 14
% 31.90/4.49  conjectures                             2
% 31.90/4.49  EPR                                     3
% 31.90/4.49  Horn                                    14
% 31.90/4.49  unary                                   4
% 31.90/4.49  binary                                  4
% 31.90/4.49  lits                                    30
% 31.90/4.49  lits eq                                 3
% 31.90/4.49  fd_pure                                 0
% 31.90/4.49  fd_pseudo                               0
% 31.90/4.49  fd_cond                                 0
% 31.90/4.49  fd_pseudo_cond                          0
% 31.90/4.49  AC symbols                              0
% 31.90/4.49  
% 31.90/4.49  ------ Schedule dynamic 5 is on 
% 31.90/4.49  
% 31.90/4.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.90/4.49  
% 31.90/4.49  
% 31.90/4.49  ------ 
% 31.90/4.49  Current options:
% 31.90/4.49  ------ 
% 31.90/4.49  
% 31.90/4.49  ------ Input Options
% 31.90/4.49  
% 31.90/4.49  --out_options                           all
% 31.90/4.49  --tptp_safe_out                         true
% 31.90/4.49  --problem_path                          ""
% 31.90/4.49  --include_path                          ""
% 31.90/4.49  --clausifier                            res/vclausify_rel
% 31.90/4.49  --clausifier_options                    ""
% 31.90/4.49  --stdin                                 false
% 31.90/4.49  --stats_out                             all
% 31.90/4.49  
% 31.90/4.49  ------ General Options
% 31.90/4.49  
% 31.90/4.49  --fof                                   false
% 31.90/4.49  --time_out_real                         305.
% 31.90/4.49  --time_out_virtual                      -1.
% 31.90/4.49  --symbol_type_check                     false
% 31.90/4.49  --clausify_out                          false
% 31.90/4.49  --sig_cnt_out                           false
% 31.90/4.49  --trig_cnt_out                          false
% 31.90/4.49  --trig_cnt_out_tolerance                1.
% 31.90/4.49  --trig_cnt_out_sk_spl                   false
% 31.90/4.49  --abstr_cl_out                          false
% 31.90/4.49  
% 31.90/4.49  ------ Global Options
% 31.90/4.49  
% 31.90/4.49  --schedule                              default
% 31.90/4.49  --add_important_lit                     false
% 31.90/4.49  --prop_solver_per_cl                    1000
% 31.90/4.49  --min_unsat_core                        false
% 31.90/4.49  --soft_assumptions                      false
% 31.90/4.49  --soft_lemma_size                       3
% 31.90/4.49  --prop_impl_unit_size                   0
% 31.90/4.49  --prop_impl_unit                        []
% 31.90/4.49  --share_sel_clauses                     true
% 31.90/4.49  --reset_solvers                         false
% 31.90/4.49  --bc_imp_inh                            [conj_cone]
% 31.90/4.49  --conj_cone_tolerance                   3.
% 31.90/4.49  --extra_neg_conj                        none
% 31.90/4.49  --large_theory_mode                     true
% 31.90/4.49  --prolific_symb_bound                   200
% 31.90/4.49  --lt_threshold                          2000
% 31.90/4.49  --clause_weak_htbl                      true
% 31.90/4.49  --gc_record_bc_elim                     false
% 31.90/4.49  
% 31.90/4.49  ------ Preprocessing Options
% 31.90/4.49  
% 31.90/4.49  --preprocessing_flag                    true
% 31.90/4.49  --time_out_prep_mult                    0.1
% 31.90/4.49  --splitting_mode                        input
% 31.90/4.49  --splitting_grd                         true
% 31.90/4.49  --splitting_cvd                         false
% 31.90/4.49  --splitting_cvd_svl                     false
% 31.90/4.49  --splitting_nvd                         32
% 31.90/4.49  --sub_typing                            true
% 31.90/4.49  --prep_gs_sim                           true
% 31.90/4.49  --prep_unflatten                        true
% 31.90/4.49  --prep_res_sim                          true
% 31.90/4.49  --prep_upred                            true
% 31.90/4.49  --prep_sem_filter                       exhaustive
% 31.90/4.49  --prep_sem_filter_out                   false
% 31.90/4.49  --pred_elim                             true
% 31.90/4.49  --res_sim_input                         true
% 31.90/4.49  --eq_ax_congr_red                       true
% 31.90/4.49  --pure_diseq_elim                       true
% 31.90/4.49  --brand_transform                       false
% 31.90/4.49  --non_eq_to_eq                          false
% 31.90/4.49  --prep_def_merge                        true
% 31.90/4.49  --prep_def_merge_prop_impl              false
% 31.90/4.49  --prep_def_merge_mbd                    true
% 31.90/4.49  --prep_def_merge_tr_red                 false
% 31.90/4.49  --prep_def_merge_tr_cl                  false
% 31.90/4.49  --smt_preprocessing                     true
% 31.90/4.49  --smt_ac_axioms                         fast
% 31.90/4.49  --preprocessed_out                      false
% 31.90/4.49  --preprocessed_stats                    false
% 31.90/4.49  
% 31.90/4.49  ------ Abstraction refinement Options
% 31.90/4.49  
% 31.90/4.49  --abstr_ref                             []
% 31.90/4.49  --abstr_ref_prep                        false
% 31.90/4.49  --abstr_ref_until_sat                   false
% 31.90/4.49  --abstr_ref_sig_restrict                funpre
% 31.90/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.90/4.49  --abstr_ref_under                       []
% 31.90/4.49  
% 31.90/4.49  ------ SAT Options
% 31.90/4.49  
% 31.90/4.49  --sat_mode                              false
% 31.90/4.49  --sat_fm_restart_options                ""
% 31.90/4.49  --sat_gr_def                            false
% 31.90/4.49  --sat_epr_types                         true
% 31.90/4.49  --sat_non_cyclic_types                  false
% 31.90/4.49  --sat_finite_models                     false
% 31.90/4.49  --sat_fm_lemmas                         false
% 31.90/4.49  --sat_fm_prep                           false
% 31.90/4.49  --sat_fm_uc_incr                        true
% 31.90/4.49  --sat_out_model                         small
% 31.90/4.49  --sat_out_clauses                       false
% 31.90/4.49  
% 31.90/4.49  ------ QBF Options
% 31.90/4.49  
% 31.90/4.49  --qbf_mode                              false
% 31.90/4.49  --qbf_elim_univ                         false
% 31.90/4.49  --qbf_dom_inst                          none
% 31.90/4.49  --qbf_dom_pre_inst                      false
% 31.90/4.49  --qbf_sk_in                             false
% 31.90/4.49  --qbf_pred_elim                         true
% 31.90/4.49  --qbf_split                             512
% 31.90/4.49  
% 31.90/4.49  ------ BMC1 Options
% 31.90/4.49  
% 31.90/4.49  --bmc1_incremental                      false
% 31.90/4.49  --bmc1_axioms                           reachable_all
% 31.90/4.49  --bmc1_min_bound                        0
% 31.90/4.49  --bmc1_max_bound                        -1
% 31.90/4.49  --bmc1_max_bound_default                -1
% 31.90/4.49  --bmc1_symbol_reachability              true
% 31.90/4.49  --bmc1_property_lemmas                  false
% 31.90/4.49  --bmc1_k_induction                      false
% 31.90/4.49  --bmc1_non_equiv_states                 false
% 31.90/4.49  --bmc1_deadlock                         false
% 31.90/4.49  --bmc1_ucm                              false
% 31.90/4.49  --bmc1_add_unsat_core                   none
% 31.90/4.49  --bmc1_unsat_core_children              false
% 31.90/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.90/4.49  --bmc1_out_stat                         full
% 31.90/4.49  --bmc1_ground_init                      false
% 31.90/4.49  --bmc1_pre_inst_next_state              false
% 31.90/4.49  --bmc1_pre_inst_state                   false
% 31.90/4.49  --bmc1_pre_inst_reach_state             false
% 31.90/4.49  --bmc1_out_unsat_core                   false
% 31.90/4.49  --bmc1_aig_witness_out                  false
% 31.90/4.49  --bmc1_verbose                          false
% 31.90/4.49  --bmc1_dump_clauses_tptp                false
% 31.90/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.90/4.49  --bmc1_dump_file                        -
% 31.90/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.90/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.90/4.49  --bmc1_ucm_extend_mode                  1
% 31.90/4.49  --bmc1_ucm_init_mode                    2
% 31.90/4.49  --bmc1_ucm_cone_mode                    none
% 31.90/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.90/4.49  --bmc1_ucm_relax_model                  4
% 31.90/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.90/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.90/4.49  --bmc1_ucm_layered_model                none
% 31.90/4.49  --bmc1_ucm_max_lemma_size               10
% 31.90/4.49  
% 31.90/4.49  ------ AIG Options
% 31.90/4.49  
% 31.90/4.49  --aig_mode                              false
% 31.90/4.49  
% 31.90/4.49  ------ Instantiation Options
% 31.90/4.49  
% 31.90/4.49  --instantiation_flag                    true
% 31.90/4.49  --inst_sos_flag                         true
% 31.90/4.49  --inst_sos_phase                        true
% 31.90/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.90/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.90/4.49  --inst_lit_sel_side                     none
% 31.90/4.49  --inst_solver_per_active                1400
% 31.90/4.49  --inst_solver_calls_frac                1.
% 31.90/4.49  --inst_passive_queue_type               priority_queues
% 31.90/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.90/4.49  --inst_passive_queues_freq              [25;2]
% 31.90/4.49  --inst_dismatching                      true
% 31.90/4.49  --inst_eager_unprocessed_to_passive     true
% 31.90/4.49  --inst_prop_sim_given                   true
% 31.90/4.49  --inst_prop_sim_new                     false
% 31.90/4.49  --inst_subs_new                         false
% 31.90/4.49  --inst_eq_res_simp                      false
% 31.90/4.49  --inst_subs_given                       false
% 31.90/4.49  --inst_orphan_elimination               true
% 31.90/4.49  --inst_learning_loop_flag               true
% 31.90/4.49  --inst_learning_start                   3000
% 31.90/4.49  --inst_learning_factor                  2
% 31.90/4.49  --inst_start_prop_sim_after_learn       3
% 31.90/4.49  --inst_sel_renew                        solver
% 31.90/4.49  --inst_lit_activity_flag                true
% 31.90/4.49  --inst_restr_to_given                   false
% 31.90/4.49  --inst_activity_threshold               500
% 31.90/4.49  --inst_out_proof                        true
% 31.90/4.49  
% 31.90/4.49  ------ Resolution Options
% 31.90/4.49  
% 31.90/4.49  --resolution_flag                       false
% 31.90/4.49  --res_lit_sel                           adaptive
% 31.90/4.49  --res_lit_sel_side                      none
% 31.90/4.49  --res_ordering                          kbo
% 31.90/4.49  --res_to_prop_solver                    active
% 31.90/4.49  --res_prop_simpl_new                    false
% 31.90/4.49  --res_prop_simpl_given                  true
% 31.90/4.49  --res_passive_queue_type                priority_queues
% 31.90/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.90/4.49  --res_passive_queues_freq               [15;5]
% 31.90/4.49  --res_forward_subs                      full
% 31.90/4.49  --res_backward_subs                     full
% 31.90/4.49  --res_forward_subs_resolution           true
% 31.90/4.49  --res_backward_subs_resolution          true
% 31.90/4.49  --res_orphan_elimination                true
% 31.90/4.49  --res_time_limit                        2.
% 31.90/4.49  --res_out_proof                         true
% 31.90/4.49  
% 31.90/4.49  ------ Superposition Options
% 31.90/4.49  
% 31.90/4.49  --superposition_flag                    true
% 31.90/4.49  --sup_passive_queue_type                priority_queues
% 31.90/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.90/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.90/4.49  --demod_completeness_check              fast
% 31.90/4.49  --demod_use_ground                      true
% 31.90/4.49  --sup_to_prop_solver                    passive
% 31.90/4.49  --sup_prop_simpl_new                    true
% 31.90/4.49  --sup_prop_simpl_given                  true
% 31.90/4.49  --sup_fun_splitting                     true
% 31.90/4.49  --sup_smt_interval                      50000
% 31.90/4.49  
% 31.90/4.49  ------ Superposition Simplification Setup
% 31.90/4.49  
% 31.90/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.90/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.90/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.90/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.90/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.90/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.90/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.90/4.49  --sup_immed_triv                        [TrivRules]
% 31.90/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.90/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.90/4.49  --sup_immed_bw_main                     []
% 31.90/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.90/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.90/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.90/4.49  --sup_input_bw                          []
% 31.90/4.49  
% 31.90/4.49  ------ Combination Options
% 31.90/4.49  
% 31.90/4.49  --comb_res_mult                         3
% 31.90/4.49  --comb_sup_mult                         2
% 31.90/4.49  --comb_inst_mult                        10
% 31.90/4.49  
% 31.90/4.49  ------ Debug Options
% 31.90/4.49  
% 31.90/4.49  --dbg_backtrace                         false
% 31.90/4.49  --dbg_dump_prop_clauses                 false
% 31.90/4.49  --dbg_dump_prop_clauses_file            -
% 31.90/4.49  --dbg_out_stat                          false
% 31.90/4.49  
% 31.90/4.49  
% 31.90/4.49  
% 31.90/4.49  
% 31.90/4.49  ------ Proving...
% 31.90/4.49  
% 31.90/4.49  
% 31.90/4.49  % SZS status Theorem for theBenchmark.p
% 31.90/4.49  
% 31.90/4.49   Resolution empty clause
% 31.90/4.49  
% 31.90/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.90/4.49  
% 31.90/4.49  fof(f2,axiom,(
% 31.90/4.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 31.90/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.49  
% 31.90/4.49  fof(f36,plain,(
% 31.90/4.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 31.90/4.49    inference(cnf_transformation,[],[f2])).
% 31.90/4.49  
% 31.90/4.49  fof(f7,axiom,(
% 31.90/4.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 31.90/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.49  
% 31.90/4.49  fof(f41,plain,(
% 31.90/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 31.90/4.49    inference(cnf_transformation,[],[f7])).
% 31.90/4.49  
% 31.90/4.49  fof(f5,axiom,(
% 31.90/4.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 31.90/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.49  
% 31.90/4.49  fof(f39,plain,(
% 31.90/4.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 31.90/4.49    inference(cnf_transformation,[],[f5])).
% 31.90/4.49  
% 31.90/4.49  fof(f6,axiom,(
% 31.90/4.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 31.90/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.49  
% 31.90/4.49  fof(f40,plain,(
% 31.90/4.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 31.90/4.49    inference(cnf_transformation,[],[f6])).
% 31.90/4.49  
% 31.90/4.49  fof(f54,plain,(
% 31.90/4.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 31.90/4.49    inference(definition_unfolding,[],[f39,f40])).
% 31.90/4.49  
% 31.90/4.49  fof(f55,plain,(
% 31.90/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 31.90/4.49    inference(definition_unfolding,[],[f41,f54])).
% 31.90/4.49  
% 31.90/4.49  fof(f57,plain,(
% 31.90/4.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 31.90/4.49    inference(definition_unfolding,[],[f36,f55])).
% 31.90/4.49  
% 31.90/4.49  fof(f1,axiom,(
% 31.90/4.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 31.90/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.49  
% 31.90/4.49  fof(f35,plain,(
% 31.90/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 31.90/4.49    inference(cnf_transformation,[],[f1])).
% 31.90/4.49  
% 31.90/4.49  fof(f56,plain,(
% 31.90/4.49    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 31.90/4.49    inference(definition_unfolding,[],[f35,f55,f55])).
% 31.90/4.49  
% 31.90/4.49  fof(f16,conjecture,(
% 31.90/4.49    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 31.90/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.49  
% 31.90/4.49  fof(f17,negated_conjecture,(
% 31.90/4.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 31.90/4.49    inference(negated_conjecture,[],[f16])).
% 31.90/4.49  
% 31.90/4.49  fof(f31,plain,(
% 31.90/4.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 31.90/4.49    inference(ennf_transformation,[],[f17])).
% 31.90/4.49  
% 31.90/4.49  fof(f33,plain,(
% 31.90/4.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 31.90/4.49    introduced(choice_axiom,[])).
% 31.90/4.49  
% 31.90/4.49  fof(f34,plain,(
% 31.90/4.49    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 31.90/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f33])).
% 31.90/4.49  
% 31.90/4.49  fof(f52,plain,(
% 31.90/4.49    v1_relat_1(sK2)),
% 31.90/4.49    inference(cnf_transformation,[],[f34])).
% 31.90/4.49  
% 31.90/4.49  fof(f10,axiom,(
% 31.90/4.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 31.90/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.49  
% 31.90/4.49  fof(f23,plain,(
% 31.90/4.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 31.90/4.49    inference(ennf_transformation,[],[f10])).
% 31.90/4.49  
% 31.90/4.49  fof(f45,plain,(
% 31.90/4.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 31.90/4.49    inference(cnf_transformation,[],[f23])).
% 31.90/4.49  
% 31.90/4.49  fof(f13,axiom,(
% 31.90/4.49    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 31.90/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.49  
% 31.90/4.49  fof(f27,plain,(
% 31.90/4.49    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 31.90/4.49    inference(ennf_transformation,[],[f13])).
% 31.90/4.49  
% 31.90/4.49  fof(f48,plain,(
% 31.90/4.49    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 31.90/4.49    inference(cnf_transformation,[],[f27])).
% 31.90/4.49  
% 31.90/4.49  fof(f14,axiom,(
% 31.90/4.49    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 31.90/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.49  
% 31.90/4.49  fof(f28,plain,(
% 31.90/4.49    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 31.90/4.49    inference(ennf_transformation,[],[f14])).
% 31.90/4.49  
% 31.90/4.49  fof(f49,plain,(
% 31.90/4.49    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 31.90/4.49    inference(cnf_transformation,[],[f28])).
% 31.90/4.49  
% 31.90/4.49  fof(f12,axiom,(
% 31.90/4.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 31.90/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.49  
% 31.90/4.49  fof(f26,plain,(
% 31.90/4.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 31.90/4.49    inference(ennf_transformation,[],[f12])).
% 31.90/4.49  
% 31.90/4.49  fof(f47,plain,(
% 31.90/4.49    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 31.90/4.49    inference(cnf_transformation,[],[f26])).
% 31.90/4.49  
% 31.90/4.49  fof(f11,axiom,(
% 31.90/4.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))))),
% 31.90/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.49  
% 31.90/4.49  fof(f24,plain,(
% 31.90/4.49    ! [X0,X1,X2] : ((r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 31.90/4.49    inference(ennf_transformation,[],[f11])).
% 31.90/4.49  
% 31.90/4.49  fof(f25,plain,(
% 31.90/4.49    ! [X0,X1,X2] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 31.90/4.49    inference(flattening,[],[f24])).
% 31.90/4.49  
% 31.90/4.49  fof(f46,plain,(
% 31.90/4.49    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 31.90/4.49    inference(cnf_transformation,[],[f25])).
% 31.90/4.49  
% 31.90/4.49  fof(f15,axiom,(
% 31.90/4.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 31.90/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.49  
% 31.90/4.49  fof(f29,plain,(
% 31.90/4.49    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.90/4.49    inference(ennf_transformation,[],[f15])).
% 31.90/4.49  
% 31.90/4.49  fof(f30,plain,(
% 31.90/4.49    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.90/4.49    inference(flattening,[],[f29])).
% 31.90/4.49  
% 31.90/4.49  fof(f51,plain,(
% 31.90/4.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 31.90/4.49    inference(cnf_transformation,[],[f30])).
% 31.90/4.49  
% 31.90/4.49  fof(f9,axiom,(
% 31.90/4.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 31.90/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.49  
% 31.90/4.49  fof(f22,plain,(
% 31.90/4.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 31.90/4.49    inference(ennf_transformation,[],[f9])).
% 31.90/4.49  
% 31.90/4.49  fof(f44,plain,(
% 31.90/4.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 31.90/4.49    inference(cnf_transformation,[],[f22])).
% 31.90/4.49  
% 31.90/4.49  fof(f8,axiom,(
% 31.90/4.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.90/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.49  
% 31.90/4.49  fof(f32,plain,(
% 31.90/4.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.90/4.49    inference(nnf_transformation,[],[f8])).
% 31.90/4.49  
% 31.90/4.49  fof(f43,plain,(
% 31.90/4.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.90/4.49    inference(cnf_transformation,[],[f32])).
% 31.90/4.49  
% 31.90/4.49  fof(f4,axiom,(
% 31.90/4.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 31.90/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.49  
% 31.90/4.49  fof(f20,plain,(
% 31.90/4.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 31.90/4.49    inference(ennf_transformation,[],[f4])).
% 31.90/4.49  
% 31.90/4.49  fof(f21,plain,(
% 31.90/4.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 31.90/4.49    inference(flattening,[],[f20])).
% 31.90/4.49  
% 31.90/4.49  fof(f38,plain,(
% 31.90/4.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 31.90/4.49    inference(cnf_transformation,[],[f21])).
% 31.90/4.49  
% 31.90/4.49  fof(f3,axiom,(
% 31.90/4.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 31.90/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.90/4.49  
% 31.90/4.49  fof(f18,plain,(
% 31.90/4.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 31.90/4.49    inference(ennf_transformation,[],[f3])).
% 31.90/4.49  
% 31.90/4.49  fof(f19,plain,(
% 31.90/4.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 31.90/4.49    inference(flattening,[],[f18])).
% 31.90/4.49  
% 31.90/4.49  fof(f37,plain,(
% 31.90/4.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 31.90/4.49    inference(cnf_transformation,[],[f19])).
% 31.90/4.49  
% 31.90/4.49  fof(f58,plain,(
% 31.90/4.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 31.90/4.49    inference(definition_unfolding,[],[f37,f55])).
% 31.90/4.49  
% 31.90/4.49  fof(f53,plain,(
% 31.90/4.49    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 31.90/4.49    inference(cnf_transformation,[],[f34])).
% 31.90/4.49  
% 31.90/4.49  fof(f59,plain,(
% 31.90/4.49    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 31.90/4.49    inference(definition_unfolding,[],[f53,f55,f55])).
% 31.90/4.49  
% 31.90/4.49  cnf(c_1,plain,
% 31.90/4.49      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
% 31.90/4.49      inference(cnf_transformation,[],[f57]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_317,plain,
% 31.90/4.49      ( r1_tarski(k1_setfam_1(k2_enumset1(X0_41,X0_41,X0_41,X1_41)),X0_41) ),
% 31.90/4.49      inference(subtyping,[status(esa)],[c_1]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_546,plain,
% 31.90/4.49      ( r1_tarski(k1_setfam_1(k2_enumset1(X0_41,X0_41,X0_41,X1_41)),X0_41) = iProver_top ),
% 31.90/4.49      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_0,plain,
% 31.90/4.49      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
% 31.90/4.49      inference(cnf_transformation,[],[f56]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_318,plain,
% 31.90/4.49      ( k1_setfam_1(k2_enumset1(X0_41,X0_41,X0_41,X1_41)) = k1_setfam_1(k2_enumset1(X1_41,X1_41,X1_41,X0_41)) ),
% 31.90/4.49      inference(subtyping,[status(esa)],[c_0]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_843,plain,
% 31.90/4.49      ( r1_tarski(k1_setfam_1(k2_enumset1(X0_41,X0_41,X0_41,X1_41)),X1_41) = iProver_top ),
% 31.90/4.49      inference(superposition,[status(thm)],[c_318,c_546]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_15,negated_conjecture,
% 31.90/4.49      ( v1_relat_1(sK2) ),
% 31.90/4.49      inference(cnf_transformation,[],[f52]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_308,negated_conjecture,
% 31.90/4.49      ( v1_relat_1(sK2) ),
% 31.90/4.49      inference(subtyping,[status(esa)],[c_15]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_555,plain,
% 31.90/4.49      ( v1_relat_1(sK2) = iProver_top ),
% 31.90/4.49      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_7,plain,
% 31.90/4.49      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 31.90/4.49      inference(cnf_transformation,[],[f45]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_314,plain,
% 31.90/4.49      ( ~ v1_relat_1(X0_41) | v1_relat_1(k7_relat_1(X0_41,X1_41)) ),
% 31.90/4.49      inference(subtyping,[status(esa)],[c_7]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_549,plain,
% 31.90/4.49      ( v1_relat_1(X0_41) != iProver_top
% 31.90/4.49      | v1_relat_1(k7_relat_1(X0_41,X1_41)) = iProver_top ),
% 31.90/4.49      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_10,plain,
% 31.90/4.49      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 31.90/4.49      inference(cnf_transformation,[],[f48]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_311,plain,
% 31.90/4.49      ( ~ v1_relat_1(X0_41)
% 31.90/4.49      | k9_relat_1(X0_41,k1_relat_1(X0_41)) = k2_relat_1(X0_41) ),
% 31.90/4.49      inference(subtyping,[status(esa)],[c_10]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_552,plain,
% 31.90/4.49      ( k9_relat_1(X0_41,k1_relat_1(X0_41)) = k2_relat_1(X0_41)
% 31.90/4.49      | v1_relat_1(X0_41) != iProver_top ),
% 31.90/4.49      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_908,plain,
% 31.90/4.49      ( k9_relat_1(k7_relat_1(X0_41,X1_41),k1_relat_1(k7_relat_1(X0_41,X1_41))) = k2_relat_1(k7_relat_1(X0_41,X1_41))
% 31.90/4.49      | v1_relat_1(X0_41) != iProver_top ),
% 31.90/4.49      inference(superposition,[status(thm)],[c_549,c_552]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_2389,plain,
% 31.90/4.49      ( k9_relat_1(k7_relat_1(sK2,X0_41),k1_relat_1(k7_relat_1(sK2,X0_41))) = k2_relat_1(k7_relat_1(sK2,X0_41)) ),
% 31.90/4.49      inference(superposition,[status(thm)],[c_555,c_908]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_11,plain,
% 31.90/4.49      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 31.90/4.49      inference(cnf_transformation,[],[f49]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_310,plain,
% 31.90/4.49      ( ~ v1_relat_1(X0_41)
% 31.90/4.49      | k2_relat_1(k7_relat_1(X0_41,X1_41)) = k9_relat_1(X0_41,X1_41) ),
% 31.90/4.49      inference(subtyping,[status(esa)],[c_11]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_553,plain,
% 31.90/4.49      ( k2_relat_1(k7_relat_1(X0_41,X1_41)) = k9_relat_1(X0_41,X1_41)
% 31.90/4.49      | v1_relat_1(X0_41) != iProver_top ),
% 31.90/4.49      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_1048,plain,
% 31.90/4.49      ( k2_relat_1(k7_relat_1(sK2,X0_41)) = k9_relat_1(sK2,X0_41) ),
% 31.90/4.49      inference(superposition,[status(thm)],[c_555,c_553]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_2395,plain,
% 31.90/4.49      ( k9_relat_1(k7_relat_1(sK2,X0_41),k1_relat_1(k7_relat_1(sK2,X0_41))) = k9_relat_1(sK2,X0_41) ),
% 31.90/4.49      inference(light_normalisation,[status(thm)],[c_2389,c_1048]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_9,plain,
% 31.90/4.49      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 31.90/4.49      inference(cnf_transformation,[],[f47]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_312,plain,
% 31.90/4.49      ( r1_tarski(k9_relat_1(X0_41,X1_41),k2_relat_1(X0_41))
% 31.90/4.49      | ~ v1_relat_1(X0_41) ),
% 31.90/4.49      inference(subtyping,[status(esa)],[c_9]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_551,plain,
% 31.90/4.49      ( r1_tarski(k9_relat_1(X0_41,X1_41),k2_relat_1(X0_41)) = iProver_top
% 31.90/4.49      | v1_relat_1(X0_41) != iProver_top ),
% 31.90/4.49      inference(predicate_to_equality,[status(thm)],[c_312]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_1118,plain,
% 31.90/4.49      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_41),X1_41),k9_relat_1(sK2,X0_41)) = iProver_top
% 31.90/4.49      | v1_relat_1(k7_relat_1(sK2,X0_41)) != iProver_top ),
% 31.90/4.49      inference(superposition,[status(thm)],[c_1048,c_551]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_2467,plain,
% 31.90/4.49      ( r1_tarski(k9_relat_1(sK2,X0_41),k9_relat_1(sK2,X0_41)) = iProver_top
% 31.90/4.49      | v1_relat_1(k7_relat_1(sK2,X0_41)) != iProver_top ),
% 31.90/4.49      inference(superposition,[status(thm)],[c_2395,c_1118]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_16,plain,
% 31.90/4.49      ( v1_relat_1(sK2) = iProver_top ),
% 31.90/4.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_4537,plain,
% 31.90/4.49      ( v1_relat_1(k7_relat_1(sK2,X0_41)) | ~ v1_relat_1(sK2) ),
% 31.90/4.49      inference(instantiation,[status(thm)],[c_314]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_4538,plain,
% 31.90/4.49      ( v1_relat_1(k7_relat_1(sK2,X0_41)) = iProver_top
% 31.90/4.49      | v1_relat_1(sK2) != iProver_top ),
% 31.90/4.49      inference(predicate_to_equality,[status(thm)],[c_4537]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_10350,plain,
% 31.90/4.49      ( r1_tarski(k9_relat_1(sK2,X0_41),k9_relat_1(sK2,X0_41)) = iProver_top ),
% 31.90/4.49      inference(global_propositional_subsumption,
% 31.90/4.49                [status(thm)],
% 31.90/4.49                [c_2467,c_16,c_4538]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_8,plain,
% 31.90/4.49      ( ~ r1_tarski(X0,X1)
% 31.90/4.49      | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
% 31.90/4.49      | ~ v1_relat_1(X2) ),
% 31.90/4.49      inference(cnf_transformation,[],[f46]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_313,plain,
% 31.90/4.49      ( ~ r1_tarski(X0_41,X1_41)
% 31.90/4.49      | r1_tarski(k7_relat_1(X2_41,X0_41),k7_relat_1(X2_41,X1_41))
% 31.90/4.49      | ~ v1_relat_1(X2_41) ),
% 31.90/4.49      inference(subtyping,[status(esa)],[c_8]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_550,plain,
% 31.90/4.49      ( r1_tarski(X0_41,X1_41) != iProver_top
% 31.90/4.49      | r1_tarski(k7_relat_1(X2_41,X0_41),k7_relat_1(X2_41,X1_41)) = iProver_top
% 31.90/4.49      | v1_relat_1(X2_41) != iProver_top ),
% 31.90/4.49      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_12,plain,
% 31.90/4.49      ( ~ r1_tarski(X0,X1)
% 31.90/4.49      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 31.90/4.49      | ~ v1_relat_1(X0)
% 31.90/4.49      | ~ v1_relat_1(X1) ),
% 31.90/4.49      inference(cnf_transformation,[],[f51]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_6,plain,
% 31.90/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 31.90/4.49      inference(cnf_transformation,[],[f44]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_4,plain,
% 31.90/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.90/4.49      inference(cnf_transformation,[],[f43]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_92,plain,
% 31.90/4.49      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 31.90/4.49      | ~ r1_tarski(X0,X1)
% 31.90/4.49      | ~ v1_relat_1(X1) ),
% 31.90/4.49      inference(global_propositional_subsumption,[status(thm)],[c_12,c_6,c_4]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_93,plain,
% 31.90/4.49      ( ~ r1_tarski(X0,X1)
% 31.90/4.49      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 31.90/4.49      | ~ v1_relat_1(X1) ),
% 31.90/4.49      inference(renaming,[status(thm)],[c_92]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_306,plain,
% 31.90/4.49      ( ~ r1_tarski(X0_41,X1_41)
% 31.90/4.49      | r1_tarski(k2_relat_1(X0_41),k2_relat_1(X1_41))
% 31.90/4.49      | ~ v1_relat_1(X1_41) ),
% 31.90/4.49      inference(subtyping,[status(esa)],[c_93]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_557,plain,
% 31.90/4.49      ( r1_tarski(X0_41,X1_41) != iProver_top
% 31.90/4.49      | r1_tarski(k2_relat_1(X0_41),k2_relat_1(X1_41)) = iProver_top
% 31.90/4.49      | v1_relat_1(X1_41) != iProver_top ),
% 31.90/4.49      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_2188,plain,
% 31.90/4.49      ( r1_tarski(k9_relat_1(sK2,X0_41),k2_relat_1(X1_41)) = iProver_top
% 31.90/4.49      | r1_tarski(k7_relat_1(sK2,X0_41),X1_41) != iProver_top
% 31.90/4.49      | v1_relat_1(X1_41) != iProver_top ),
% 31.90/4.49      inference(superposition,[status(thm)],[c_1048,c_557]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_3,plain,
% 31.90/4.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 31.90/4.49      inference(cnf_transformation,[],[f38]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_315,plain,
% 31.90/4.49      ( ~ r1_tarski(X0_41,X1_41)
% 31.90/4.49      | ~ r1_tarski(X1_41,X2_41)
% 31.90/4.49      | r1_tarski(X0_41,X2_41) ),
% 31.90/4.49      inference(subtyping,[status(esa)],[c_3]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_548,plain,
% 31.90/4.49      ( r1_tarski(X0_41,X1_41) != iProver_top
% 31.90/4.49      | r1_tarski(X1_41,X2_41) != iProver_top
% 31.90/4.49      | r1_tarski(X0_41,X2_41) = iProver_top ),
% 31.90/4.49      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_2483,plain,
% 31.90/4.49      ( r1_tarski(k9_relat_1(sK2,X0_41),X1_41) = iProver_top
% 31.90/4.49      | r1_tarski(k7_relat_1(sK2,X0_41),X2_41) != iProver_top
% 31.90/4.49      | r1_tarski(k2_relat_1(X2_41),X1_41) != iProver_top
% 31.90/4.49      | v1_relat_1(X2_41) != iProver_top ),
% 31.90/4.49      inference(superposition,[status(thm)],[c_2188,c_548]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_19834,plain,
% 31.90/4.49      ( r1_tarski(X0_41,X1_41) != iProver_top
% 31.90/4.49      | r1_tarski(k9_relat_1(sK2,X0_41),X2_41) = iProver_top
% 31.90/4.49      | r1_tarski(k2_relat_1(k7_relat_1(sK2,X1_41)),X2_41) != iProver_top
% 31.90/4.49      | v1_relat_1(k7_relat_1(sK2,X1_41)) != iProver_top
% 31.90/4.49      | v1_relat_1(sK2) != iProver_top ),
% 31.90/4.49      inference(superposition,[status(thm)],[c_550,c_2483]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_19836,plain,
% 31.90/4.49      ( r1_tarski(X0_41,X1_41) != iProver_top
% 31.90/4.49      | r1_tarski(k9_relat_1(sK2,X1_41),X2_41) != iProver_top
% 31.90/4.49      | r1_tarski(k9_relat_1(sK2,X0_41),X2_41) = iProver_top
% 31.90/4.49      | v1_relat_1(k7_relat_1(sK2,X1_41)) != iProver_top
% 31.90/4.49      | v1_relat_1(sK2) != iProver_top ),
% 31.90/4.49      inference(demodulation,[status(thm)],[c_19834,c_1048]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_20177,plain,
% 31.90/4.49      ( v1_relat_1(k7_relat_1(sK2,X1_41)) != iProver_top
% 31.90/4.49      | r1_tarski(k9_relat_1(sK2,X0_41),X2_41) = iProver_top
% 31.90/4.49      | r1_tarski(k9_relat_1(sK2,X1_41),X2_41) != iProver_top
% 31.90/4.49      | r1_tarski(X0_41,X1_41) != iProver_top ),
% 31.90/4.49      inference(global_propositional_subsumption,[status(thm)],[c_19836,c_16]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_20178,plain,
% 31.90/4.49      ( r1_tarski(X0_41,X1_41) != iProver_top
% 31.90/4.49      | r1_tarski(k9_relat_1(sK2,X1_41),X2_41) != iProver_top
% 31.90/4.49      | r1_tarski(k9_relat_1(sK2,X0_41),X2_41) = iProver_top
% 31.90/4.49      | v1_relat_1(k7_relat_1(sK2,X1_41)) != iProver_top ),
% 31.90/4.49      inference(renaming,[status(thm)],[c_20177]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_20185,plain,
% 31.90/4.49      ( r1_tarski(X0_41,X1_41) != iProver_top
% 31.90/4.49      | r1_tarski(k9_relat_1(sK2,X0_41),k9_relat_1(sK2,X1_41)) = iProver_top
% 31.90/4.49      | v1_relat_1(k7_relat_1(sK2,X1_41)) != iProver_top ),
% 31.90/4.49      inference(superposition,[status(thm)],[c_10350,c_20178]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_2,plain,
% 31.90/4.49      ( ~ r1_tarski(X0,X1)
% 31.90/4.49      | ~ r1_tarski(X0,X2)
% 31.90/4.49      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
% 31.90/4.49      inference(cnf_transformation,[],[f58]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_316,plain,
% 31.90/4.49      ( ~ r1_tarski(X0_41,X1_41)
% 31.90/4.49      | ~ r1_tarski(X0_41,X2_41)
% 31.90/4.49      | r1_tarski(X0_41,k1_setfam_1(k2_enumset1(X2_41,X2_41,X2_41,X1_41))) ),
% 31.90/4.49      inference(subtyping,[status(esa)],[c_2]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_547,plain,
% 31.90/4.49      ( r1_tarski(X0_41,X1_41) != iProver_top
% 31.90/4.49      | r1_tarski(X0_41,X2_41) != iProver_top
% 31.90/4.49      | r1_tarski(X0_41,k1_setfam_1(k2_enumset1(X2_41,X2_41,X2_41,X1_41))) = iProver_top ),
% 31.90/4.49      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_14,negated_conjecture,
% 31.90/4.49      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
% 31.90/4.49      inference(cnf_transformation,[],[f59]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_309,negated_conjecture,
% 31.90/4.49      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
% 31.90/4.49      inference(subtyping,[status(esa)],[c_14]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_554,plain,
% 31.90/4.49      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) != iProver_top ),
% 31.90/4.49      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_983,plain,
% 31.90/4.49      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) != iProver_top
% 31.90/4.49      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) != iProver_top ),
% 31.90/4.49      inference(superposition,[status(thm)],[c_547,c_554]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_20331,plain,
% 31.90/4.49      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) != iProver_top
% 31.90/4.49      | r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) != iProver_top
% 31.90/4.49      | v1_relat_1(k7_relat_1(sK2,sK1)) != iProver_top ),
% 31.90/4.49      inference(superposition,[status(thm)],[c_20185,c_983]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_9974,plain,
% 31.90/4.49      ( v1_relat_1(k7_relat_1(sK2,sK1)) | ~ v1_relat_1(sK2) ),
% 31.90/4.49      inference(instantiation,[status(thm)],[c_4537]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_9975,plain,
% 31.90/4.49      ( v1_relat_1(k7_relat_1(sK2,sK1)) = iProver_top
% 31.90/4.49      | v1_relat_1(sK2) != iProver_top ),
% 31.90/4.49      inference(predicate_to_equality,[status(thm)],[c_9974]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_20469,plain,
% 31.90/4.49      ( r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) != iProver_top
% 31.90/4.49      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) != iProver_top ),
% 31.90/4.49      inference(global_propositional_subsumption,
% 31.90/4.49                [status(thm)],
% 31.90/4.49                [c_20331,c_16,c_9975]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_20470,plain,
% 31.90/4.49      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) != iProver_top
% 31.90/4.49      | r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) != iProver_top ),
% 31.90/4.49      inference(renaming,[status(thm)],[c_20469]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_20475,plain,
% 31.90/4.49      ( r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) != iProver_top
% 31.90/4.49      | r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) != iProver_top
% 31.90/4.49      | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
% 31.90/4.49      inference(superposition,[status(thm)],[c_20185,c_20470]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_4540,plain,
% 31.90/4.49      ( v1_relat_1(k7_relat_1(sK2,sK0)) = iProver_top
% 31.90/4.49      | v1_relat_1(sK2) != iProver_top ),
% 31.90/4.49      inference(instantiation,[status(thm)],[c_4538]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_61977,plain,
% 31.90/4.49      ( r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) != iProver_top
% 31.90/4.49      | r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) != iProver_top ),
% 31.90/4.49      inference(global_propositional_subsumption,
% 31.90/4.49                [status(thm)],
% 31.90/4.49                [c_20475,c_16,c_4540]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_61978,plain,
% 31.90/4.49      ( r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) != iProver_top
% 31.90/4.49      | r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) != iProver_top ),
% 31.90/4.49      inference(renaming,[status(thm)],[c_61977]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_61981,plain,
% 31.90/4.49      ( r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) != iProver_top ),
% 31.90/4.49      inference(superposition,[status(thm)],[c_843,c_61978]) ).
% 31.90/4.49  
% 31.90/4.49  cnf(c_89677,plain,
% 31.90/4.49      ( $false ),
% 31.90/4.49      inference(superposition,[status(thm)],[c_546,c_61981]) ).
% 31.90/4.49  
% 31.90/4.49  
% 31.90/4.49  % SZS output end CNFRefutation for theBenchmark.p
% 31.90/4.49  
% 31.90/4.49  ------                               Statistics
% 31.90/4.49  
% 31.90/4.49  ------ General
% 31.90/4.49  
% 31.90/4.49  abstr_ref_over_cycles:                  0
% 31.90/4.49  abstr_ref_under_cycles:                 0
% 31.90/4.49  gc_basic_clause_elim:                   0
% 31.90/4.49  forced_gc_time:                         0
% 31.90/4.49  parsing_time:                           0.009
% 31.90/4.49  unif_index_cands_time:                  0.
% 31.90/4.49  unif_index_add_time:                    0.
% 31.90/4.49  orderings_time:                         0.
% 31.90/4.49  out_proof_time:                         0.015
% 31.90/4.49  total_time:                             3.954
% 31.90/4.49  num_of_symbols:                         46
% 31.90/4.49  num_of_terms:                           80217
% 31.90/4.49  
% 31.90/4.49  ------ Preprocessing
% 31.90/4.49  
% 31.90/4.49  num_of_splits:                          0
% 31.90/4.49  num_of_split_atoms:                     0
% 31.90/4.49  num_of_reused_defs:                     0
% 31.90/4.49  num_eq_ax_congr_red:                    11
% 31.90/4.49  num_of_sem_filtered_clauses:            1
% 31.90/4.49  num_of_subtypes:                        2
% 31.90/4.49  monotx_restored_types:                  0
% 31.90/4.49  sat_num_of_epr_types:                   0
% 31.90/4.49  sat_num_of_non_cyclic_types:            0
% 31.90/4.49  sat_guarded_non_collapsed_types:        0
% 31.90/4.49  num_pure_diseq_elim:                    0
% 31.90/4.49  simp_replaced_by:                       0
% 31.90/4.49  res_preprocessed:                       77
% 31.90/4.49  prep_upred:                             0
% 31.90/4.49  prep_unflattend:                        0
% 31.90/4.49  smt_new_axioms:                         0
% 31.90/4.49  pred_elim_cands:                        2
% 31.90/4.49  pred_elim:                              1
% 31.90/4.49  pred_elim_cl:                           2
% 31.90/4.49  pred_elim_cycles:                       3
% 31.90/4.49  merged_defs:                            2
% 31.90/4.49  merged_defs_ncl:                        0
% 31.90/4.49  bin_hyper_res:                          3
% 31.90/4.49  prep_cycles:                            4
% 31.90/4.49  pred_elim_time:                         0.001
% 31.90/4.49  splitting_time:                         0.
% 31.90/4.49  sem_filter_time:                        0.
% 31.90/4.49  monotx_time:                            0.
% 31.90/4.49  subtype_inf_time:                       0.
% 31.90/4.49  
% 31.90/4.49  ------ Problem properties
% 31.90/4.49  
% 31.90/4.49  clauses:                                14
% 31.90/4.49  conjectures:                            2
% 31.90/4.49  epr:                                    3
% 31.90/4.49  horn:                                   14
% 31.90/4.49  ground:                                 2
% 31.90/4.49  unary:                                  4
% 31.90/4.49  binary:                                 4
% 31.90/4.49  lits:                                   30
% 31.90/4.49  lits_eq:                                3
% 31.90/4.49  fd_pure:                                0
% 31.90/4.49  fd_pseudo:                              0
% 31.90/4.49  fd_cond:                                0
% 31.90/4.49  fd_pseudo_cond:                         0
% 31.90/4.49  ac_symbols:                             0
% 31.90/4.49  
% 31.90/4.49  ------ Propositional Solver
% 31.90/4.49  
% 31.90/4.49  prop_solver_calls:                      47
% 31.90/4.49  prop_fast_solver_calls:                 2560
% 31.90/4.49  smt_solver_calls:                       0
% 31.90/4.49  smt_fast_solver_calls:                  0
% 31.90/4.49  prop_num_of_clauses:                    35986
% 31.90/4.49  prop_preprocess_simplified:             35837
% 31.90/4.49  prop_fo_subsumed:                       102
% 31.90/4.49  prop_solver_time:                       0.
% 31.90/4.49  smt_solver_time:                        0.
% 31.90/4.49  smt_fast_solver_time:                   0.
% 31.90/4.49  prop_fast_solver_time:                  0.
% 31.90/4.49  prop_unsat_core_time:                   0.
% 31.90/4.49  
% 31.90/4.49  ------ QBF
% 31.90/4.49  
% 31.90/4.49  qbf_q_res:                              0
% 31.90/4.49  qbf_num_tautologies:                    0
% 31.90/4.49  qbf_prep_cycles:                        0
% 31.90/4.49  
% 31.90/4.49  ------ BMC1
% 31.90/4.49  
% 31.90/4.49  bmc1_current_bound:                     -1
% 31.90/4.49  bmc1_last_solved_bound:                 -1
% 31.90/4.49  bmc1_unsat_core_size:                   -1
% 31.90/4.49  bmc1_unsat_core_parents_size:           -1
% 31.90/4.49  bmc1_merge_next_fun:                    0
% 31.90/4.49  bmc1_unsat_core_clauses_time:           0.
% 31.90/4.49  
% 31.90/4.49  ------ Instantiation
% 31.90/4.49  
% 31.90/4.49  inst_num_of_clauses:                    477
% 31.90/4.49  inst_num_in_passive:                    75
% 31.90/4.49  inst_num_in_active:                     2977
% 31.90/4.49  inst_num_in_unprocessed:                158
% 31.90/4.49  inst_num_of_loops:                      3249
% 31.90/4.49  inst_num_of_learning_restarts:          1
% 31.90/4.49  inst_num_moves_active_passive:          261
% 31.90/4.49  inst_lit_activity:                      0
% 31.90/4.49  inst_lit_activity_moves:                2
% 31.90/4.49  inst_num_tautologies:                   0
% 31.90/4.49  inst_num_prop_implied:                  0
% 31.90/4.49  inst_num_existing_simplified:           0
% 31.90/4.49  inst_num_eq_res_simplified:             0
% 31.90/4.49  inst_num_child_elim:                    0
% 31.90/4.49  inst_num_of_dismatching_blockings:      23793
% 31.90/4.49  inst_num_of_non_proper_insts:           11160
% 31.90/4.49  inst_num_of_duplicates:                 0
% 31.90/4.49  inst_inst_num_from_inst_to_res:         0
% 31.90/4.49  inst_dismatching_checking_time:         0.
% 31.90/4.49  
% 31.90/4.49  ------ Resolution
% 31.90/4.49  
% 31.90/4.49  res_num_of_clauses:                     23
% 31.90/4.49  res_num_in_passive:                     23
% 31.90/4.49  res_num_in_active:                      0
% 31.90/4.49  res_num_of_loops:                       81
% 31.90/4.49  res_forward_subset_subsumed:            676
% 31.90/4.49  res_backward_subset_subsumed:           10
% 31.90/4.49  res_forward_subsumed:                   0
% 31.90/4.49  res_backward_subsumed:                  0
% 31.90/4.49  res_forward_subsumption_resolution:     0
% 31.90/4.49  res_backward_subsumption_resolution:    0
% 31.90/4.49  res_clause_to_clause_subsumption:       22696
% 31.90/4.49  res_orphan_elimination:                 0
% 31.90/4.49  res_tautology_del:                      1693
% 31.90/4.49  res_num_eq_res_simplified:              0
% 31.90/4.49  res_num_sel_changes:                    0
% 31.90/4.49  res_moves_from_active_to_pass:          0
% 31.90/4.49  
% 31.90/4.49  ------ Superposition
% 31.90/4.49  
% 31.90/4.49  sup_time_total:                         0.
% 31.90/4.49  sup_time_generating:                    0.
% 31.90/4.49  sup_time_sim_full:                      0.
% 31.90/4.49  sup_time_sim_immed:                     0.
% 31.90/4.49  
% 31.90/4.49  sup_num_of_clauses:                     3796
% 31.90/4.49  sup_num_in_active:                      592
% 31.90/4.49  sup_num_in_passive:                     3204
% 31.90/4.49  sup_num_of_loops:                       648
% 31.90/4.49  sup_fw_superposition:                   4773
% 31.90/4.49  sup_bw_superposition:                   2484
% 31.90/4.49  sup_immediate_simplified:               923
% 31.90/4.49  sup_given_eliminated:                   15
% 31.90/4.49  comparisons_done:                       0
% 31.90/4.49  comparisons_avoided:                    0
% 31.90/4.49  
% 31.90/4.49  ------ Simplifications
% 31.90/4.49  
% 31.90/4.49  
% 31.90/4.49  sim_fw_subset_subsumed:                 164
% 31.90/4.49  sim_bw_subset_subsumed:                 98
% 31.90/4.49  sim_fw_subsumed:                        308
% 31.90/4.49  sim_bw_subsumed:                        157
% 31.90/4.49  sim_fw_subsumption_res:                 0
% 31.90/4.49  sim_bw_subsumption_res:                 0
% 31.90/4.49  sim_tautology_del:                      116
% 31.90/4.49  sim_eq_tautology_del:                   1
% 31.90/4.49  sim_eq_res_simp:                        0
% 31.90/4.49  sim_fw_demodulated:                     120
% 31.90/4.49  sim_bw_demodulated:                     0
% 31.90/4.49  sim_light_normalised:                   295
% 31.90/4.49  sim_joinable_taut:                      0
% 31.90/4.49  sim_joinable_simp:                      0
% 31.90/4.49  sim_ac_normalised:                      0
% 31.90/4.49  sim_smt_subsumption:                    0
% 31.90/4.49  
%------------------------------------------------------------------------------
