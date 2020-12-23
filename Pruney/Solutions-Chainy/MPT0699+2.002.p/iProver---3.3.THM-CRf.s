%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:05 EST 2020

% Result     : Theorem 8.05s
% Output     : CNFRefutation 8.05s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 269 expanded)
%              Number of clauses        :   58 (  81 expanded)
%              Number of leaves         :   16 (  57 expanded)
%              Depth                    :   17
%              Number of atoms          :  265 ( 825 expanded)
%              Number of equality atoms :  127 ( 273 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f33,f34,f34])).

fof(f12,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f59,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).

fof(f52,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f36,f56])).

fof(f53,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f48,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_10,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_610,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_613,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2710,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_613])).

cnf(c_22039,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_610,c_2710])).

cnf(c_6,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_22063,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_22039,c_6])).

cnf(c_0,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_12,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_853,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_0,c_12])).

cnf(c_1065,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_853,c_6])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_607,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1))) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_616,plain,
    ( k9_relat_1(X0,k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1))) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2845,plain,
    ( k9_relat_1(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0))) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_607,c_616])).

cnf(c_3114,plain,
    ( k9_relat_1(sK1,k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(X0)))) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1065,c_2845])).

cnf(c_23580,plain,
    ( k9_relat_1(sK1,k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)) = k9_relat_1(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_22063,c_3114])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_608,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_611,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_614,plain,
    ( k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3473,plain,
    ( k10_relat_1(sK1,k10_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(sK1,X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_607,c_614])).

cnf(c_3786,plain,
    ( k10_relat_1(k5_relat_1(sK1,k2_funct_1(X0)),X1) = k10_relat_1(sK1,k10_relat_1(k2_funct_1(X0),X1))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_3473])).

cnf(c_4978,plain,
    ( k10_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0) = k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0))
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_608,c_3786])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_295,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_296,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_25,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_298,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_20,c_19,c_18,c_25])).

cnf(c_4979,plain,
    ( k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0)) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4978,c_298])).

cnf(c_21,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4987,plain,
    ( k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0)) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4979,c_21])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_311,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_312,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_31,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_314,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_312,c_20,c_19,c_18,c_31])).

cnf(c_2,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_615,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1903,plain,
    ( r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k2_relat_1(sK1)) = iProver_top
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_314,c_615])).

cnf(c_22,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_46,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_48,plain,
    ( v1_funct_1(sK1) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_1926,plain,
    ( r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k2_relat_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1903,c_21,c_22,c_48])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_609,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1932,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0))) = k10_relat_1(k2_funct_1(sK1),X0)
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1926,c_609])).

cnf(c_2270,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0))) = k10_relat_1(k2_funct_1(sK1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1932,c_21,c_22])).

cnf(c_4990,plain,
    ( k9_relat_1(sK1,k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)) = k10_relat_1(k2_funct_1(sK1),X0) ),
    inference(demodulation,[status(thm)],[c_4987,c_2270])).

cnf(c_24325,plain,
    ( k10_relat_1(k2_funct_1(sK1),X0) = k9_relat_1(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_23580,c_4990])).

cnf(c_17,negated_conjecture,
    ( k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24622,plain,
    ( k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_24325,c_17])).

cnf(c_24637,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_24622])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:19:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 8.05/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.05/1.51  
% 8.05/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.05/1.51  
% 8.05/1.51  ------  iProver source info
% 8.05/1.51  
% 8.05/1.51  git: date: 2020-06-30 10:37:57 +0100
% 8.05/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.05/1.51  git: non_committed_changes: false
% 8.05/1.51  git: last_make_outside_of_git: false
% 8.05/1.51  
% 8.05/1.51  ------ 
% 8.05/1.51  
% 8.05/1.51  ------ Input Options
% 8.05/1.51  
% 8.05/1.51  --out_options                           all
% 8.05/1.51  --tptp_safe_out                         true
% 8.05/1.51  --problem_path                          ""
% 8.05/1.51  --include_path                          ""
% 8.05/1.51  --clausifier                            res/vclausify_rel
% 8.05/1.51  --clausifier_options                    ""
% 8.05/1.51  --stdin                                 false
% 8.05/1.51  --stats_out                             all
% 8.05/1.51  
% 8.05/1.51  ------ General Options
% 8.05/1.51  
% 8.05/1.51  --fof                                   false
% 8.05/1.51  --time_out_real                         305.
% 8.05/1.51  --time_out_virtual                      -1.
% 8.05/1.51  --symbol_type_check                     false
% 8.05/1.51  --clausify_out                          false
% 8.05/1.51  --sig_cnt_out                           false
% 8.05/1.51  --trig_cnt_out                          false
% 8.05/1.51  --trig_cnt_out_tolerance                1.
% 8.05/1.51  --trig_cnt_out_sk_spl                   false
% 8.05/1.51  --abstr_cl_out                          false
% 8.05/1.51  
% 8.05/1.51  ------ Global Options
% 8.05/1.51  
% 8.05/1.51  --schedule                              default
% 8.05/1.51  --add_important_lit                     false
% 8.05/1.51  --prop_solver_per_cl                    1000
% 8.05/1.51  --min_unsat_core                        false
% 8.05/1.51  --soft_assumptions                      false
% 8.05/1.51  --soft_lemma_size                       3
% 8.05/1.51  --prop_impl_unit_size                   0
% 8.05/1.51  --prop_impl_unit                        []
% 8.05/1.51  --share_sel_clauses                     true
% 8.05/1.51  --reset_solvers                         false
% 8.05/1.51  --bc_imp_inh                            [conj_cone]
% 8.05/1.51  --conj_cone_tolerance                   3.
% 8.05/1.51  --extra_neg_conj                        none
% 8.05/1.51  --large_theory_mode                     true
% 8.05/1.51  --prolific_symb_bound                   200
% 8.05/1.51  --lt_threshold                          2000
% 8.05/1.51  --clause_weak_htbl                      true
% 8.05/1.51  --gc_record_bc_elim                     false
% 8.05/1.51  
% 8.05/1.51  ------ Preprocessing Options
% 8.05/1.51  
% 8.05/1.51  --preprocessing_flag                    true
% 8.05/1.51  --time_out_prep_mult                    0.1
% 8.05/1.51  --splitting_mode                        input
% 8.05/1.51  --splitting_grd                         true
% 8.05/1.51  --splitting_cvd                         false
% 8.05/1.51  --splitting_cvd_svl                     false
% 8.05/1.51  --splitting_nvd                         32
% 8.05/1.51  --sub_typing                            true
% 8.05/1.51  --prep_gs_sim                           true
% 8.05/1.51  --prep_unflatten                        true
% 8.05/1.51  --prep_res_sim                          true
% 8.05/1.51  --prep_upred                            true
% 8.05/1.51  --prep_sem_filter                       exhaustive
% 8.05/1.51  --prep_sem_filter_out                   false
% 8.05/1.51  --pred_elim                             true
% 8.05/1.51  --res_sim_input                         true
% 8.05/1.51  --eq_ax_congr_red                       true
% 8.05/1.51  --pure_diseq_elim                       true
% 8.05/1.51  --brand_transform                       false
% 8.05/1.51  --non_eq_to_eq                          false
% 8.05/1.51  --prep_def_merge                        true
% 8.05/1.51  --prep_def_merge_prop_impl              false
% 8.05/1.51  --prep_def_merge_mbd                    true
% 8.05/1.51  --prep_def_merge_tr_red                 false
% 8.05/1.51  --prep_def_merge_tr_cl                  false
% 8.05/1.51  --smt_preprocessing                     true
% 8.05/1.51  --smt_ac_axioms                         fast
% 8.05/1.51  --preprocessed_out                      false
% 8.05/1.51  --preprocessed_stats                    false
% 8.05/1.51  
% 8.05/1.51  ------ Abstraction refinement Options
% 8.05/1.51  
% 8.05/1.51  --abstr_ref                             []
% 8.05/1.51  --abstr_ref_prep                        false
% 8.05/1.51  --abstr_ref_until_sat                   false
% 8.05/1.51  --abstr_ref_sig_restrict                funpre
% 8.05/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 8.05/1.51  --abstr_ref_under                       []
% 8.05/1.51  
% 8.05/1.51  ------ SAT Options
% 8.05/1.51  
% 8.05/1.51  --sat_mode                              false
% 8.05/1.51  --sat_fm_restart_options                ""
% 8.05/1.51  --sat_gr_def                            false
% 8.05/1.51  --sat_epr_types                         true
% 8.05/1.51  --sat_non_cyclic_types                  false
% 8.05/1.51  --sat_finite_models                     false
% 8.05/1.51  --sat_fm_lemmas                         false
% 8.05/1.51  --sat_fm_prep                           false
% 8.05/1.51  --sat_fm_uc_incr                        true
% 8.05/1.51  --sat_out_model                         small
% 8.05/1.51  --sat_out_clauses                       false
% 8.05/1.51  
% 8.05/1.51  ------ QBF Options
% 8.05/1.51  
% 8.05/1.51  --qbf_mode                              false
% 8.05/1.51  --qbf_elim_univ                         false
% 8.05/1.51  --qbf_dom_inst                          none
% 8.05/1.51  --qbf_dom_pre_inst                      false
% 8.05/1.51  --qbf_sk_in                             false
% 8.05/1.51  --qbf_pred_elim                         true
% 8.05/1.51  --qbf_split                             512
% 8.05/1.51  
% 8.05/1.51  ------ BMC1 Options
% 8.05/1.51  
% 8.05/1.51  --bmc1_incremental                      false
% 8.05/1.51  --bmc1_axioms                           reachable_all
% 8.05/1.51  --bmc1_min_bound                        0
% 8.05/1.51  --bmc1_max_bound                        -1
% 8.05/1.51  --bmc1_max_bound_default                -1
% 8.05/1.51  --bmc1_symbol_reachability              true
% 8.05/1.51  --bmc1_property_lemmas                  false
% 8.05/1.51  --bmc1_k_induction                      false
% 8.05/1.51  --bmc1_non_equiv_states                 false
% 8.05/1.51  --bmc1_deadlock                         false
% 8.05/1.51  --bmc1_ucm                              false
% 8.05/1.51  --bmc1_add_unsat_core                   none
% 8.05/1.51  --bmc1_unsat_core_children              false
% 8.05/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 8.05/1.51  --bmc1_out_stat                         full
% 8.05/1.51  --bmc1_ground_init                      false
% 8.05/1.51  --bmc1_pre_inst_next_state              false
% 8.05/1.51  --bmc1_pre_inst_state                   false
% 8.05/1.51  --bmc1_pre_inst_reach_state             false
% 8.05/1.51  --bmc1_out_unsat_core                   false
% 8.05/1.51  --bmc1_aig_witness_out                  false
% 8.05/1.51  --bmc1_verbose                          false
% 8.05/1.51  --bmc1_dump_clauses_tptp                false
% 8.05/1.51  --bmc1_dump_unsat_core_tptp             false
% 8.05/1.51  --bmc1_dump_file                        -
% 8.05/1.51  --bmc1_ucm_expand_uc_limit              128
% 8.05/1.51  --bmc1_ucm_n_expand_iterations          6
% 8.05/1.51  --bmc1_ucm_extend_mode                  1
% 8.05/1.51  --bmc1_ucm_init_mode                    2
% 8.05/1.51  --bmc1_ucm_cone_mode                    none
% 8.05/1.51  --bmc1_ucm_reduced_relation_type        0
% 8.05/1.51  --bmc1_ucm_relax_model                  4
% 8.05/1.51  --bmc1_ucm_full_tr_after_sat            true
% 8.05/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 8.05/1.51  --bmc1_ucm_layered_model                none
% 8.05/1.51  --bmc1_ucm_max_lemma_size               10
% 8.05/1.51  
% 8.05/1.51  ------ AIG Options
% 8.05/1.51  
% 8.05/1.51  --aig_mode                              false
% 8.05/1.51  
% 8.05/1.51  ------ Instantiation Options
% 8.05/1.51  
% 8.05/1.51  --instantiation_flag                    true
% 8.05/1.51  --inst_sos_flag                         true
% 8.05/1.51  --inst_sos_phase                        true
% 8.05/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.05/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.05/1.51  --inst_lit_sel_side                     num_symb
% 8.05/1.51  --inst_solver_per_active                1400
% 8.05/1.51  --inst_solver_calls_frac                1.
% 8.05/1.51  --inst_passive_queue_type               priority_queues
% 8.05/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.05/1.51  --inst_passive_queues_freq              [25;2]
% 8.05/1.51  --inst_dismatching                      true
% 8.05/1.51  --inst_eager_unprocessed_to_passive     true
% 8.05/1.51  --inst_prop_sim_given                   true
% 8.05/1.51  --inst_prop_sim_new                     false
% 8.05/1.51  --inst_subs_new                         false
% 8.05/1.51  --inst_eq_res_simp                      false
% 8.05/1.51  --inst_subs_given                       false
% 8.05/1.51  --inst_orphan_elimination               true
% 8.05/1.51  --inst_learning_loop_flag               true
% 8.05/1.51  --inst_learning_start                   3000
% 8.05/1.51  --inst_learning_factor                  2
% 8.05/1.51  --inst_start_prop_sim_after_learn       3
% 8.05/1.51  --inst_sel_renew                        solver
% 8.05/1.51  --inst_lit_activity_flag                true
% 8.05/1.51  --inst_restr_to_given                   false
% 8.05/1.51  --inst_activity_threshold               500
% 8.05/1.51  --inst_out_proof                        true
% 8.05/1.51  
% 8.05/1.51  ------ Resolution Options
% 8.05/1.51  
% 8.05/1.51  --resolution_flag                       true
% 8.05/1.51  --res_lit_sel                           adaptive
% 8.05/1.51  --res_lit_sel_side                      none
% 8.05/1.51  --res_ordering                          kbo
% 8.05/1.51  --res_to_prop_solver                    active
% 8.05/1.51  --res_prop_simpl_new                    false
% 8.05/1.51  --res_prop_simpl_given                  true
% 8.05/1.51  --res_passive_queue_type                priority_queues
% 8.05/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.05/1.51  --res_passive_queues_freq               [15;5]
% 8.05/1.51  --res_forward_subs                      full
% 8.05/1.51  --res_backward_subs                     full
% 8.05/1.51  --res_forward_subs_resolution           true
% 8.05/1.51  --res_backward_subs_resolution          true
% 8.05/1.51  --res_orphan_elimination                true
% 8.05/1.51  --res_time_limit                        2.
% 8.05/1.51  --res_out_proof                         true
% 8.05/1.51  
% 8.05/1.51  ------ Superposition Options
% 8.05/1.51  
% 8.05/1.51  --superposition_flag                    true
% 8.05/1.51  --sup_passive_queue_type                priority_queues
% 8.05/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.05/1.51  --sup_passive_queues_freq               [8;1;4]
% 8.05/1.51  --demod_completeness_check              fast
% 8.05/1.51  --demod_use_ground                      true
% 8.05/1.51  --sup_to_prop_solver                    passive
% 8.05/1.51  --sup_prop_simpl_new                    true
% 8.05/1.51  --sup_prop_simpl_given                  true
% 8.05/1.51  --sup_fun_splitting                     true
% 8.05/1.51  --sup_smt_interval                      50000
% 8.05/1.51  
% 8.05/1.51  ------ Superposition Simplification Setup
% 8.05/1.51  
% 8.05/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.05/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.05/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.05/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.05/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 8.05/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.05/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.05/1.51  --sup_immed_triv                        [TrivRules]
% 8.05/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.05/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.05/1.51  --sup_immed_bw_main                     []
% 8.05/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.05/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 8.05/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.05/1.51  --sup_input_bw                          []
% 8.05/1.51  
% 8.05/1.51  ------ Combination Options
% 8.05/1.51  
% 8.05/1.51  --comb_res_mult                         3
% 8.05/1.51  --comb_sup_mult                         2
% 8.05/1.51  --comb_inst_mult                        10
% 8.05/1.51  
% 8.05/1.51  ------ Debug Options
% 8.05/1.51  
% 8.05/1.51  --dbg_backtrace                         false
% 8.05/1.51  --dbg_dump_prop_clauses                 false
% 8.05/1.51  --dbg_dump_prop_clauses_file            -
% 8.05/1.51  --dbg_out_stat                          false
% 8.05/1.51  ------ Parsing...
% 8.05/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.05/1.51  
% 8.05/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 8.05/1.51  
% 8.05/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.05/1.51  
% 8.05/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.05/1.51  ------ Proving...
% 8.05/1.51  ------ Problem Properties 
% 8.05/1.51  
% 8.05/1.51  
% 8.05/1.51  clauses                                 23
% 8.05/1.51  conjectures                             3
% 8.05/1.51  EPR                                     2
% 8.05/1.51  Horn                                    23
% 8.05/1.51  unary                                   12
% 8.05/1.51  binary                                  6
% 8.05/1.51  lits                                    40
% 8.05/1.51  lits eq                                 17
% 8.05/1.51  fd_pure                                 0
% 8.05/1.51  fd_pseudo                               0
% 8.05/1.51  fd_cond                                 0
% 8.05/1.51  fd_pseudo_cond                          0
% 8.05/1.51  AC symbols                              0
% 8.05/1.51  
% 8.05/1.51  ------ Schedule dynamic 5 is on 
% 8.05/1.51  
% 8.05/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.05/1.51  
% 8.05/1.51  
% 8.05/1.51  ------ 
% 8.05/1.51  Current options:
% 8.05/1.51  ------ 
% 8.05/1.51  
% 8.05/1.51  ------ Input Options
% 8.05/1.51  
% 8.05/1.51  --out_options                           all
% 8.05/1.51  --tptp_safe_out                         true
% 8.05/1.51  --problem_path                          ""
% 8.05/1.51  --include_path                          ""
% 8.05/1.51  --clausifier                            res/vclausify_rel
% 8.05/1.51  --clausifier_options                    ""
% 8.05/1.51  --stdin                                 false
% 8.05/1.51  --stats_out                             all
% 8.05/1.51  
% 8.05/1.51  ------ General Options
% 8.05/1.51  
% 8.05/1.51  --fof                                   false
% 8.05/1.51  --time_out_real                         305.
% 8.05/1.51  --time_out_virtual                      -1.
% 8.05/1.51  --symbol_type_check                     false
% 8.05/1.51  --clausify_out                          false
% 8.05/1.51  --sig_cnt_out                           false
% 8.05/1.51  --trig_cnt_out                          false
% 8.05/1.51  --trig_cnt_out_tolerance                1.
% 8.05/1.51  --trig_cnt_out_sk_spl                   false
% 8.05/1.51  --abstr_cl_out                          false
% 8.05/1.51  
% 8.05/1.51  ------ Global Options
% 8.05/1.51  
% 8.05/1.51  --schedule                              default
% 8.05/1.51  --add_important_lit                     false
% 8.05/1.51  --prop_solver_per_cl                    1000
% 8.05/1.51  --min_unsat_core                        false
% 8.05/1.51  --soft_assumptions                      false
% 8.05/1.51  --soft_lemma_size                       3
% 8.05/1.51  --prop_impl_unit_size                   0
% 8.05/1.51  --prop_impl_unit                        []
% 8.05/1.51  --share_sel_clauses                     true
% 8.05/1.51  --reset_solvers                         false
% 8.05/1.51  --bc_imp_inh                            [conj_cone]
% 8.05/1.51  --conj_cone_tolerance                   3.
% 8.05/1.51  --extra_neg_conj                        none
% 8.05/1.51  --large_theory_mode                     true
% 8.05/1.51  --prolific_symb_bound                   200
% 8.05/1.51  --lt_threshold                          2000
% 8.05/1.51  --clause_weak_htbl                      true
% 8.05/1.51  --gc_record_bc_elim                     false
% 8.05/1.51  
% 8.05/1.51  ------ Preprocessing Options
% 8.05/1.51  
% 8.05/1.51  --preprocessing_flag                    true
% 8.05/1.51  --time_out_prep_mult                    0.1
% 8.05/1.51  --splitting_mode                        input
% 8.05/1.51  --splitting_grd                         true
% 8.05/1.51  --splitting_cvd                         false
% 8.05/1.51  --splitting_cvd_svl                     false
% 8.05/1.51  --splitting_nvd                         32
% 8.05/1.51  --sub_typing                            true
% 8.05/1.51  --prep_gs_sim                           true
% 8.05/1.51  --prep_unflatten                        true
% 8.05/1.51  --prep_res_sim                          true
% 8.05/1.51  --prep_upred                            true
% 8.05/1.51  --prep_sem_filter                       exhaustive
% 8.05/1.51  --prep_sem_filter_out                   false
% 8.05/1.51  --pred_elim                             true
% 8.05/1.51  --res_sim_input                         true
% 8.05/1.51  --eq_ax_congr_red                       true
% 8.05/1.51  --pure_diseq_elim                       true
% 8.05/1.51  --brand_transform                       false
% 8.05/1.51  --non_eq_to_eq                          false
% 8.05/1.51  --prep_def_merge                        true
% 8.05/1.51  --prep_def_merge_prop_impl              false
% 8.05/1.51  --prep_def_merge_mbd                    true
% 8.05/1.51  --prep_def_merge_tr_red                 false
% 8.05/1.51  --prep_def_merge_tr_cl                  false
% 8.05/1.51  --smt_preprocessing                     true
% 8.05/1.51  --smt_ac_axioms                         fast
% 8.05/1.51  --preprocessed_out                      false
% 8.05/1.51  --preprocessed_stats                    false
% 8.05/1.51  
% 8.05/1.51  ------ Abstraction refinement Options
% 8.05/1.51  
% 8.05/1.51  --abstr_ref                             []
% 8.05/1.51  --abstr_ref_prep                        false
% 8.05/1.51  --abstr_ref_until_sat                   false
% 8.05/1.51  --abstr_ref_sig_restrict                funpre
% 8.05/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 8.05/1.51  --abstr_ref_under                       []
% 8.05/1.51  
% 8.05/1.51  ------ SAT Options
% 8.05/1.51  
% 8.05/1.51  --sat_mode                              false
% 8.05/1.51  --sat_fm_restart_options                ""
% 8.05/1.51  --sat_gr_def                            false
% 8.05/1.51  --sat_epr_types                         true
% 8.05/1.51  --sat_non_cyclic_types                  false
% 8.05/1.51  --sat_finite_models                     false
% 8.05/1.51  --sat_fm_lemmas                         false
% 8.05/1.51  --sat_fm_prep                           false
% 8.05/1.51  --sat_fm_uc_incr                        true
% 8.05/1.51  --sat_out_model                         small
% 8.05/1.51  --sat_out_clauses                       false
% 8.05/1.51  
% 8.05/1.51  ------ QBF Options
% 8.05/1.51  
% 8.05/1.51  --qbf_mode                              false
% 8.05/1.51  --qbf_elim_univ                         false
% 8.05/1.51  --qbf_dom_inst                          none
% 8.05/1.51  --qbf_dom_pre_inst                      false
% 8.05/1.51  --qbf_sk_in                             false
% 8.05/1.51  --qbf_pred_elim                         true
% 8.05/1.51  --qbf_split                             512
% 8.05/1.51  
% 8.05/1.51  ------ BMC1 Options
% 8.05/1.51  
% 8.05/1.51  --bmc1_incremental                      false
% 8.05/1.51  --bmc1_axioms                           reachable_all
% 8.05/1.51  --bmc1_min_bound                        0
% 8.05/1.51  --bmc1_max_bound                        -1
% 8.05/1.51  --bmc1_max_bound_default                -1
% 8.05/1.51  --bmc1_symbol_reachability              true
% 8.05/1.51  --bmc1_property_lemmas                  false
% 8.05/1.51  --bmc1_k_induction                      false
% 8.05/1.51  --bmc1_non_equiv_states                 false
% 8.05/1.51  --bmc1_deadlock                         false
% 8.05/1.51  --bmc1_ucm                              false
% 8.05/1.51  --bmc1_add_unsat_core                   none
% 8.05/1.51  --bmc1_unsat_core_children              false
% 8.05/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 8.05/1.51  --bmc1_out_stat                         full
% 8.05/1.51  --bmc1_ground_init                      false
% 8.05/1.51  --bmc1_pre_inst_next_state              false
% 8.05/1.51  --bmc1_pre_inst_state                   false
% 8.05/1.51  --bmc1_pre_inst_reach_state             false
% 8.05/1.51  --bmc1_out_unsat_core                   false
% 8.05/1.51  --bmc1_aig_witness_out                  false
% 8.05/1.51  --bmc1_verbose                          false
% 8.05/1.51  --bmc1_dump_clauses_tptp                false
% 8.05/1.51  --bmc1_dump_unsat_core_tptp             false
% 8.05/1.51  --bmc1_dump_file                        -
% 8.05/1.51  --bmc1_ucm_expand_uc_limit              128
% 8.05/1.51  --bmc1_ucm_n_expand_iterations          6
% 8.05/1.51  --bmc1_ucm_extend_mode                  1
% 8.05/1.51  --bmc1_ucm_init_mode                    2
% 8.05/1.51  --bmc1_ucm_cone_mode                    none
% 8.05/1.51  --bmc1_ucm_reduced_relation_type        0
% 8.05/1.51  --bmc1_ucm_relax_model                  4
% 8.05/1.51  --bmc1_ucm_full_tr_after_sat            true
% 8.05/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 8.05/1.51  --bmc1_ucm_layered_model                none
% 8.05/1.51  --bmc1_ucm_max_lemma_size               10
% 8.05/1.51  
% 8.05/1.51  ------ AIG Options
% 8.05/1.51  
% 8.05/1.51  --aig_mode                              false
% 8.05/1.51  
% 8.05/1.51  ------ Instantiation Options
% 8.05/1.51  
% 8.05/1.51  --instantiation_flag                    true
% 8.05/1.51  --inst_sos_flag                         true
% 8.05/1.51  --inst_sos_phase                        true
% 8.05/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.05/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.05/1.51  --inst_lit_sel_side                     none
% 8.05/1.51  --inst_solver_per_active                1400
% 8.05/1.51  --inst_solver_calls_frac                1.
% 8.05/1.51  --inst_passive_queue_type               priority_queues
% 8.05/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.05/1.51  --inst_passive_queues_freq              [25;2]
% 8.05/1.51  --inst_dismatching                      true
% 8.05/1.51  --inst_eager_unprocessed_to_passive     true
% 8.05/1.51  --inst_prop_sim_given                   true
% 8.05/1.51  --inst_prop_sim_new                     false
% 8.05/1.51  --inst_subs_new                         false
% 8.05/1.51  --inst_eq_res_simp                      false
% 8.05/1.51  --inst_subs_given                       false
% 8.05/1.51  --inst_orphan_elimination               true
% 8.05/1.51  --inst_learning_loop_flag               true
% 8.05/1.51  --inst_learning_start                   3000
% 8.05/1.51  --inst_learning_factor                  2
% 8.05/1.51  --inst_start_prop_sim_after_learn       3
% 8.05/1.51  --inst_sel_renew                        solver
% 8.05/1.51  --inst_lit_activity_flag                true
% 8.05/1.51  --inst_restr_to_given                   false
% 8.05/1.51  --inst_activity_threshold               500
% 8.05/1.51  --inst_out_proof                        true
% 8.05/1.51  
% 8.05/1.51  ------ Resolution Options
% 8.05/1.51  
% 8.05/1.51  --resolution_flag                       false
% 8.05/1.51  --res_lit_sel                           adaptive
% 8.05/1.51  --res_lit_sel_side                      none
% 8.05/1.51  --res_ordering                          kbo
% 8.05/1.51  --res_to_prop_solver                    active
% 8.05/1.51  --res_prop_simpl_new                    false
% 8.05/1.51  --res_prop_simpl_given                  true
% 8.05/1.51  --res_passive_queue_type                priority_queues
% 8.05/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.05/1.51  --res_passive_queues_freq               [15;5]
% 8.05/1.51  --res_forward_subs                      full
% 8.05/1.51  --res_backward_subs                     full
% 8.05/1.51  --res_forward_subs_resolution           true
% 8.05/1.51  --res_backward_subs_resolution          true
% 8.05/1.51  --res_orphan_elimination                true
% 8.05/1.51  --res_time_limit                        2.
% 8.05/1.51  --res_out_proof                         true
% 8.05/1.51  
% 8.05/1.51  ------ Superposition Options
% 8.05/1.51  
% 8.05/1.51  --superposition_flag                    true
% 8.05/1.51  --sup_passive_queue_type                priority_queues
% 8.05/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.05/1.51  --sup_passive_queues_freq               [8;1;4]
% 8.05/1.51  --demod_completeness_check              fast
% 8.05/1.51  --demod_use_ground                      true
% 8.05/1.51  --sup_to_prop_solver                    passive
% 8.05/1.51  --sup_prop_simpl_new                    true
% 8.05/1.51  --sup_prop_simpl_given                  true
% 8.05/1.51  --sup_fun_splitting                     true
% 8.05/1.51  --sup_smt_interval                      50000
% 8.05/1.51  
% 8.05/1.51  ------ Superposition Simplification Setup
% 8.05/1.51  
% 8.05/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.05/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.05/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.05/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.05/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 8.05/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.05/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.05/1.51  --sup_immed_triv                        [TrivRules]
% 8.05/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.05/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.05/1.51  --sup_immed_bw_main                     []
% 8.05/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.05/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 8.05/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.05/1.51  --sup_input_bw                          []
% 8.05/1.51  
% 8.05/1.51  ------ Combination Options
% 8.05/1.51  
% 8.05/1.51  --comb_res_mult                         3
% 8.05/1.51  --comb_sup_mult                         2
% 8.05/1.51  --comb_inst_mult                        10
% 8.05/1.51  
% 8.05/1.51  ------ Debug Options
% 8.05/1.51  
% 8.05/1.51  --dbg_backtrace                         false
% 8.05/1.51  --dbg_dump_prop_clauses                 false
% 8.05/1.51  --dbg_dump_prop_clauses_file            -
% 8.05/1.51  --dbg_out_stat                          false
% 8.05/1.51  
% 8.05/1.51  
% 8.05/1.51  
% 8.05/1.51  
% 8.05/1.51  ------ Proving...
% 8.05/1.51  
% 8.05/1.51  
% 8.05/1.51  % SZS status Theorem for theBenchmark.p
% 8.05/1.51  
% 8.05/1.51   Resolution empty clause
% 8.05/1.51  
% 8.05/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 8.05/1.51  
% 8.05/1.51  fof(f10,axiom,(
% 8.05/1.51    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 8.05/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.05/1.51  
% 8.05/1.51  fof(f44,plain,(
% 8.05/1.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 8.05/1.51    inference(cnf_transformation,[],[f10])).
% 8.05/1.51  
% 8.05/1.51  fof(f7,axiom,(
% 8.05/1.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 8.05/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.05/1.51  
% 8.05/1.51  fof(f20,plain,(
% 8.05/1.51    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 8.05/1.51    inference(ennf_transformation,[],[f7])).
% 8.05/1.51  
% 8.05/1.51  fof(f39,plain,(
% 8.05/1.51    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 8.05/1.51    inference(cnf_transformation,[],[f20])).
% 8.05/1.51  
% 8.05/1.51  fof(f8,axiom,(
% 8.05/1.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 8.05/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.05/1.51  
% 8.05/1.51  fof(f40,plain,(
% 8.05/1.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 8.05/1.51    inference(cnf_transformation,[],[f8])).
% 8.05/1.51  
% 8.05/1.51  fof(f1,axiom,(
% 8.05/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 8.05/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.05/1.51  
% 8.05/1.51  fof(f33,plain,(
% 8.05/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 8.05/1.51    inference(cnf_transformation,[],[f1])).
% 8.05/1.51  
% 8.05/1.51  fof(f2,axiom,(
% 8.05/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 8.05/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.05/1.51  
% 8.05/1.51  fof(f34,plain,(
% 8.05/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 8.05/1.51    inference(cnf_transformation,[],[f2])).
% 8.05/1.51  
% 8.05/1.51  fof(f57,plain,(
% 8.05/1.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 8.05/1.51    inference(definition_unfolding,[],[f33,f34,f34])).
% 8.05/1.51  
% 8.05/1.51  fof(f12,axiom,(
% 8.05/1.51    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 8.05/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.05/1.51  
% 8.05/1.51  fof(f47,plain,(
% 8.05/1.51    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 8.05/1.51    inference(cnf_transformation,[],[f12])).
% 8.05/1.51  
% 8.05/1.51  fof(f3,axiom,(
% 8.05/1.51    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 8.05/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.05/1.51  
% 8.05/1.51  fof(f35,plain,(
% 8.05/1.51    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 8.05/1.51    inference(cnf_transformation,[],[f3])).
% 8.05/1.52  
% 8.05/1.52  fof(f56,plain,(
% 8.05/1.52    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 8.05/1.52    inference(definition_unfolding,[],[f35,f34])).
% 8.05/1.52  
% 8.05/1.52  fof(f59,plain,(
% 8.05/1.52    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 8.05/1.52    inference(definition_unfolding,[],[f47,f56])).
% 8.05/1.52  
% 8.05/1.52  fof(f15,conjecture,(
% 8.05/1.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 8.05/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.05/1.52  
% 8.05/1.52  fof(f16,negated_conjecture,(
% 8.05/1.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 8.05/1.52    inference(negated_conjecture,[],[f15])).
% 8.05/1.52  
% 8.05/1.52  fof(f29,plain,(
% 8.05/1.52    ? [X0,X1] : ((k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 8.05/1.52    inference(ennf_transformation,[],[f16])).
% 8.05/1.52  
% 8.05/1.52  fof(f30,plain,(
% 8.05/1.52    ? [X0,X1] : (k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 8.05/1.52    inference(flattening,[],[f29])).
% 8.05/1.52  
% 8.05/1.52  fof(f31,plain,(
% 8.05/1.52    ? [X0,X1] : (k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 8.05/1.52    introduced(choice_axiom,[])).
% 8.05/1.52  
% 8.05/1.52  fof(f32,plain,(
% 8.05/1.52    k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 8.05/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).
% 8.05/1.52  
% 8.05/1.52  fof(f52,plain,(
% 8.05/1.52    v1_relat_1(sK1)),
% 8.05/1.52    inference(cnf_transformation,[],[f32])).
% 8.05/1.52  
% 8.05/1.52  fof(f4,axiom,(
% 8.05/1.52    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 8.05/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.05/1.52  
% 8.05/1.52  fof(f17,plain,(
% 8.05/1.52    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 8.05/1.52    inference(ennf_transformation,[],[f4])).
% 8.05/1.52  
% 8.05/1.52  fof(f36,plain,(
% 8.05/1.52    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 8.05/1.52    inference(cnf_transformation,[],[f17])).
% 8.05/1.52  
% 8.05/1.52  fof(f58,plain,(
% 8.05/1.52    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 8.05/1.52    inference(definition_unfolding,[],[f36,f56])).
% 8.05/1.52  
% 8.05/1.52  fof(f53,plain,(
% 8.05/1.52    v1_funct_1(sK1)),
% 8.05/1.52    inference(cnf_transformation,[],[f32])).
% 8.05/1.52  
% 8.05/1.52  fof(f9,axiom,(
% 8.05/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 8.05/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.05/1.52  
% 8.05/1.52  fof(f21,plain,(
% 8.05/1.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.05/1.52    inference(ennf_transformation,[],[f9])).
% 8.05/1.52  
% 8.05/1.52  fof(f22,plain,(
% 8.05/1.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.05/1.52    inference(flattening,[],[f21])).
% 8.05/1.52  
% 8.05/1.52  fof(f42,plain,(
% 8.05/1.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.05/1.52    inference(cnf_transformation,[],[f22])).
% 8.05/1.52  
% 8.05/1.52  fof(f6,axiom,(
% 8.05/1.52    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)))),
% 8.05/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.05/1.52  
% 8.05/1.52  fof(f19,plain,(
% 8.05/1.52    ! [X0,X1] : (! [X2] : (k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 8.05/1.52    inference(ennf_transformation,[],[f6])).
% 8.05/1.52  
% 8.05/1.52  fof(f38,plain,(
% 8.05/1.52    ( ! [X2,X0,X1] : (k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 8.05/1.52    inference(cnf_transformation,[],[f19])).
% 8.05/1.52  
% 8.05/1.52  fof(f14,axiom,(
% 8.05/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 8.05/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.05/1.52  
% 8.05/1.52  fof(f27,plain,(
% 8.05/1.52    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.05/1.52    inference(ennf_transformation,[],[f14])).
% 8.05/1.52  
% 8.05/1.52  fof(f28,plain,(
% 8.05/1.52    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.05/1.52    inference(flattening,[],[f27])).
% 8.05/1.52  
% 8.05/1.52  fof(f50,plain,(
% 8.05/1.52    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.05/1.52    inference(cnf_transformation,[],[f28])).
% 8.05/1.52  
% 8.05/1.52  fof(f54,plain,(
% 8.05/1.52    v2_funct_1(sK1)),
% 8.05/1.52    inference(cnf_transformation,[],[f32])).
% 8.05/1.52  
% 8.05/1.52  fof(f13,axiom,(
% 8.05/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 8.05/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.05/1.52  
% 8.05/1.52  fof(f25,plain,(
% 8.05/1.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.05/1.52    inference(ennf_transformation,[],[f13])).
% 8.05/1.52  
% 8.05/1.52  fof(f26,plain,(
% 8.05/1.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.05/1.52    inference(flattening,[],[f25])).
% 8.05/1.52  
% 8.05/1.52  fof(f48,plain,(
% 8.05/1.52    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.05/1.52    inference(cnf_transformation,[],[f26])).
% 8.05/1.52  
% 8.05/1.52  fof(f5,axiom,(
% 8.05/1.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 8.05/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.05/1.52  
% 8.05/1.52  fof(f18,plain,(
% 8.05/1.52    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 8.05/1.52    inference(ennf_transformation,[],[f5])).
% 8.05/1.52  
% 8.05/1.52  fof(f37,plain,(
% 8.05/1.52    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 8.05/1.52    inference(cnf_transformation,[],[f18])).
% 8.05/1.52  
% 8.05/1.52  fof(f11,axiom,(
% 8.05/1.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 8.05/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.05/1.52  
% 8.05/1.52  fof(f23,plain,(
% 8.05/1.52    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 8.05/1.52    inference(ennf_transformation,[],[f11])).
% 8.05/1.52  
% 8.05/1.52  fof(f24,plain,(
% 8.05/1.52    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 8.05/1.52    inference(flattening,[],[f23])).
% 8.05/1.52  
% 8.05/1.52  fof(f46,plain,(
% 8.05/1.52    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 8.05/1.52    inference(cnf_transformation,[],[f24])).
% 8.05/1.52  
% 8.05/1.52  fof(f55,plain,(
% 8.05/1.52    k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0)),
% 8.05/1.52    inference(cnf_transformation,[],[f32])).
% 8.05/1.52  
% 8.05/1.52  cnf(c_10,plain,
% 8.05/1.52      ( v1_relat_1(k6_relat_1(X0)) ),
% 8.05/1.52      inference(cnf_transformation,[],[f44]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_610,plain,
% 8.05/1.52      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 8.05/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_4,plain,
% 8.05/1.52      ( ~ v1_relat_1(X0)
% 8.05/1.52      | ~ v1_relat_1(X1)
% 8.05/1.52      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 8.05/1.52      inference(cnf_transformation,[],[f39]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_613,plain,
% 8.05/1.52      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 8.05/1.52      | v1_relat_1(X1) != iProver_top
% 8.05/1.52      | v1_relat_1(X0) != iProver_top ),
% 8.05/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_2710,plain,
% 8.05/1.52      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
% 8.05/1.52      | v1_relat_1(X1) != iProver_top ),
% 8.05/1.52      inference(superposition,[status(thm)],[c_610,c_613]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_22039,plain,
% 8.05/1.52      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
% 8.05/1.52      inference(superposition,[status(thm)],[c_610,c_2710]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_6,plain,
% 8.05/1.52      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 8.05/1.52      inference(cnf_transformation,[],[f40]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_22063,plain,
% 8.05/1.52      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
% 8.05/1.52      inference(demodulation,[status(thm)],[c_22039,c_6]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_0,plain,
% 8.05/1.52      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 8.05/1.52      inference(cnf_transformation,[],[f57]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_12,plain,
% 8.05/1.52      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 8.05/1.52      inference(cnf_transformation,[],[f59]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_853,plain,
% 8.05/1.52      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 8.05/1.52      inference(superposition,[status(thm)],[c_0,c_12]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_1065,plain,
% 8.05/1.52      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
% 8.05/1.52      inference(superposition,[status(thm)],[c_853,c_6]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_20,negated_conjecture,
% 8.05/1.52      ( v1_relat_1(sK1) ),
% 8.05/1.52      inference(cnf_transformation,[],[f52]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_607,plain,
% 8.05/1.52      ( v1_relat_1(sK1) = iProver_top ),
% 8.05/1.52      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_1,plain,
% 8.05/1.52      ( ~ v1_relat_1(X0)
% 8.05/1.52      | k9_relat_1(X0,k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1))) = k9_relat_1(X0,X1) ),
% 8.05/1.52      inference(cnf_transformation,[],[f58]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_616,plain,
% 8.05/1.52      ( k9_relat_1(X0,k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1))) = k9_relat_1(X0,X1)
% 8.05/1.52      | v1_relat_1(X0) != iProver_top ),
% 8.05/1.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_2845,plain,
% 8.05/1.52      ( k9_relat_1(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0))) = k9_relat_1(sK1,X0) ),
% 8.05/1.52      inference(superposition,[status(thm)],[c_607,c_616]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_3114,plain,
% 8.05/1.52      ( k9_relat_1(sK1,k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),k6_relat_1(X0)))) = k9_relat_1(sK1,X0) ),
% 8.05/1.52      inference(superposition,[status(thm)],[c_1065,c_2845]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_23580,plain,
% 8.05/1.52      ( k9_relat_1(sK1,k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)) = k9_relat_1(sK1,X0) ),
% 8.05/1.52      inference(demodulation,[status(thm)],[c_22063,c_3114]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_19,negated_conjecture,
% 8.05/1.52      ( v1_funct_1(sK1) ),
% 8.05/1.52      inference(cnf_transformation,[],[f53]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_608,plain,
% 8.05/1.52      ( v1_funct_1(sK1) = iProver_top ),
% 8.05/1.52      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_8,plain,
% 8.05/1.52      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 8.05/1.52      inference(cnf_transformation,[],[f42]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_611,plain,
% 8.05/1.52      ( v1_funct_1(X0) != iProver_top
% 8.05/1.52      | v1_relat_1(X0) != iProver_top
% 8.05/1.52      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 8.05/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_3,plain,
% 8.05/1.52      ( ~ v1_relat_1(X0)
% 8.05/1.52      | ~ v1_relat_1(X1)
% 8.05/1.52      | k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2)) ),
% 8.05/1.52      inference(cnf_transformation,[],[f38]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_614,plain,
% 8.05/1.52      ( k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2))
% 8.05/1.52      | v1_relat_1(X0) != iProver_top
% 8.05/1.52      | v1_relat_1(X1) != iProver_top ),
% 8.05/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_3473,plain,
% 8.05/1.52      ( k10_relat_1(sK1,k10_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(sK1,X0),X1)
% 8.05/1.52      | v1_relat_1(X0) != iProver_top ),
% 8.05/1.52      inference(superposition,[status(thm)],[c_607,c_614]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_3786,plain,
% 8.05/1.52      ( k10_relat_1(k5_relat_1(sK1,k2_funct_1(X0)),X1) = k10_relat_1(sK1,k10_relat_1(k2_funct_1(X0),X1))
% 8.05/1.52      | v1_funct_1(X0) != iProver_top
% 8.05/1.52      | v1_relat_1(X0) != iProver_top ),
% 8.05/1.52      inference(superposition,[status(thm)],[c_611,c_3473]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_4978,plain,
% 8.05/1.52      ( k10_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0) = k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0))
% 8.05/1.52      | v1_relat_1(sK1) != iProver_top ),
% 8.05/1.52      inference(superposition,[status(thm)],[c_608,c_3786]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_16,plain,
% 8.05/1.52      ( ~ v2_funct_1(X0)
% 8.05/1.52      | ~ v1_funct_1(X0)
% 8.05/1.52      | ~ v1_relat_1(X0)
% 8.05/1.52      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 8.05/1.52      inference(cnf_transformation,[],[f50]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_18,negated_conjecture,
% 8.05/1.52      ( v2_funct_1(sK1) ),
% 8.05/1.52      inference(cnf_transformation,[],[f54]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_295,plain,
% 8.05/1.52      ( ~ v1_funct_1(X0)
% 8.05/1.52      | ~ v1_relat_1(X0)
% 8.05/1.52      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
% 8.05/1.52      | sK1 != X0 ),
% 8.05/1.52      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_296,plain,
% 8.05/1.52      ( ~ v1_funct_1(sK1)
% 8.05/1.52      | ~ v1_relat_1(sK1)
% 8.05/1.52      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
% 8.05/1.52      inference(unflattening,[status(thm)],[c_295]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_25,plain,
% 8.05/1.52      ( ~ v2_funct_1(sK1)
% 8.05/1.52      | ~ v1_funct_1(sK1)
% 8.05/1.52      | ~ v1_relat_1(sK1)
% 8.05/1.52      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
% 8.05/1.52      inference(instantiation,[status(thm)],[c_16]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_298,plain,
% 8.05/1.52      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
% 8.05/1.52      inference(global_propositional_subsumption,
% 8.05/1.52                [status(thm)],
% 8.05/1.52                [c_296,c_20,c_19,c_18,c_25]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_4979,plain,
% 8.05/1.52      ( k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0)) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)
% 8.05/1.52      | v1_relat_1(sK1) != iProver_top ),
% 8.05/1.52      inference(light_normalisation,[status(thm)],[c_4978,c_298]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_21,plain,
% 8.05/1.52      ( v1_relat_1(sK1) = iProver_top ),
% 8.05/1.52      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_4987,plain,
% 8.05/1.52      ( k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0)) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) ),
% 8.05/1.52      inference(global_propositional_subsumption,[status(thm)],[c_4979,c_21]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_14,plain,
% 8.05/1.52      ( ~ v2_funct_1(X0)
% 8.05/1.52      | ~ v1_funct_1(X0)
% 8.05/1.52      | ~ v1_relat_1(X0)
% 8.05/1.52      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 8.05/1.52      inference(cnf_transformation,[],[f48]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_311,plain,
% 8.05/1.52      ( ~ v1_funct_1(X0)
% 8.05/1.52      | ~ v1_relat_1(X0)
% 8.05/1.52      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 8.05/1.52      | sK1 != X0 ),
% 8.05/1.52      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_312,plain,
% 8.05/1.52      ( ~ v1_funct_1(sK1)
% 8.05/1.52      | ~ v1_relat_1(sK1)
% 8.05/1.52      | k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
% 8.05/1.52      inference(unflattening,[status(thm)],[c_311]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_31,plain,
% 8.05/1.52      ( ~ v2_funct_1(sK1)
% 8.05/1.52      | ~ v1_funct_1(sK1)
% 8.05/1.52      | ~ v1_relat_1(sK1)
% 8.05/1.52      | k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
% 8.05/1.52      inference(instantiation,[status(thm)],[c_14]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_314,plain,
% 8.05/1.52      ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
% 8.05/1.52      inference(global_propositional_subsumption,
% 8.05/1.52                [status(thm)],
% 8.05/1.52                [c_312,c_20,c_19,c_18,c_31]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_2,plain,
% 8.05/1.52      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 8.05/1.52      inference(cnf_transformation,[],[f37]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_615,plain,
% 8.05/1.52      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 8.05/1.52      | v1_relat_1(X0) != iProver_top ),
% 8.05/1.52      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_1903,plain,
% 8.05/1.52      ( r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k2_relat_1(sK1)) = iProver_top
% 8.05/1.52      | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
% 8.05/1.52      inference(superposition,[status(thm)],[c_314,c_615]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_22,plain,
% 8.05/1.52      ( v1_funct_1(sK1) = iProver_top ),
% 8.05/1.52      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_46,plain,
% 8.05/1.52      ( v1_funct_1(X0) != iProver_top
% 8.05/1.52      | v1_relat_1(X0) != iProver_top
% 8.05/1.52      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 8.05/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_48,plain,
% 8.05/1.52      ( v1_funct_1(sK1) != iProver_top
% 8.05/1.52      | v1_relat_1(k2_funct_1(sK1)) = iProver_top
% 8.05/1.52      | v1_relat_1(sK1) != iProver_top ),
% 8.05/1.52      inference(instantiation,[status(thm)],[c_46]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_1926,plain,
% 8.05/1.52      ( r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k2_relat_1(sK1)) = iProver_top ),
% 8.05/1.52      inference(global_propositional_subsumption,
% 8.05/1.52                [status(thm)],
% 8.05/1.52                [c_1903,c_21,c_22,c_48]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_11,plain,
% 8.05/1.52      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 8.05/1.52      | ~ v1_funct_1(X1)
% 8.05/1.52      | ~ v1_relat_1(X1)
% 8.05/1.52      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 8.05/1.52      inference(cnf_transformation,[],[f46]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_609,plain,
% 8.05/1.52      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 8.05/1.52      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 8.05/1.52      | v1_funct_1(X0) != iProver_top
% 8.05/1.52      | v1_relat_1(X0) != iProver_top ),
% 8.05/1.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_1932,plain,
% 8.05/1.52      ( k9_relat_1(sK1,k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0))) = k10_relat_1(k2_funct_1(sK1),X0)
% 8.05/1.52      | v1_funct_1(sK1) != iProver_top
% 8.05/1.52      | v1_relat_1(sK1) != iProver_top ),
% 8.05/1.52      inference(superposition,[status(thm)],[c_1926,c_609]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_2270,plain,
% 8.05/1.52      ( k9_relat_1(sK1,k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0))) = k10_relat_1(k2_funct_1(sK1),X0) ),
% 8.05/1.52      inference(global_propositional_subsumption,
% 8.05/1.52                [status(thm)],
% 8.05/1.52                [c_1932,c_21,c_22]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_4990,plain,
% 8.05/1.52      ( k9_relat_1(sK1,k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)) = k10_relat_1(k2_funct_1(sK1),X0) ),
% 8.05/1.52      inference(demodulation,[status(thm)],[c_4987,c_2270]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_24325,plain,
% 8.05/1.52      ( k10_relat_1(k2_funct_1(sK1),X0) = k9_relat_1(sK1,X0) ),
% 8.05/1.52      inference(demodulation,[status(thm)],[c_23580,c_4990]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_17,negated_conjecture,
% 8.05/1.52      ( k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) ),
% 8.05/1.52      inference(cnf_transformation,[],[f55]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_24622,plain,
% 8.05/1.52      ( k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0) ),
% 8.05/1.52      inference(demodulation,[status(thm)],[c_24325,c_17]) ).
% 8.05/1.52  
% 8.05/1.52  cnf(c_24637,plain,
% 8.05/1.52      ( $false ),
% 8.05/1.52      inference(equality_resolution_simp,[status(thm)],[c_24622]) ).
% 8.05/1.52  
% 8.05/1.52  
% 8.05/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 8.05/1.52  
% 8.05/1.52  ------                               Statistics
% 8.05/1.52  
% 8.05/1.52  ------ General
% 8.05/1.52  
% 8.05/1.52  abstr_ref_over_cycles:                  0
% 8.05/1.52  abstr_ref_under_cycles:                 0
% 8.05/1.52  gc_basic_clause_elim:                   0
% 8.05/1.52  forced_gc_time:                         0
% 8.05/1.52  parsing_time:                           0.013
% 8.05/1.52  unif_index_cands_time:                  0.
% 8.05/1.52  unif_index_add_time:                    0.
% 8.05/1.52  orderings_time:                         0.
% 8.05/1.52  out_proof_time:                         0.01
% 8.05/1.52  total_time:                             0.854
% 8.05/1.52  num_of_symbols:                         46
% 8.05/1.52  num_of_terms:                           28387
% 8.05/1.52  
% 8.05/1.52  ------ Preprocessing
% 8.05/1.52  
% 8.05/1.52  num_of_splits:                          0
% 8.05/1.52  num_of_split_atoms:                     0
% 8.05/1.52  num_of_reused_defs:                     0
% 8.05/1.52  num_eq_ax_congr_red:                    2
% 8.05/1.52  num_of_sem_filtered_clauses:            1
% 8.05/1.52  num_of_subtypes:                        0
% 8.05/1.52  monotx_restored_types:                  0
% 8.05/1.52  sat_num_of_epr_types:                   0
% 8.05/1.52  sat_num_of_non_cyclic_types:            0
% 8.05/1.52  sat_guarded_non_collapsed_types:        0
% 8.05/1.52  num_pure_diseq_elim:                    0
% 8.05/1.52  simp_replaced_by:                       0
% 8.05/1.52  res_preprocessed:                       96
% 8.05/1.52  prep_upred:                             0
% 8.05/1.52  prep_unflattend:                        9
% 8.05/1.52  smt_new_axioms:                         0
% 8.05/1.52  pred_elim_cands:                        4
% 8.05/1.52  pred_elim:                              1
% 8.05/1.52  pred_elim_cl:                           -2
% 8.05/1.52  pred_elim_cycles:                       3
% 8.05/1.52  merged_defs:                            0
% 8.05/1.52  merged_defs_ncl:                        0
% 8.05/1.52  bin_hyper_res:                          0
% 8.05/1.52  prep_cycles:                            3
% 8.05/1.52  pred_elim_time:                         0.002
% 8.05/1.52  splitting_time:                         0.
% 8.05/1.52  sem_filter_time:                        0.
% 8.05/1.52  monotx_time:                            0.
% 8.05/1.52  subtype_inf_time:                       0.
% 8.05/1.52  
% 8.05/1.52  ------ Problem properties
% 8.05/1.52  
% 8.05/1.52  clauses:                                23
% 8.05/1.52  conjectures:                            3
% 8.05/1.52  epr:                                    2
% 8.05/1.52  horn:                                   23
% 8.05/1.52  ground:                                 7
% 8.05/1.52  unary:                                  12
% 8.05/1.52  binary:                                 6
% 8.05/1.52  lits:                                   40
% 8.05/1.52  lits_eq:                                17
% 8.05/1.52  fd_pure:                                0
% 8.05/1.52  fd_pseudo:                              0
% 8.05/1.52  fd_cond:                                0
% 8.05/1.52  fd_pseudo_cond:                         0
% 8.05/1.52  ac_symbols:                             0
% 8.05/1.52  
% 8.05/1.52  ------ Propositional Solver
% 8.05/1.52  
% 8.05/1.52  prop_solver_calls:                      31
% 8.05/1.52  prop_fast_solver_calls:                 738
% 8.05/1.52  smt_solver_calls:                       0
% 8.05/1.52  smt_fast_solver_calls:                  0
% 8.05/1.52  prop_num_of_clauses:                    9488
% 8.05/1.52  prop_preprocess_simplified:             19112
% 8.05/1.52  prop_fo_subsumed:                       26
% 8.05/1.52  prop_solver_time:                       0.
% 8.05/1.52  smt_solver_time:                        0.
% 8.05/1.52  smt_fast_solver_time:                   0.
% 8.05/1.52  prop_fast_solver_time:                  0.
% 8.05/1.52  prop_unsat_core_time:                   0.
% 8.05/1.52  
% 8.05/1.52  ------ QBF
% 8.05/1.52  
% 8.05/1.52  qbf_q_res:                              0
% 8.05/1.52  qbf_num_tautologies:                    0
% 8.05/1.52  qbf_prep_cycles:                        0
% 8.05/1.52  
% 8.05/1.52  ------ BMC1
% 8.05/1.52  
% 8.05/1.52  bmc1_current_bound:                     -1
% 8.05/1.52  bmc1_last_solved_bound:                 -1
% 8.05/1.52  bmc1_unsat_core_size:                   -1
% 8.05/1.52  bmc1_unsat_core_parents_size:           -1
% 8.05/1.52  bmc1_merge_next_fun:                    0
% 8.05/1.52  bmc1_unsat_core_clauses_time:           0.
% 8.05/1.52  
% 8.05/1.52  ------ Instantiation
% 8.05/1.52  
% 8.05/1.52  inst_num_of_clauses:                    3824
% 8.05/1.52  inst_num_in_passive:                    1666
% 8.05/1.52  inst_num_in_active:                     985
% 8.05/1.52  inst_num_in_unprocessed:                1173
% 8.05/1.52  inst_num_of_loops:                      1060
% 8.05/1.52  inst_num_of_learning_restarts:          0
% 8.05/1.52  inst_num_moves_active_passive:          69
% 8.05/1.52  inst_lit_activity:                      0
% 8.05/1.52  inst_lit_activity_moves:                1
% 8.05/1.52  inst_num_tautologies:                   0
% 8.05/1.52  inst_num_prop_implied:                  0
% 8.05/1.52  inst_num_existing_simplified:           0
% 8.05/1.52  inst_num_eq_res_simplified:             0
% 8.05/1.52  inst_num_child_elim:                    0
% 8.05/1.52  inst_num_of_dismatching_blockings:      906
% 8.05/1.52  inst_num_of_non_proper_insts:           4837
% 8.05/1.52  inst_num_of_duplicates:                 0
% 8.05/1.52  inst_inst_num_from_inst_to_res:         0
% 8.05/1.52  inst_dismatching_checking_time:         0.
% 8.05/1.52  
% 8.05/1.52  ------ Resolution
% 8.05/1.52  
% 8.05/1.52  res_num_of_clauses:                     0
% 8.05/1.52  res_num_in_passive:                     0
% 8.05/1.52  res_num_in_active:                      0
% 8.05/1.52  res_num_of_loops:                       99
% 8.05/1.52  res_forward_subset_subsumed:            953
% 8.05/1.52  res_backward_subset_subsumed:           0
% 8.05/1.52  res_forward_subsumed:                   0
% 8.05/1.52  res_backward_subsumed:                  0
% 8.05/1.52  res_forward_subsumption_resolution:     0
% 8.05/1.52  res_backward_subsumption_resolution:    0
% 8.05/1.52  res_clause_to_clause_subsumption:       3390
% 8.05/1.52  res_orphan_elimination:                 0
% 8.05/1.52  res_tautology_del:                      427
% 8.05/1.52  res_num_eq_res_simplified:              0
% 8.05/1.52  res_num_sel_changes:                    0
% 8.05/1.52  res_moves_from_active_to_pass:          0
% 8.05/1.52  
% 8.05/1.52  ------ Superposition
% 8.05/1.52  
% 8.05/1.52  sup_time_total:                         0.
% 8.05/1.52  sup_time_generating:                    0.
% 8.05/1.52  sup_time_sim_full:                      0.
% 8.05/1.52  sup_time_sim_immed:                     0.
% 8.05/1.52  
% 8.05/1.52  sup_num_of_clauses:                     991
% 8.05/1.52  sup_num_in_active:                      52
% 8.05/1.52  sup_num_in_passive:                     939
% 8.05/1.52  sup_num_of_loops:                       210
% 8.05/1.52  sup_fw_superposition:                   2943
% 8.05/1.52  sup_bw_superposition:                   691
% 8.05/1.52  sup_immediate_simplified:               2076
% 8.05/1.52  sup_given_eliminated:                   1
% 8.05/1.52  comparisons_done:                       0
% 8.05/1.52  comparisons_avoided:                    0
% 8.05/1.52  
% 8.05/1.52  ------ Simplifications
% 8.05/1.52  
% 8.05/1.52  
% 8.05/1.52  sim_fw_subset_subsumed:                 2
% 8.05/1.52  sim_bw_subset_subsumed:                 10
% 8.05/1.52  sim_fw_subsumed:                        51
% 8.05/1.52  sim_bw_subsumed:                        3
% 8.05/1.52  sim_fw_subsumption_res:                 0
% 8.05/1.52  sim_bw_subsumption_res:                 0
% 8.05/1.52  sim_tautology_del:                      0
% 8.05/1.52  sim_eq_tautology_del:                   314
% 8.05/1.52  sim_eq_res_simp:                        0
% 8.05/1.52  sim_fw_demodulated:                     1551
% 8.05/1.52  sim_bw_demodulated:                     173
% 8.05/1.52  sim_light_normalised:                   672
% 8.05/1.52  sim_joinable_taut:                      0
% 8.05/1.52  sim_joinable_simp:                      0
% 8.05/1.52  sim_ac_normalised:                      0
% 8.05/1.52  sim_smt_subsumption:                    0
% 8.05/1.52  
%------------------------------------------------------------------------------
