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
% DateTime   : Thu Dec  3 11:51:48 EST 2020

% Result     : Theorem 8.01s
% Output     : CNFRefutation 8.01s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 439 expanded)
%              Number of clauses        :   79 ( 164 expanded)
%              Number of leaves         :   20 (  94 expanded)
%              Depth                    :   17
%              Number of atoms          :  266 ( 773 expanded)
%              Number of equality atoms :  146 ( 353 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f67,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f66,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f44])).

fof(f71,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f21,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f73])).

fof(f75,plain,(
    ! [X0,X1] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f53,f74])).

fof(f77,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f69,f75])).

fof(f64,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f68,f75])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_17,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_709,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_710,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_907,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_709,c_710])).

cnf(c_14,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_912,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_907,c_14])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_706,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_718,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X1)
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4931,plain,
    ( k7_relat_1(k7_relat_1(X0,sK0),k1_relat_1(sK1)) = k7_relat_1(X0,sK0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_718])).

cnf(c_5911,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),sK0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),sK0) ),
    inference(superposition,[status(thm)],[c_709,c_4931])).

cnf(c_6137,plain,
    ( k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(sK0),sK0) ),
    inference(superposition,[status(thm)],[c_912,c_5911])).

cnf(c_6148,plain,
    ( k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) = k6_relat_1(sK0) ),
    inference(demodulation,[status(thm)],[c_6137,c_912])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_705,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_712,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2541,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(X1,k1_relat_1(k6_relat_1(X0))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_709,c_712])).

cnf(c_2565,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(X1,X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2541,c_14])).

cnf(c_4005,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_705,c_2565])).

cnf(c_15,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_711,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4356,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4005,c_711])).

cnf(c_30,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7170,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4356,c_30])).

cnf(c_7178,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK0)),k1_relat_1(k7_relat_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6148,c_7170])).

cnf(c_7212,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7178,c_14])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_723,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7905,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7212,c_723])).

cnf(c_23,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_932,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_937,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_932])).

cnf(c_939,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_937])).

cnf(c_1032,plain,
    ( ~ r1_tarski(X0,sK0)
    | ~ r1_tarski(sK0,X0)
    | X0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1289,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0)
    | ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(X0,sK0)))
    | k1_relat_1(k7_relat_1(X0,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_1290,plain,
    ( k1_relat_1(k7_relat_1(X0,sK0)) = sK0
    | r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0) != iProver_top
    | r1_tarski(sK0,k1_relat_1(k7_relat_1(X0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1289])).

cnf(c_1292,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) != iProver_top
    | r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1290])).

cnf(c_23890,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7905,c_23,c_939,c_1292,c_7212])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_720,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_714,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1320,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_720,c_714])).

cnf(c_15684,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_705,c_1320])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_717,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1946,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_705,c_717])).

cnf(c_15710,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_15684,c_1946])).

cnf(c_19,plain,
    ( k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_13,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_998,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_19,c_13])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_708,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_988,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_705,c_708])).

cnf(c_2392,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(sK1,X0)),k6_relat_1(X1))) = k10_relat_1(k7_relat_1(sK1,X1),X0) ),
    inference(superposition,[status(thm)],[c_998,c_988])).

cnf(c_1000,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_998,c_19])).

cnf(c_2403,plain,
    ( k5_relat_1(k6_relat_1(k10_relat_1(sK1,X0)),k6_relat_1(X1)) = k6_relat_1(k10_relat_1(k7_relat_1(sK1,X1),X0)) ),
    inference(superposition,[status(thm)],[c_2392,c_1000])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_713,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3666,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_709,c_713])).

cnf(c_27525,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_709,c_3666])).

cnf(c_1575,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_1000,c_14])).

cnf(c_27555,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(light_normalisation,[status(thm)],[c_27525,c_1575])).

cnf(c_27556,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_27555,c_14])).

cnf(c_27805,plain,
    ( k2_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK1,X0),X1))) = k10_relat_1(k6_relat_1(k10_relat_1(sK1,X1)),X0) ),
    inference(superposition,[status(thm)],[c_2403,c_27556])).

cnf(c_27837,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK1,X0)),X1) = k10_relat_1(k7_relat_1(sK1,X1),X0) ),
    inference(demodulation,[status(thm)],[c_27805,c_13])).

cnf(c_9,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_715,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1804,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_715])).

cnf(c_2677,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1804,c_30])).

cnf(c_27954,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27837,c_2677])).

cnf(c_35046,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15710,c_27954])).

cnf(c_35847,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_23890,c_35046])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_25,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35847,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:36:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 8.01/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.01/1.49  
% 8.01/1.49  ------  iProver source info
% 8.01/1.49  
% 8.01/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.01/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.01/1.49  git: non_committed_changes: false
% 8.01/1.49  git: last_make_outside_of_git: false
% 8.01/1.49  
% 8.01/1.49  ------ 
% 8.01/1.49  
% 8.01/1.49  ------ Input Options
% 8.01/1.49  
% 8.01/1.49  --out_options                           all
% 8.01/1.49  --tptp_safe_out                         true
% 8.01/1.49  --problem_path                          ""
% 8.01/1.49  --include_path                          ""
% 8.01/1.49  --clausifier                            res/vclausify_rel
% 8.01/1.49  --clausifier_options                    --mode clausify
% 8.01/1.49  --stdin                                 false
% 8.01/1.49  --stats_out                             all
% 8.01/1.49  
% 8.01/1.49  ------ General Options
% 8.01/1.49  
% 8.01/1.49  --fof                                   false
% 8.01/1.49  --time_out_real                         305.
% 8.01/1.49  --time_out_virtual                      -1.
% 8.01/1.49  --symbol_type_check                     false
% 8.01/1.49  --clausify_out                          false
% 8.01/1.49  --sig_cnt_out                           false
% 8.01/1.49  --trig_cnt_out                          false
% 8.01/1.49  --trig_cnt_out_tolerance                1.
% 8.01/1.49  --trig_cnt_out_sk_spl                   false
% 8.01/1.49  --abstr_cl_out                          false
% 8.01/1.49  
% 8.01/1.49  ------ Global Options
% 8.01/1.49  
% 8.01/1.49  --schedule                              default
% 8.01/1.49  --add_important_lit                     false
% 8.01/1.49  --prop_solver_per_cl                    1000
% 8.01/1.49  --min_unsat_core                        false
% 8.01/1.49  --soft_assumptions                      false
% 8.01/1.49  --soft_lemma_size                       3
% 8.01/1.49  --prop_impl_unit_size                   0
% 8.01/1.49  --prop_impl_unit                        []
% 8.01/1.49  --share_sel_clauses                     true
% 8.01/1.49  --reset_solvers                         false
% 8.01/1.49  --bc_imp_inh                            [conj_cone]
% 8.01/1.49  --conj_cone_tolerance                   3.
% 8.01/1.49  --extra_neg_conj                        none
% 8.01/1.49  --large_theory_mode                     true
% 8.01/1.49  --prolific_symb_bound                   200
% 8.01/1.49  --lt_threshold                          2000
% 8.01/1.49  --clause_weak_htbl                      true
% 8.01/1.49  --gc_record_bc_elim                     false
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing Options
% 8.01/1.49  
% 8.01/1.49  --preprocessing_flag                    true
% 8.01/1.49  --time_out_prep_mult                    0.1
% 8.01/1.49  --splitting_mode                        input
% 8.01/1.49  --splitting_grd                         true
% 8.01/1.49  --splitting_cvd                         false
% 8.01/1.49  --splitting_cvd_svl                     false
% 8.01/1.49  --splitting_nvd                         32
% 8.01/1.49  --sub_typing                            true
% 8.01/1.49  --prep_gs_sim                           true
% 8.01/1.49  --prep_unflatten                        true
% 8.01/1.49  --prep_res_sim                          true
% 8.01/1.49  --prep_upred                            true
% 8.01/1.49  --prep_sem_filter                       exhaustive
% 8.01/1.49  --prep_sem_filter_out                   false
% 8.01/1.49  --pred_elim                             true
% 8.01/1.49  --res_sim_input                         true
% 8.01/1.49  --eq_ax_congr_red                       true
% 8.01/1.49  --pure_diseq_elim                       true
% 8.01/1.49  --brand_transform                       false
% 8.01/1.49  --non_eq_to_eq                          false
% 8.01/1.49  --prep_def_merge                        true
% 8.01/1.49  --prep_def_merge_prop_impl              false
% 8.01/1.49  --prep_def_merge_mbd                    true
% 8.01/1.49  --prep_def_merge_tr_red                 false
% 8.01/1.49  --prep_def_merge_tr_cl                  false
% 8.01/1.49  --smt_preprocessing                     true
% 8.01/1.49  --smt_ac_axioms                         fast
% 8.01/1.49  --preprocessed_out                      false
% 8.01/1.49  --preprocessed_stats                    false
% 8.01/1.49  
% 8.01/1.49  ------ Abstraction refinement Options
% 8.01/1.49  
% 8.01/1.49  --abstr_ref                             []
% 8.01/1.49  --abstr_ref_prep                        false
% 8.01/1.49  --abstr_ref_until_sat                   false
% 8.01/1.49  --abstr_ref_sig_restrict                funpre
% 8.01/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.01/1.49  --abstr_ref_under                       []
% 8.01/1.49  
% 8.01/1.49  ------ SAT Options
% 8.01/1.49  
% 8.01/1.49  --sat_mode                              false
% 8.01/1.49  --sat_fm_restart_options                ""
% 8.01/1.49  --sat_gr_def                            false
% 8.01/1.49  --sat_epr_types                         true
% 8.01/1.49  --sat_non_cyclic_types                  false
% 8.01/1.49  --sat_finite_models                     false
% 8.01/1.49  --sat_fm_lemmas                         false
% 8.01/1.49  --sat_fm_prep                           false
% 8.01/1.49  --sat_fm_uc_incr                        true
% 8.01/1.49  --sat_out_model                         small
% 8.01/1.49  --sat_out_clauses                       false
% 8.01/1.49  
% 8.01/1.49  ------ QBF Options
% 8.01/1.49  
% 8.01/1.49  --qbf_mode                              false
% 8.01/1.49  --qbf_elim_univ                         false
% 8.01/1.49  --qbf_dom_inst                          none
% 8.01/1.49  --qbf_dom_pre_inst                      false
% 8.01/1.49  --qbf_sk_in                             false
% 8.01/1.49  --qbf_pred_elim                         true
% 8.01/1.49  --qbf_split                             512
% 8.01/1.49  
% 8.01/1.49  ------ BMC1 Options
% 8.01/1.49  
% 8.01/1.49  --bmc1_incremental                      false
% 8.01/1.49  --bmc1_axioms                           reachable_all
% 8.01/1.49  --bmc1_min_bound                        0
% 8.01/1.49  --bmc1_max_bound                        -1
% 8.01/1.49  --bmc1_max_bound_default                -1
% 8.01/1.49  --bmc1_symbol_reachability              true
% 8.01/1.49  --bmc1_property_lemmas                  false
% 8.01/1.49  --bmc1_k_induction                      false
% 8.01/1.49  --bmc1_non_equiv_states                 false
% 8.01/1.49  --bmc1_deadlock                         false
% 8.01/1.49  --bmc1_ucm                              false
% 8.01/1.49  --bmc1_add_unsat_core                   none
% 8.01/1.49  --bmc1_unsat_core_children              false
% 8.01/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.01/1.49  --bmc1_out_stat                         full
% 8.01/1.49  --bmc1_ground_init                      false
% 8.01/1.49  --bmc1_pre_inst_next_state              false
% 8.01/1.49  --bmc1_pre_inst_state                   false
% 8.01/1.49  --bmc1_pre_inst_reach_state             false
% 8.01/1.49  --bmc1_out_unsat_core                   false
% 8.01/1.49  --bmc1_aig_witness_out                  false
% 8.01/1.49  --bmc1_verbose                          false
% 8.01/1.49  --bmc1_dump_clauses_tptp                false
% 8.01/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.01/1.49  --bmc1_dump_file                        -
% 8.01/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.01/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.01/1.49  --bmc1_ucm_extend_mode                  1
% 8.01/1.49  --bmc1_ucm_init_mode                    2
% 8.01/1.49  --bmc1_ucm_cone_mode                    none
% 8.01/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.01/1.49  --bmc1_ucm_relax_model                  4
% 8.01/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.01/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.01/1.49  --bmc1_ucm_layered_model                none
% 8.01/1.49  --bmc1_ucm_max_lemma_size               10
% 8.01/1.49  
% 8.01/1.49  ------ AIG Options
% 8.01/1.49  
% 8.01/1.49  --aig_mode                              false
% 8.01/1.49  
% 8.01/1.49  ------ Instantiation Options
% 8.01/1.49  
% 8.01/1.49  --instantiation_flag                    true
% 8.01/1.49  --inst_sos_flag                         false
% 8.01/1.49  --inst_sos_phase                        true
% 8.01/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.01/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.01/1.49  --inst_lit_sel_side                     num_symb
% 8.01/1.49  --inst_solver_per_active                1400
% 8.01/1.49  --inst_solver_calls_frac                1.
% 8.01/1.49  --inst_passive_queue_type               priority_queues
% 8.01/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.01/1.49  --inst_passive_queues_freq              [25;2]
% 8.01/1.49  --inst_dismatching                      true
% 8.01/1.49  --inst_eager_unprocessed_to_passive     true
% 8.01/1.49  --inst_prop_sim_given                   true
% 8.01/1.49  --inst_prop_sim_new                     false
% 8.01/1.49  --inst_subs_new                         false
% 8.01/1.49  --inst_eq_res_simp                      false
% 8.01/1.49  --inst_subs_given                       false
% 8.01/1.49  --inst_orphan_elimination               true
% 8.01/1.49  --inst_learning_loop_flag               true
% 8.01/1.49  --inst_learning_start                   3000
% 8.01/1.49  --inst_learning_factor                  2
% 8.01/1.49  --inst_start_prop_sim_after_learn       3
% 8.01/1.49  --inst_sel_renew                        solver
% 8.01/1.49  --inst_lit_activity_flag                true
% 8.01/1.49  --inst_restr_to_given                   false
% 8.01/1.49  --inst_activity_threshold               500
% 8.01/1.49  --inst_out_proof                        true
% 8.01/1.49  
% 8.01/1.49  ------ Resolution Options
% 8.01/1.49  
% 8.01/1.49  --resolution_flag                       true
% 8.01/1.49  --res_lit_sel                           adaptive
% 8.01/1.49  --res_lit_sel_side                      none
% 8.01/1.49  --res_ordering                          kbo
% 8.01/1.49  --res_to_prop_solver                    active
% 8.01/1.49  --res_prop_simpl_new                    false
% 8.01/1.49  --res_prop_simpl_given                  true
% 8.01/1.49  --res_passive_queue_type                priority_queues
% 8.01/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.01/1.49  --res_passive_queues_freq               [15;5]
% 8.01/1.49  --res_forward_subs                      full
% 8.01/1.49  --res_backward_subs                     full
% 8.01/1.49  --res_forward_subs_resolution           true
% 8.01/1.49  --res_backward_subs_resolution          true
% 8.01/1.49  --res_orphan_elimination                true
% 8.01/1.49  --res_time_limit                        2.
% 8.01/1.49  --res_out_proof                         true
% 8.01/1.49  
% 8.01/1.49  ------ Superposition Options
% 8.01/1.49  
% 8.01/1.49  --superposition_flag                    true
% 8.01/1.49  --sup_passive_queue_type                priority_queues
% 8.01/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.01/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.01/1.49  --demod_completeness_check              fast
% 8.01/1.49  --demod_use_ground                      true
% 8.01/1.49  --sup_to_prop_solver                    passive
% 8.01/1.49  --sup_prop_simpl_new                    true
% 8.01/1.49  --sup_prop_simpl_given                  true
% 8.01/1.49  --sup_fun_splitting                     false
% 8.01/1.49  --sup_smt_interval                      50000
% 8.01/1.49  
% 8.01/1.49  ------ Superposition Simplification Setup
% 8.01/1.49  
% 8.01/1.49  --sup_indices_passive                   []
% 8.01/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.01/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.01/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.01/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.01/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.01/1.49  --sup_full_bw                           [BwDemod]
% 8.01/1.49  --sup_immed_triv                        [TrivRules]
% 8.01/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.01/1.49  --sup_immed_bw_main                     []
% 8.01/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.01/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.01/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.01/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.01/1.49  
% 8.01/1.49  ------ Combination Options
% 8.01/1.49  
% 8.01/1.49  --comb_res_mult                         3
% 8.01/1.49  --comb_sup_mult                         2
% 8.01/1.49  --comb_inst_mult                        10
% 8.01/1.49  
% 8.01/1.49  ------ Debug Options
% 8.01/1.49  
% 8.01/1.49  --dbg_backtrace                         false
% 8.01/1.49  --dbg_dump_prop_clauses                 false
% 8.01/1.49  --dbg_dump_prop_clauses_file            -
% 8.01/1.49  --dbg_out_stat                          false
% 8.01/1.49  ------ Parsing...
% 8.01/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.01/1.49  ------ Proving...
% 8.01/1.49  ------ Problem Properties 
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  clauses                                 22
% 8.01/1.49  conjectures                             3
% 8.01/1.49  EPR                                     4
% 8.01/1.49  Horn                                    22
% 8.01/1.49  unary                                   8
% 8.01/1.49  binary                                  8
% 8.01/1.49  lits                                    42
% 8.01/1.49  lits eq                                 13
% 8.01/1.49  fd_pure                                 0
% 8.01/1.49  fd_pseudo                               0
% 8.01/1.49  fd_cond                                 0
% 8.01/1.49  fd_pseudo_cond                          1
% 8.01/1.49  AC symbols                              0
% 8.01/1.49  
% 8.01/1.49  ------ Schedule dynamic 5 is on 
% 8.01/1.49  
% 8.01/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  ------ 
% 8.01/1.49  Current options:
% 8.01/1.49  ------ 
% 8.01/1.49  
% 8.01/1.49  ------ Input Options
% 8.01/1.49  
% 8.01/1.49  --out_options                           all
% 8.01/1.49  --tptp_safe_out                         true
% 8.01/1.49  --problem_path                          ""
% 8.01/1.49  --include_path                          ""
% 8.01/1.49  --clausifier                            res/vclausify_rel
% 8.01/1.49  --clausifier_options                    --mode clausify
% 8.01/1.49  --stdin                                 false
% 8.01/1.49  --stats_out                             all
% 8.01/1.49  
% 8.01/1.49  ------ General Options
% 8.01/1.49  
% 8.01/1.49  --fof                                   false
% 8.01/1.49  --time_out_real                         305.
% 8.01/1.49  --time_out_virtual                      -1.
% 8.01/1.49  --symbol_type_check                     false
% 8.01/1.49  --clausify_out                          false
% 8.01/1.49  --sig_cnt_out                           false
% 8.01/1.49  --trig_cnt_out                          false
% 8.01/1.49  --trig_cnt_out_tolerance                1.
% 8.01/1.49  --trig_cnt_out_sk_spl                   false
% 8.01/1.49  --abstr_cl_out                          false
% 8.01/1.49  
% 8.01/1.49  ------ Global Options
% 8.01/1.49  
% 8.01/1.49  --schedule                              default
% 8.01/1.49  --add_important_lit                     false
% 8.01/1.49  --prop_solver_per_cl                    1000
% 8.01/1.49  --min_unsat_core                        false
% 8.01/1.49  --soft_assumptions                      false
% 8.01/1.49  --soft_lemma_size                       3
% 8.01/1.49  --prop_impl_unit_size                   0
% 8.01/1.49  --prop_impl_unit                        []
% 8.01/1.49  --share_sel_clauses                     true
% 8.01/1.49  --reset_solvers                         false
% 8.01/1.49  --bc_imp_inh                            [conj_cone]
% 8.01/1.49  --conj_cone_tolerance                   3.
% 8.01/1.49  --extra_neg_conj                        none
% 8.01/1.49  --large_theory_mode                     true
% 8.01/1.49  --prolific_symb_bound                   200
% 8.01/1.49  --lt_threshold                          2000
% 8.01/1.49  --clause_weak_htbl                      true
% 8.01/1.49  --gc_record_bc_elim                     false
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing Options
% 8.01/1.49  
% 8.01/1.49  --preprocessing_flag                    true
% 8.01/1.49  --time_out_prep_mult                    0.1
% 8.01/1.49  --splitting_mode                        input
% 8.01/1.49  --splitting_grd                         true
% 8.01/1.49  --splitting_cvd                         false
% 8.01/1.49  --splitting_cvd_svl                     false
% 8.01/1.49  --splitting_nvd                         32
% 8.01/1.49  --sub_typing                            true
% 8.01/1.49  --prep_gs_sim                           true
% 8.01/1.49  --prep_unflatten                        true
% 8.01/1.49  --prep_res_sim                          true
% 8.01/1.49  --prep_upred                            true
% 8.01/1.49  --prep_sem_filter                       exhaustive
% 8.01/1.49  --prep_sem_filter_out                   false
% 8.01/1.49  --pred_elim                             true
% 8.01/1.49  --res_sim_input                         true
% 8.01/1.49  --eq_ax_congr_red                       true
% 8.01/1.49  --pure_diseq_elim                       true
% 8.01/1.49  --brand_transform                       false
% 8.01/1.49  --non_eq_to_eq                          false
% 8.01/1.49  --prep_def_merge                        true
% 8.01/1.49  --prep_def_merge_prop_impl              false
% 8.01/1.49  --prep_def_merge_mbd                    true
% 8.01/1.49  --prep_def_merge_tr_red                 false
% 8.01/1.49  --prep_def_merge_tr_cl                  false
% 8.01/1.49  --smt_preprocessing                     true
% 8.01/1.49  --smt_ac_axioms                         fast
% 8.01/1.49  --preprocessed_out                      false
% 8.01/1.49  --preprocessed_stats                    false
% 8.01/1.49  
% 8.01/1.49  ------ Abstraction refinement Options
% 8.01/1.49  
% 8.01/1.49  --abstr_ref                             []
% 8.01/1.49  --abstr_ref_prep                        false
% 8.01/1.49  --abstr_ref_until_sat                   false
% 8.01/1.49  --abstr_ref_sig_restrict                funpre
% 8.01/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.01/1.49  --abstr_ref_under                       []
% 8.01/1.49  
% 8.01/1.49  ------ SAT Options
% 8.01/1.49  
% 8.01/1.49  --sat_mode                              false
% 8.01/1.49  --sat_fm_restart_options                ""
% 8.01/1.49  --sat_gr_def                            false
% 8.01/1.49  --sat_epr_types                         true
% 8.01/1.49  --sat_non_cyclic_types                  false
% 8.01/1.49  --sat_finite_models                     false
% 8.01/1.49  --sat_fm_lemmas                         false
% 8.01/1.49  --sat_fm_prep                           false
% 8.01/1.49  --sat_fm_uc_incr                        true
% 8.01/1.49  --sat_out_model                         small
% 8.01/1.49  --sat_out_clauses                       false
% 8.01/1.49  
% 8.01/1.49  ------ QBF Options
% 8.01/1.49  
% 8.01/1.49  --qbf_mode                              false
% 8.01/1.49  --qbf_elim_univ                         false
% 8.01/1.49  --qbf_dom_inst                          none
% 8.01/1.49  --qbf_dom_pre_inst                      false
% 8.01/1.49  --qbf_sk_in                             false
% 8.01/1.49  --qbf_pred_elim                         true
% 8.01/1.49  --qbf_split                             512
% 8.01/1.49  
% 8.01/1.49  ------ BMC1 Options
% 8.01/1.49  
% 8.01/1.49  --bmc1_incremental                      false
% 8.01/1.49  --bmc1_axioms                           reachable_all
% 8.01/1.49  --bmc1_min_bound                        0
% 8.01/1.49  --bmc1_max_bound                        -1
% 8.01/1.49  --bmc1_max_bound_default                -1
% 8.01/1.49  --bmc1_symbol_reachability              true
% 8.01/1.49  --bmc1_property_lemmas                  false
% 8.01/1.49  --bmc1_k_induction                      false
% 8.01/1.49  --bmc1_non_equiv_states                 false
% 8.01/1.49  --bmc1_deadlock                         false
% 8.01/1.49  --bmc1_ucm                              false
% 8.01/1.49  --bmc1_add_unsat_core                   none
% 8.01/1.49  --bmc1_unsat_core_children              false
% 8.01/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.01/1.49  --bmc1_out_stat                         full
% 8.01/1.49  --bmc1_ground_init                      false
% 8.01/1.49  --bmc1_pre_inst_next_state              false
% 8.01/1.49  --bmc1_pre_inst_state                   false
% 8.01/1.49  --bmc1_pre_inst_reach_state             false
% 8.01/1.49  --bmc1_out_unsat_core                   false
% 8.01/1.49  --bmc1_aig_witness_out                  false
% 8.01/1.49  --bmc1_verbose                          false
% 8.01/1.49  --bmc1_dump_clauses_tptp                false
% 8.01/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.01/1.49  --bmc1_dump_file                        -
% 8.01/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.01/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.01/1.49  --bmc1_ucm_extend_mode                  1
% 8.01/1.49  --bmc1_ucm_init_mode                    2
% 8.01/1.49  --bmc1_ucm_cone_mode                    none
% 8.01/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.01/1.49  --bmc1_ucm_relax_model                  4
% 8.01/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.01/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.01/1.49  --bmc1_ucm_layered_model                none
% 8.01/1.49  --bmc1_ucm_max_lemma_size               10
% 8.01/1.49  
% 8.01/1.49  ------ AIG Options
% 8.01/1.49  
% 8.01/1.49  --aig_mode                              false
% 8.01/1.49  
% 8.01/1.49  ------ Instantiation Options
% 8.01/1.49  
% 8.01/1.49  --instantiation_flag                    true
% 8.01/1.49  --inst_sos_flag                         false
% 8.01/1.49  --inst_sos_phase                        true
% 8.01/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.01/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.01/1.49  --inst_lit_sel_side                     none
% 8.01/1.49  --inst_solver_per_active                1400
% 8.01/1.49  --inst_solver_calls_frac                1.
% 8.01/1.49  --inst_passive_queue_type               priority_queues
% 8.01/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.01/1.49  --inst_passive_queues_freq              [25;2]
% 8.01/1.49  --inst_dismatching                      true
% 8.01/1.49  --inst_eager_unprocessed_to_passive     true
% 8.01/1.49  --inst_prop_sim_given                   true
% 8.01/1.49  --inst_prop_sim_new                     false
% 8.01/1.49  --inst_subs_new                         false
% 8.01/1.49  --inst_eq_res_simp                      false
% 8.01/1.49  --inst_subs_given                       false
% 8.01/1.49  --inst_orphan_elimination               true
% 8.01/1.49  --inst_learning_loop_flag               true
% 8.01/1.49  --inst_learning_start                   3000
% 8.01/1.49  --inst_learning_factor                  2
% 8.01/1.49  --inst_start_prop_sim_after_learn       3
% 8.01/1.49  --inst_sel_renew                        solver
% 8.01/1.49  --inst_lit_activity_flag                true
% 8.01/1.49  --inst_restr_to_given                   false
% 8.01/1.49  --inst_activity_threshold               500
% 8.01/1.49  --inst_out_proof                        true
% 8.01/1.49  
% 8.01/1.49  ------ Resolution Options
% 8.01/1.49  
% 8.01/1.49  --resolution_flag                       false
% 8.01/1.49  --res_lit_sel                           adaptive
% 8.01/1.49  --res_lit_sel_side                      none
% 8.01/1.49  --res_ordering                          kbo
% 8.01/1.49  --res_to_prop_solver                    active
% 8.01/1.49  --res_prop_simpl_new                    false
% 8.01/1.49  --res_prop_simpl_given                  true
% 8.01/1.49  --res_passive_queue_type                priority_queues
% 8.01/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.01/1.49  --res_passive_queues_freq               [15;5]
% 8.01/1.49  --res_forward_subs                      full
% 8.01/1.49  --res_backward_subs                     full
% 8.01/1.49  --res_forward_subs_resolution           true
% 8.01/1.49  --res_backward_subs_resolution          true
% 8.01/1.49  --res_orphan_elimination                true
% 8.01/1.49  --res_time_limit                        2.
% 8.01/1.49  --res_out_proof                         true
% 8.01/1.49  
% 8.01/1.49  ------ Superposition Options
% 8.01/1.49  
% 8.01/1.49  --superposition_flag                    true
% 8.01/1.49  --sup_passive_queue_type                priority_queues
% 8.01/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.01/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.01/1.49  --demod_completeness_check              fast
% 8.01/1.49  --demod_use_ground                      true
% 8.01/1.49  --sup_to_prop_solver                    passive
% 8.01/1.49  --sup_prop_simpl_new                    true
% 8.01/1.49  --sup_prop_simpl_given                  true
% 8.01/1.49  --sup_fun_splitting                     false
% 8.01/1.49  --sup_smt_interval                      50000
% 8.01/1.49  
% 8.01/1.49  ------ Superposition Simplification Setup
% 8.01/1.49  
% 8.01/1.49  --sup_indices_passive                   []
% 8.01/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.01/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.01/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.01/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.01/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.01/1.49  --sup_full_bw                           [BwDemod]
% 8.01/1.49  --sup_immed_triv                        [TrivRules]
% 8.01/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.01/1.49  --sup_immed_bw_main                     []
% 8.01/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.01/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.01/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.01/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.01/1.49  
% 8.01/1.49  ------ Combination Options
% 8.01/1.49  
% 8.01/1.49  --comb_res_mult                         3
% 8.01/1.49  --comb_sup_mult                         2
% 8.01/1.49  --comb_inst_mult                        10
% 8.01/1.49  
% 8.01/1.49  ------ Debug Options
% 8.01/1.49  
% 8.01/1.49  --dbg_backtrace                         false
% 8.01/1.49  --dbg_dump_prop_clauses                 false
% 8.01/1.49  --dbg_dump_prop_clauses_file            -
% 8.01/1.49  --dbg_out_stat                          false
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  ------ Proving...
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  % SZS status Theorem for theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  fof(f19,axiom,(
% 8.01/1.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f24,plain,(
% 8.01/1.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 8.01/1.49    inference(pure_predicate_removal,[],[f19])).
% 8.01/1.49  
% 8.01/1.49  fof(f67,plain,(
% 8.01/1.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 8.01/1.49    inference(cnf_transformation,[],[f24])).
% 8.01/1.49  
% 8.01/1.49  fof(f18,axiom,(
% 8.01/1.49    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f38,plain,(
% 8.01/1.49    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f18])).
% 8.01/1.49  
% 8.01/1.49  fof(f66,plain,(
% 8.01/1.49    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f38])).
% 8.01/1.49  
% 8.01/1.49  fof(f16,axiom,(
% 8.01/1.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f63,plain,(
% 8.01/1.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 8.01/1.49    inference(cnf_transformation,[],[f16])).
% 8.01/1.49  
% 8.01/1.49  fof(f22,conjecture,(
% 8.01/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f23,negated_conjecture,(
% 8.01/1.49    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 8.01/1.49    inference(negated_conjecture,[],[f22])).
% 8.01/1.49  
% 8.01/1.49  fof(f40,plain,(
% 8.01/1.49    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 8.01/1.49    inference(ennf_transformation,[],[f23])).
% 8.01/1.49  
% 8.01/1.49  fof(f41,plain,(
% 8.01/1.49    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 8.01/1.49    inference(flattening,[],[f40])).
% 8.01/1.49  
% 8.01/1.49  fof(f44,plain,(
% 8.01/1.49    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 8.01/1.49    introduced(choice_axiom,[])).
% 8.01/1.49  
% 8.01/1.49  fof(f45,plain,(
% 8.01/1.49    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 8.01/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f44])).
% 8.01/1.49  
% 8.01/1.49  fof(f71,plain,(
% 8.01/1.49    r1_tarski(sK0,k1_relat_1(sK1))),
% 8.01/1.49    inference(cnf_transformation,[],[f45])).
% 8.01/1.49  
% 8.01/1.49  fof(f9,axiom,(
% 8.01/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f29,plain,(
% 8.01/1.49    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 8.01/1.49    inference(ennf_transformation,[],[f9])).
% 8.01/1.49  
% 8.01/1.49  fof(f30,plain,(
% 8.01/1.49    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 8.01/1.49    inference(flattening,[],[f29])).
% 8.01/1.49  
% 8.01/1.49  fof(f56,plain,(
% 8.01/1.49    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f30])).
% 8.01/1.49  
% 8.01/1.49  fof(f70,plain,(
% 8.01/1.49    v1_relat_1(sK1)),
% 8.01/1.49    inference(cnf_transformation,[],[f45])).
% 8.01/1.49  
% 8.01/1.49  fof(f15,axiom,(
% 8.01/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f36,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f15])).
% 8.01/1.49  
% 8.01/1.49  fof(f62,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f36])).
% 8.01/1.49  
% 8.01/1.49  fof(f17,axiom,(
% 8.01/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f37,plain,(
% 8.01/1.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 8.01/1.49    inference(ennf_transformation,[],[f17])).
% 8.01/1.49  
% 8.01/1.49  fof(f65,plain,(
% 8.01/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f37])).
% 8.01/1.49  
% 8.01/1.49  fof(f1,axiom,(
% 8.01/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f42,plain,(
% 8.01/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.01/1.49    inference(nnf_transformation,[],[f1])).
% 8.01/1.49  
% 8.01/1.49  fof(f43,plain,(
% 8.01/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.01/1.49    inference(flattening,[],[f42])).
% 8.01/1.49  
% 8.01/1.49  fof(f48,plain,(
% 8.01/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f43])).
% 8.01/1.49  
% 8.01/1.49  fof(f7,axiom,(
% 8.01/1.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f27,plain,(
% 8.01/1.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f7])).
% 8.01/1.49  
% 8.01/1.49  fof(f54,plain,(
% 8.01/1.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f27])).
% 8.01/1.49  
% 8.01/1.49  fof(f13,axiom,(
% 8.01/1.49    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f34,plain,(
% 8.01/1.49    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f13])).
% 8.01/1.49  
% 8.01/1.49  fof(f60,plain,(
% 8.01/1.49    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f34])).
% 8.01/1.49  
% 8.01/1.49  fof(f10,axiom,(
% 8.01/1.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f31,plain,(
% 8.01/1.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 8.01/1.49    inference(ennf_transformation,[],[f10])).
% 8.01/1.49  
% 8.01/1.49  fof(f57,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f31])).
% 8.01/1.49  
% 8.01/1.49  fof(f21,axiom,(
% 8.01/1.49    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f69,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 8.01/1.49    inference(cnf_transformation,[],[f21])).
% 8.01/1.49  
% 8.01/1.49  fof(f6,axiom,(
% 8.01/1.49    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f53,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f6])).
% 8.01/1.49  
% 8.01/1.49  fof(f3,axiom,(
% 8.01/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f50,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f3])).
% 8.01/1.49  
% 8.01/1.49  fof(f4,axiom,(
% 8.01/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f51,plain,(
% 8.01/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f4])).
% 8.01/1.49  
% 8.01/1.49  fof(f5,axiom,(
% 8.01/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f52,plain,(
% 8.01/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f5])).
% 8.01/1.49  
% 8.01/1.49  fof(f73,plain,(
% 8.01/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 8.01/1.49    inference(definition_unfolding,[],[f51,f52])).
% 8.01/1.49  
% 8.01/1.49  fof(f74,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 8.01/1.49    inference(definition_unfolding,[],[f50,f73])).
% 8.01/1.49  
% 8.01/1.49  fof(f75,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 8.01/1.49    inference(definition_unfolding,[],[f53,f74])).
% 8.01/1.49  
% 8.01/1.49  fof(f77,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 8.01/1.49    inference(definition_unfolding,[],[f69,f75])).
% 8.01/1.49  
% 8.01/1.49  fof(f64,plain,(
% 8.01/1.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 8.01/1.49    inference(cnf_transformation,[],[f16])).
% 8.01/1.49  
% 8.01/1.49  fof(f20,axiom,(
% 8.01/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f39,plain,(
% 8.01/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 8.01/1.49    inference(ennf_transformation,[],[f20])).
% 8.01/1.49  
% 8.01/1.49  fof(f68,plain,(
% 8.01/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f39])).
% 8.01/1.49  
% 8.01/1.49  fof(f76,plain,(
% 8.01/1.49    ( ! [X2,X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 8.01/1.49    inference(definition_unfolding,[],[f68,f75])).
% 8.01/1.49  
% 8.01/1.49  fof(f14,axiom,(
% 8.01/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f35,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f14])).
% 8.01/1.49  
% 8.01/1.49  fof(f61,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f35])).
% 8.01/1.49  
% 8.01/1.49  fof(f12,axiom,(
% 8.01/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f33,plain,(
% 8.01/1.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 8.01/1.49    inference(ennf_transformation,[],[f12])).
% 8.01/1.49  
% 8.01/1.49  fof(f59,plain,(
% 8.01/1.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f33])).
% 8.01/1.49  
% 8.01/1.49  fof(f72,plain,(
% 8.01/1.49    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 8.01/1.49    inference(cnf_transformation,[],[f45])).
% 8.01/1.49  
% 8.01/1.49  cnf(c_17,plain,
% 8.01/1.49      ( v1_relat_1(k6_relat_1(X0)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f67]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_709,plain,
% 8.01/1.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_16,plain,
% 8.01/1.49      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 8.01/1.49      inference(cnf_transformation,[],[f66]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_710,plain,
% 8.01/1.49      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 8.01/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_907,plain,
% 8.01/1.49      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_709,c_710]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_14,plain,
% 8.01/1.49      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 8.01/1.49      inference(cnf_transformation,[],[f63]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_912,plain,
% 8.01/1.49      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 8.01/1.49      inference(light_normalisation,[status(thm)],[c_907,c_14]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_21,negated_conjecture,
% 8.01/1.49      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f71]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_706,plain,
% 8.01/1.49      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_6,plain,
% 8.01/1.49      ( ~ r1_tarski(X0,X1)
% 8.01/1.49      | ~ v1_relat_1(X2)
% 8.01/1.49      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f56]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_718,plain,
% 8.01/1.49      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X1)
% 8.01/1.49      | r1_tarski(X1,X2) != iProver_top
% 8.01/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_4931,plain,
% 8.01/1.49      ( k7_relat_1(k7_relat_1(X0,sK0),k1_relat_1(sK1)) = k7_relat_1(X0,sK0)
% 8.01/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_706,c_718]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_5911,plain,
% 8.01/1.49      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),sK0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),sK0) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_709,c_4931]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_6137,plain,
% 8.01/1.49      ( k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(sK0),sK0) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_912,c_5911]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_6148,plain,
% 8.01/1.49      ( k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) = k6_relat_1(sK0) ),
% 8.01/1.49      inference(demodulation,[status(thm)],[c_6137,c_912]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_22,negated_conjecture,
% 8.01/1.49      ( v1_relat_1(sK1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f70]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_705,plain,
% 8.01/1.49      ( v1_relat_1(sK1) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_12,plain,
% 8.01/1.49      ( ~ v1_relat_1(X0)
% 8.01/1.49      | ~ v1_relat_1(X1)
% 8.01/1.49      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f62]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_712,plain,
% 8.01/1.49      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1))
% 8.01/1.49      | v1_relat_1(X0) != iProver_top
% 8.01/1.49      | v1_relat_1(X1) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2541,plain,
% 8.01/1.49      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(X1,k1_relat_1(k6_relat_1(X0))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(X1))
% 8.01/1.49      | v1_relat_1(X1) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_709,c_712]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2565,plain,
% 8.01/1.49      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(X1,X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(X1))
% 8.01/1.49      | v1_relat_1(X1) != iProver_top ),
% 8.01/1.49      inference(light_normalisation,[status(thm)],[c_2541,c_14]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_4005,plain,
% 8.01/1.49      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_705,c_2565]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_15,plain,
% 8.01/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f65]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_711,plain,
% 8.01/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 8.01/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_4356,plain,
% 8.01/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top
% 8.01/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_4005,c_711]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_30,plain,
% 8.01/1.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_7170,plain,
% 8.01/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_4356,c_30]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_7178,plain,
% 8.01/1.49      ( r1_tarski(k1_relat_1(k6_relat_1(sK0)),k1_relat_1(k7_relat_1(sK1,sK0))) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_6148,c_7170]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_7212,plain,
% 8.01/1.49      ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = iProver_top ),
% 8.01/1.49      inference(demodulation,[status(thm)],[c_7178,c_14]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_0,plain,
% 8.01/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 8.01/1.49      inference(cnf_transformation,[],[f48]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_723,plain,
% 8.01/1.49      ( X0 = X1
% 8.01/1.49      | r1_tarski(X0,X1) != iProver_top
% 8.01/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_7905,plain,
% 8.01/1.49      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
% 8.01/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_7212,c_723]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_23,plain,
% 8.01/1.49      ( v1_relat_1(sK1) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_932,plain,
% 8.01/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0)
% 8.01/1.49      | ~ v1_relat_1(X0) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_15]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_937,plain,
% 8.01/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0) = iProver_top
% 8.01/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_932]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_939,plain,
% 8.01/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) = iProver_top
% 8.01/1.49      | v1_relat_1(sK1) != iProver_top ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_937]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1032,plain,
% 8.01/1.49      ( ~ r1_tarski(X0,sK0) | ~ r1_tarski(sK0,X0) | X0 = sK0 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1289,plain,
% 8.01/1.49      ( ~ r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0)
% 8.01/1.49      | ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(X0,sK0)))
% 8.01/1.49      | k1_relat_1(k7_relat_1(X0,sK0)) = sK0 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_1032]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1290,plain,
% 8.01/1.49      ( k1_relat_1(k7_relat_1(X0,sK0)) = sK0
% 8.01/1.49      | r1_tarski(k1_relat_1(k7_relat_1(X0,sK0)),sK0) != iProver_top
% 8.01/1.49      | r1_tarski(sK0,k1_relat_1(k7_relat_1(X0,sK0))) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_1289]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1292,plain,
% 8.01/1.49      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
% 8.01/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) != iProver_top
% 8.01/1.49      | r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) != iProver_top ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_1290]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_23890,plain,
% 8.01/1.49      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_7905,c_23,c_939,c_1292,c_7212]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_4,plain,
% 8.01/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f54]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_720,plain,
% 8.01/1.49      ( v1_relat_1(X0) != iProver_top
% 8.01/1.49      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10,plain,
% 8.01/1.49      ( ~ v1_relat_1(X0)
% 8.01/1.49      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f60]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_714,plain,
% 8.01/1.49      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 8.01/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1320,plain,
% 8.01/1.49      ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
% 8.01/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_720,c_714]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_15684,plain,
% 8.01/1.49      ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_705,c_1320]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_7,plain,
% 8.01/1.49      ( ~ v1_relat_1(X0)
% 8.01/1.49      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f57]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_717,plain,
% 8.01/1.49      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 8.01/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1946,plain,
% 8.01/1.49      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_705,c_717]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_15710,plain,
% 8.01/1.49      ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 8.01/1.49      inference(light_normalisation,[status(thm)],[c_15684,c_1946]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_19,plain,
% 8.01/1.49      ( k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f77]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_13,plain,
% 8.01/1.49      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 8.01/1.49      inference(cnf_transformation,[],[f64]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_998,plain,
% 8.01/1.49      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_19,c_13]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_18,plain,
% 8.01/1.49      ( ~ v1_relat_1(X0)
% 8.01/1.49      | k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 8.01/1.49      inference(cnf_transformation,[],[f76]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_708,plain,
% 8.01/1.49      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 8.01/1.49      | v1_relat_1(X1) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_988,plain,
% 8.01/1.49      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_705,c_708]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2392,plain,
% 8.01/1.49      ( k2_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(sK1,X0)),k6_relat_1(X1))) = k10_relat_1(k7_relat_1(sK1,X1),X0) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_998,c_988]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1000,plain,
% 8.01/1.49      ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 8.01/1.49      inference(demodulation,[status(thm)],[c_998,c_19]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2403,plain,
% 8.01/1.49      ( k5_relat_1(k6_relat_1(k10_relat_1(sK1,X0)),k6_relat_1(X1)) = k6_relat_1(k10_relat_1(k7_relat_1(sK1,X1),X0)) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_2392,c_1000]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_11,plain,
% 8.01/1.49      ( ~ v1_relat_1(X0)
% 8.01/1.49      | ~ v1_relat_1(X1)
% 8.01/1.49      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f61]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_713,plain,
% 8.01/1.49      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
% 8.01/1.49      | v1_relat_1(X0) != iProver_top
% 8.01/1.49      | v1_relat_1(X1) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3666,plain,
% 8.01/1.49      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(X1))
% 8.01/1.49      | v1_relat_1(X1) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_709,c_713]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_27525,plain,
% 8.01/1.49      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_709,c_3666]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1575,plain,
% 8.01/1.49      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1000,c_14]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_27555,plain,
% 8.01/1.49      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
% 8.01/1.49      inference(light_normalisation,[status(thm)],[c_27525,c_1575]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_27556,plain,
% 8.01/1.49      ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
% 8.01/1.49      inference(demodulation,[status(thm)],[c_27555,c_14]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_27805,plain,
% 8.01/1.49      ( k2_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK1,X0),X1))) = k10_relat_1(k6_relat_1(k10_relat_1(sK1,X1)),X0) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_2403,c_27556]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_27837,plain,
% 8.01/1.49      ( k10_relat_1(k6_relat_1(k10_relat_1(sK1,X0)),X1) = k10_relat_1(k7_relat_1(sK1,X1),X0) ),
% 8.01/1.49      inference(demodulation,[status(thm)],[c_27805,c_13]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9,plain,
% 8.01/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f59]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_715,plain,
% 8.01/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 8.01/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1804,plain,
% 8.01/1.49      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top
% 8.01/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_14,c_715]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2677,plain,
% 8.01/1.49      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_1804,c_30]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_27954,plain,
% 8.01/1.49      ( r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1)) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_27837,c_2677]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_35046,plain,
% 8.01/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_15710,c_27954]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_35847,plain,
% 8.01/1.49      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_23890,c_35046]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_20,negated_conjecture,
% 8.01/1.49      ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 8.01/1.49      inference(cnf_transformation,[],[f72]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_25,plain,
% 8.01/1.49      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(contradiction,plain,
% 8.01/1.49      ( $false ),
% 8.01/1.49      inference(minisat,[status(thm)],[c_35847,c_25]) ).
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  ------                               Statistics
% 8.01/1.49  
% 8.01/1.49  ------ General
% 8.01/1.49  
% 8.01/1.49  abstr_ref_over_cycles:                  0
% 8.01/1.49  abstr_ref_under_cycles:                 0
% 8.01/1.49  gc_basic_clause_elim:                   0
% 8.01/1.49  forced_gc_time:                         0
% 8.01/1.49  parsing_time:                           0.013
% 8.01/1.49  unif_index_cands_time:                  0.
% 8.01/1.49  unif_index_add_time:                    0.
% 8.01/1.49  orderings_time:                         0.
% 8.01/1.49  out_proof_time:                         0.011
% 8.01/1.49  total_time:                             0.955
% 8.01/1.49  num_of_symbols:                         44
% 8.01/1.49  num_of_terms:                           35839
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing
% 8.01/1.49  
% 8.01/1.49  num_of_splits:                          0
% 8.01/1.49  num_of_split_atoms:                     0
% 8.01/1.49  num_of_reused_defs:                     0
% 8.01/1.49  num_eq_ax_congr_red:                    12
% 8.01/1.49  num_of_sem_filtered_clauses:            1
% 8.01/1.49  num_of_subtypes:                        0
% 8.01/1.49  monotx_restored_types:                  0
% 8.01/1.49  sat_num_of_epr_types:                   0
% 8.01/1.49  sat_num_of_non_cyclic_types:            0
% 8.01/1.49  sat_guarded_non_collapsed_types:        0
% 8.01/1.49  num_pure_diseq_elim:                    0
% 8.01/1.49  simp_replaced_by:                       0
% 8.01/1.49  res_preprocessed:                       115
% 8.01/1.49  prep_upred:                             0
% 8.01/1.49  prep_unflattend:                        0
% 8.01/1.49  smt_new_axioms:                         0
% 8.01/1.49  pred_elim_cands:                        2
% 8.01/1.49  pred_elim:                              0
% 8.01/1.49  pred_elim_cl:                           0
% 8.01/1.49  pred_elim_cycles:                       2
% 8.01/1.49  merged_defs:                            0
% 8.01/1.49  merged_defs_ncl:                        0
% 8.01/1.49  bin_hyper_res:                          0
% 8.01/1.49  prep_cycles:                            4
% 8.01/1.49  pred_elim_time:                         0.
% 8.01/1.49  splitting_time:                         0.
% 8.01/1.49  sem_filter_time:                        0.
% 8.01/1.49  monotx_time:                            0.
% 8.01/1.49  subtype_inf_time:                       0.
% 8.01/1.49  
% 8.01/1.49  ------ Problem properties
% 8.01/1.49  
% 8.01/1.49  clauses:                                22
% 8.01/1.49  conjectures:                            3
% 8.01/1.49  epr:                                    4
% 8.01/1.49  horn:                                   22
% 8.01/1.49  ground:                                 3
% 8.01/1.49  unary:                                  8
% 8.01/1.49  binary:                                 8
% 8.01/1.49  lits:                                   42
% 8.01/1.49  lits_eq:                                13
% 8.01/1.49  fd_pure:                                0
% 8.01/1.49  fd_pseudo:                              0
% 8.01/1.49  fd_cond:                                0
% 8.01/1.49  fd_pseudo_cond:                         1
% 8.01/1.49  ac_symbols:                             0
% 8.01/1.49  
% 8.01/1.49  ------ Propositional Solver
% 8.01/1.49  
% 8.01/1.49  prop_solver_calls:                      32
% 8.01/1.49  prop_fast_solver_calls:                 796
% 8.01/1.49  smt_solver_calls:                       0
% 8.01/1.49  smt_fast_solver_calls:                  0
% 8.01/1.49  prop_num_of_clauses:                    11692
% 8.01/1.49  prop_preprocess_simplified:             20589
% 8.01/1.49  prop_fo_subsumed:                       7
% 8.01/1.49  prop_solver_time:                       0.
% 8.01/1.49  smt_solver_time:                        0.
% 8.01/1.49  smt_fast_solver_time:                   0.
% 8.01/1.49  prop_fast_solver_time:                  0.
% 8.01/1.49  prop_unsat_core_time:                   0.001
% 8.01/1.49  
% 8.01/1.49  ------ QBF
% 8.01/1.49  
% 8.01/1.49  qbf_q_res:                              0
% 8.01/1.49  qbf_num_tautologies:                    0
% 8.01/1.49  qbf_prep_cycles:                        0
% 8.01/1.49  
% 8.01/1.49  ------ BMC1
% 8.01/1.49  
% 8.01/1.49  bmc1_current_bound:                     -1
% 8.01/1.49  bmc1_last_solved_bound:                 -1
% 8.01/1.49  bmc1_unsat_core_size:                   -1
% 8.01/1.49  bmc1_unsat_core_parents_size:           -1
% 8.01/1.49  bmc1_merge_next_fun:                    0
% 8.01/1.49  bmc1_unsat_core_clauses_time:           0.
% 8.01/1.49  
% 8.01/1.49  ------ Instantiation
% 8.01/1.49  
% 8.01/1.49  inst_num_of_clauses:                    3350
% 8.01/1.49  inst_num_in_passive:                    1383
% 8.01/1.49  inst_num_in_active:                     1227
% 8.01/1.49  inst_num_in_unprocessed:                740
% 8.01/1.49  inst_num_of_loops:                      1250
% 8.01/1.49  inst_num_of_learning_restarts:          0
% 8.01/1.49  inst_num_moves_active_passive:          18
% 8.01/1.49  inst_lit_activity:                      0
% 8.01/1.49  inst_lit_activity_moves:                0
% 8.01/1.49  inst_num_tautologies:                   0
% 8.01/1.49  inst_num_prop_implied:                  0
% 8.01/1.49  inst_num_existing_simplified:           0
% 8.01/1.49  inst_num_eq_res_simplified:             0
% 8.01/1.49  inst_num_child_elim:                    0
% 8.01/1.49  inst_num_of_dismatching_blockings:      1869
% 8.01/1.49  inst_num_of_non_proper_insts:           4555
% 8.01/1.49  inst_num_of_duplicates:                 0
% 8.01/1.49  inst_inst_num_from_inst_to_res:         0
% 8.01/1.49  inst_dismatching_checking_time:         0.
% 8.01/1.49  
% 8.01/1.49  ------ Resolution
% 8.01/1.49  
% 8.01/1.49  res_num_of_clauses:                     0
% 8.01/1.49  res_num_in_passive:                     0
% 8.01/1.49  res_num_in_active:                      0
% 8.01/1.49  res_num_of_loops:                       119
% 8.01/1.49  res_forward_subset_subsumed:            909
% 8.01/1.49  res_backward_subset_subsumed:           0
% 8.01/1.49  res_forward_subsumed:                   0
% 8.01/1.49  res_backward_subsumed:                  0
% 8.01/1.49  res_forward_subsumption_resolution:     0
% 8.01/1.49  res_backward_subsumption_resolution:    0
% 8.01/1.49  res_clause_to_clause_subsumption:       4501
% 8.01/1.49  res_orphan_elimination:                 0
% 8.01/1.49  res_tautology_del:                      468
% 8.01/1.49  res_num_eq_res_simplified:              0
% 8.01/1.49  res_num_sel_changes:                    0
% 8.01/1.49  res_moves_from_active_to_pass:          0
% 8.01/1.49  
% 8.01/1.49  ------ Superposition
% 8.01/1.49  
% 8.01/1.49  sup_time_total:                         0.
% 8.01/1.49  sup_time_generating:                    0.
% 8.01/1.49  sup_time_sim_full:                      0.
% 8.01/1.49  sup_time_sim_immed:                     0.
% 8.01/1.49  
% 8.01/1.49  sup_num_of_clauses:                     1297
% 8.01/1.49  sup_num_in_active:                      157
% 8.01/1.49  sup_num_in_passive:                     1140
% 8.01/1.49  sup_num_of_loops:                       249
% 8.01/1.49  sup_fw_superposition:                   1954
% 8.01/1.49  sup_bw_superposition:                   1284
% 8.01/1.49  sup_immediate_simplified:               2647
% 8.01/1.49  sup_given_eliminated:                   7
% 8.01/1.49  comparisons_done:                       0
% 8.01/1.49  comparisons_avoided:                    0
% 8.01/1.49  
% 8.01/1.49  ------ Simplifications
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  sim_fw_subset_subsumed:                 28
% 8.01/1.49  sim_bw_subset_subsumed:                 3
% 8.01/1.49  sim_fw_subsumed:                        548
% 8.01/1.49  sim_bw_subsumed:                        122
% 8.01/1.49  sim_fw_subsumption_res:                 0
% 8.01/1.49  sim_bw_subsumption_res:                 0
% 8.01/1.49  sim_tautology_del:                      36
% 8.01/1.49  sim_eq_tautology_del:                   498
% 8.01/1.49  sim_eq_res_simp:                        0
% 8.01/1.49  sim_fw_demodulated:                     1219
% 8.01/1.49  sim_bw_demodulated:                     104
% 8.01/1.49  sim_light_normalised:                   1034
% 8.01/1.49  sim_joinable_taut:                      0
% 8.01/1.49  sim_joinable_simp:                      0
% 8.01/1.49  sim_ac_normalised:                      0
% 8.01/1.49  sim_smt_subsumption:                    0
% 8.01/1.49  
%------------------------------------------------------------------------------
