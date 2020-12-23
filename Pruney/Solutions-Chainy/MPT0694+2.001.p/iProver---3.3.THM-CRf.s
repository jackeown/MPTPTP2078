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
% DateTime   : Thu Dec  3 11:51:56 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 289 expanded)
%              Number of clauses        :   43 (  55 expanded)
%              Number of leaves         :   16 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  224 ( 534 expanded)
%              Number of equality atoms :   66 ( 191 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32])).

fof(f51,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f54])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f55])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f49,f56])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f37,f56])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f56])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f55,f55])).

fof(f53,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k3_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f53,f56,f56])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_427,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_431,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1027,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(sK2,X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_427,c_431])).

cnf(c_3,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_437,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1611,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK2,X0),X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1027,c_437])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_433,plain,
    ( k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
    | r1_tarski(X2,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1784,plain,
    ( k9_relat_1(k7_relat_1(X0,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,X1),X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1611,c_433])).

cnf(c_2930,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_427,c_1784])).

cnf(c_12,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_430,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3111,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),X1) = iProver_top
    | v1_funct_1(k7_relat_1(sK2,X0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2930,c_430])).

cnf(c_16,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_17,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_541,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_542,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_546,plain,
    ( v1_funct_1(k7_relat_1(sK2,X0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_547,plain,
    ( v1_funct_1(k7_relat_1(sK2,X0)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_9976,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3111,c_16,c_17,c_542,c_547])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_436,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k3_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_429,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k3_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_692,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_429])).

cnf(c_1366,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_436,c_692])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1059,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(resolution,[status(thm)],[c_4,c_13])).

cnf(c_2266,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)
    | ~ r1_tarski(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))),sK0)
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_7,c_1059])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_826,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2364,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)
    | ~ r1_tarski(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2266,c_15,c_826])).

cnf(c_2370,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2364,c_3])).

cnf(c_2371,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2370])).

cnf(c_7707,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1366,c_2371])).

cnf(c_7711,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7707,c_1027])).

cnf(c_9996,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_9976,c_7711])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:10:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.64/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.64/0.99  
% 3.64/0.99  ------  iProver source info
% 3.64/0.99  
% 3.64/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.64/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.64/0.99  git: non_committed_changes: false
% 3.64/0.99  git: last_make_outside_of_git: false
% 3.64/0.99  
% 3.64/0.99  ------ 
% 3.64/0.99  
% 3.64/0.99  ------ Input Options
% 3.64/0.99  
% 3.64/0.99  --out_options                           all
% 3.64/0.99  --tptp_safe_out                         true
% 3.64/0.99  --problem_path                          ""
% 3.64/0.99  --include_path                          ""
% 3.64/0.99  --clausifier                            res/vclausify_rel
% 3.64/0.99  --clausifier_options                    --mode clausify
% 3.64/0.99  --stdin                                 false
% 3.64/0.99  --stats_out                             sel
% 3.64/0.99  
% 3.64/0.99  ------ General Options
% 3.64/0.99  
% 3.64/0.99  --fof                                   false
% 3.64/0.99  --time_out_real                         604.99
% 3.64/0.99  --time_out_virtual                      -1.
% 3.64/0.99  --symbol_type_check                     false
% 3.64/0.99  --clausify_out                          false
% 3.64/0.99  --sig_cnt_out                           false
% 3.64/0.99  --trig_cnt_out                          false
% 3.64/0.99  --trig_cnt_out_tolerance                1.
% 3.64/0.99  --trig_cnt_out_sk_spl                   false
% 3.64/0.99  --abstr_cl_out                          false
% 3.64/0.99  
% 3.64/0.99  ------ Global Options
% 3.64/0.99  
% 3.64/0.99  --schedule                              none
% 3.64/0.99  --add_important_lit                     false
% 3.64/0.99  --prop_solver_per_cl                    1000
% 3.64/0.99  --min_unsat_core                        false
% 3.64/0.99  --soft_assumptions                      false
% 3.64/0.99  --soft_lemma_size                       3
% 3.64/0.99  --prop_impl_unit_size                   0
% 3.64/0.99  --prop_impl_unit                        []
% 3.64/0.99  --share_sel_clauses                     true
% 3.64/0.99  --reset_solvers                         false
% 3.64/0.99  --bc_imp_inh                            [conj_cone]
% 3.64/0.99  --conj_cone_tolerance                   3.
% 3.64/0.99  --extra_neg_conj                        none
% 3.64/0.99  --large_theory_mode                     true
% 3.64/0.99  --prolific_symb_bound                   200
% 3.64/0.99  --lt_threshold                          2000
% 3.64/0.99  --clause_weak_htbl                      true
% 3.64/0.99  --gc_record_bc_elim                     false
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing Options
% 3.64/0.99  
% 3.64/0.99  --preprocessing_flag                    true
% 3.64/0.99  --time_out_prep_mult                    0.1
% 3.64/0.99  --splitting_mode                        input
% 3.64/0.99  --splitting_grd                         true
% 3.64/0.99  --splitting_cvd                         false
% 3.64/0.99  --splitting_cvd_svl                     false
% 3.64/0.99  --splitting_nvd                         32
% 3.64/0.99  --sub_typing                            true
% 3.64/0.99  --prep_gs_sim                           false
% 3.64/0.99  --prep_unflatten                        true
% 3.64/0.99  --prep_res_sim                          true
% 3.64/0.99  --prep_upred                            true
% 3.64/0.99  --prep_sem_filter                       exhaustive
% 3.64/0.99  --prep_sem_filter_out                   false
% 3.64/0.99  --pred_elim                             false
% 3.64/0.99  --res_sim_input                         true
% 3.64/0.99  --eq_ax_congr_red                       true
% 3.64/0.99  --pure_diseq_elim                       true
% 3.64/0.99  --brand_transform                       false
% 3.64/0.99  --non_eq_to_eq                          false
% 3.64/0.99  --prep_def_merge                        true
% 3.64/0.99  --prep_def_merge_prop_impl              false
% 3.64/0.99  --prep_def_merge_mbd                    true
% 3.64/0.99  --prep_def_merge_tr_red                 false
% 3.64/0.99  --prep_def_merge_tr_cl                  false
% 3.64/0.99  --smt_preprocessing                     true
% 3.64/0.99  --smt_ac_axioms                         fast
% 3.64/0.99  --preprocessed_out                      false
% 3.64/0.99  --preprocessed_stats                    false
% 3.64/0.99  
% 3.64/0.99  ------ Abstraction refinement Options
% 3.64/0.99  
% 3.64/0.99  --abstr_ref                             []
% 3.64/0.99  --abstr_ref_prep                        false
% 3.64/0.99  --abstr_ref_until_sat                   false
% 3.64/0.99  --abstr_ref_sig_restrict                funpre
% 3.64/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.64/0.99  --abstr_ref_under                       []
% 3.64/0.99  
% 3.64/0.99  ------ SAT Options
% 3.64/0.99  
% 3.64/0.99  --sat_mode                              false
% 3.64/0.99  --sat_fm_restart_options                ""
% 3.64/0.99  --sat_gr_def                            false
% 3.64/0.99  --sat_epr_types                         true
% 3.64/0.99  --sat_non_cyclic_types                  false
% 3.64/0.99  --sat_finite_models                     false
% 3.64/0.99  --sat_fm_lemmas                         false
% 3.64/0.99  --sat_fm_prep                           false
% 3.64/0.99  --sat_fm_uc_incr                        true
% 3.64/0.99  --sat_out_model                         small
% 3.64/0.99  --sat_out_clauses                       false
% 3.64/0.99  
% 3.64/0.99  ------ QBF Options
% 3.64/0.99  
% 3.64/0.99  --qbf_mode                              false
% 3.64/0.99  --qbf_elim_univ                         false
% 3.64/0.99  --qbf_dom_inst                          none
% 3.64/0.99  --qbf_dom_pre_inst                      false
% 3.64/0.99  --qbf_sk_in                             false
% 3.64/0.99  --qbf_pred_elim                         true
% 3.64/0.99  --qbf_split                             512
% 3.64/0.99  
% 3.64/0.99  ------ BMC1 Options
% 3.64/0.99  
% 3.64/0.99  --bmc1_incremental                      false
% 3.64/0.99  --bmc1_axioms                           reachable_all
% 3.64/0.99  --bmc1_min_bound                        0
% 3.64/0.99  --bmc1_max_bound                        -1
% 3.64/0.99  --bmc1_max_bound_default                -1
% 3.64/0.99  --bmc1_symbol_reachability              true
% 3.64/0.99  --bmc1_property_lemmas                  false
% 3.64/0.99  --bmc1_k_induction                      false
% 3.64/0.99  --bmc1_non_equiv_states                 false
% 3.64/0.99  --bmc1_deadlock                         false
% 3.64/0.99  --bmc1_ucm                              false
% 3.64/0.99  --bmc1_add_unsat_core                   none
% 3.64/0.99  --bmc1_unsat_core_children              false
% 3.64/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.64/0.99  --bmc1_out_stat                         full
% 3.64/0.99  --bmc1_ground_init                      false
% 3.64/0.99  --bmc1_pre_inst_next_state              false
% 3.64/0.99  --bmc1_pre_inst_state                   false
% 3.64/0.99  --bmc1_pre_inst_reach_state             false
% 3.64/0.99  --bmc1_out_unsat_core                   false
% 3.64/0.99  --bmc1_aig_witness_out                  false
% 3.64/0.99  --bmc1_verbose                          false
% 3.64/0.99  --bmc1_dump_clauses_tptp                false
% 3.64/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.64/0.99  --bmc1_dump_file                        -
% 3.64/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.64/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.64/0.99  --bmc1_ucm_extend_mode                  1
% 3.64/0.99  --bmc1_ucm_init_mode                    2
% 3.64/0.99  --bmc1_ucm_cone_mode                    none
% 3.64/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.64/0.99  --bmc1_ucm_relax_model                  4
% 3.64/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.64/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.64/0.99  --bmc1_ucm_layered_model                none
% 3.64/0.99  --bmc1_ucm_max_lemma_size               10
% 3.64/0.99  
% 3.64/0.99  ------ AIG Options
% 3.64/0.99  
% 3.64/0.99  --aig_mode                              false
% 3.64/0.99  
% 3.64/0.99  ------ Instantiation Options
% 3.64/0.99  
% 3.64/0.99  --instantiation_flag                    true
% 3.64/0.99  --inst_sos_flag                         false
% 3.64/0.99  --inst_sos_phase                        true
% 3.64/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.64/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.64/0.99  --inst_lit_sel_side                     num_symb
% 3.64/0.99  --inst_solver_per_active                1400
% 3.64/0.99  --inst_solver_calls_frac                1.
% 3.64/0.99  --inst_passive_queue_type               priority_queues
% 3.64/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.64/0.99  --inst_passive_queues_freq              [25;2]
% 3.64/0.99  --inst_dismatching                      true
% 3.64/0.99  --inst_eager_unprocessed_to_passive     true
% 3.64/0.99  --inst_prop_sim_given                   true
% 3.64/0.99  --inst_prop_sim_new                     false
% 3.64/0.99  --inst_subs_new                         false
% 3.64/0.99  --inst_eq_res_simp                      false
% 3.64/0.99  --inst_subs_given                       false
% 3.64/0.99  --inst_orphan_elimination               true
% 3.64/0.99  --inst_learning_loop_flag               true
% 3.64/0.99  --inst_learning_start                   3000
% 3.64/0.99  --inst_learning_factor                  2
% 3.64/0.99  --inst_start_prop_sim_after_learn       3
% 3.64/0.99  --inst_sel_renew                        solver
% 3.64/0.99  --inst_lit_activity_flag                true
% 3.64/0.99  --inst_restr_to_given                   false
% 3.64/0.99  --inst_activity_threshold               500
% 3.64/0.99  --inst_out_proof                        true
% 3.64/0.99  
% 3.64/0.99  ------ Resolution Options
% 3.64/0.99  
% 3.64/0.99  --resolution_flag                       true
% 3.64/0.99  --res_lit_sel                           adaptive
% 3.64/0.99  --res_lit_sel_side                      none
% 3.64/0.99  --res_ordering                          kbo
% 3.64/0.99  --res_to_prop_solver                    active
% 3.64/0.99  --res_prop_simpl_new                    false
% 3.64/0.99  --res_prop_simpl_given                  true
% 3.64/0.99  --res_passive_queue_type                priority_queues
% 3.64/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.64/0.99  --res_passive_queues_freq               [15;5]
% 3.64/0.99  --res_forward_subs                      full
% 3.64/0.99  --res_backward_subs                     full
% 3.64/0.99  --res_forward_subs_resolution           true
% 3.64/0.99  --res_backward_subs_resolution          true
% 3.64/0.99  --res_orphan_elimination                true
% 3.64/0.99  --res_time_limit                        2.
% 3.64/0.99  --res_out_proof                         true
% 3.64/0.99  
% 3.64/0.99  ------ Superposition Options
% 3.64/0.99  
% 3.64/0.99  --superposition_flag                    true
% 3.64/0.99  --sup_passive_queue_type                priority_queues
% 3.64/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.64/0.99  --sup_passive_queues_freq               [1;4]
% 3.64/0.99  --demod_completeness_check              fast
% 3.64/0.99  --demod_use_ground                      true
% 3.64/0.99  --sup_to_prop_solver                    passive
% 3.64/0.99  --sup_prop_simpl_new                    true
% 3.64/0.99  --sup_prop_simpl_given                  true
% 3.64/0.99  --sup_fun_splitting                     false
% 3.64/0.99  --sup_smt_interval                      50000
% 3.64/0.99  
% 3.64/0.99  ------ Superposition Simplification Setup
% 3.64/0.99  
% 3.64/0.99  --sup_indices_passive                   []
% 3.64/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.64/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_full_bw                           [BwDemod]
% 3.64/0.99  --sup_immed_triv                        [TrivRules]
% 3.64/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_immed_bw_main                     []
% 3.64/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.64/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.99  
% 3.64/0.99  ------ Combination Options
% 3.64/0.99  
% 3.64/0.99  --comb_res_mult                         3
% 3.64/0.99  --comb_sup_mult                         2
% 3.64/0.99  --comb_inst_mult                        10
% 3.64/0.99  
% 3.64/0.99  ------ Debug Options
% 3.64/0.99  
% 3.64/0.99  --dbg_backtrace                         false
% 3.64/0.99  --dbg_dump_prop_clauses                 false
% 3.64/0.99  --dbg_dump_prop_clauses_file            -
% 3.64/0.99  --dbg_out_stat                          false
% 3.64/0.99  ------ Parsing...
% 3.64/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/0.99  ------ Proving...
% 3.64/0.99  ------ Problem Properties 
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  clauses                                 14
% 3.64/0.99  conjectures                             3
% 3.64/0.99  EPR                                     4
% 3.64/0.99  Horn                                    14
% 3.64/0.99  unary                                   6
% 3.64/0.99  binary                                  2
% 3.64/0.99  lits                                    30
% 3.64/0.99  lits eq                                 4
% 3.64/0.99  fd_pure                                 0
% 3.64/0.99  fd_pseudo                               0
% 3.64/0.99  fd_cond                                 0
% 3.64/0.99  fd_pseudo_cond                          1
% 3.64/0.99  AC symbols                              0
% 3.64/0.99  
% 3.64/0.99  ------ Input Options Time Limit: Unbounded
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ 
% 3.64/0.99  Current options:
% 3.64/0.99  ------ 
% 3.64/0.99  
% 3.64/0.99  ------ Input Options
% 3.64/0.99  
% 3.64/0.99  --out_options                           all
% 3.64/0.99  --tptp_safe_out                         true
% 3.64/0.99  --problem_path                          ""
% 3.64/0.99  --include_path                          ""
% 3.64/0.99  --clausifier                            res/vclausify_rel
% 3.64/0.99  --clausifier_options                    --mode clausify
% 3.64/0.99  --stdin                                 false
% 3.64/0.99  --stats_out                             sel
% 3.64/0.99  
% 3.64/0.99  ------ General Options
% 3.64/0.99  
% 3.64/0.99  --fof                                   false
% 3.64/0.99  --time_out_real                         604.99
% 3.64/0.99  --time_out_virtual                      -1.
% 3.64/0.99  --symbol_type_check                     false
% 3.64/0.99  --clausify_out                          false
% 3.64/0.99  --sig_cnt_out                           false
% 3.64/0.99  --trig_cnt_out                          false
% 3.64/0.99  --trig_cnt_out_tolerance                1.
% 3.64/0.99  --trig_cnt_out_sk_spl                   false
% 3.64/0.99  --abstr_cl_out                          false
% 3.64/0.99  
% 3.64/0.99  ------ Global Options
% 3.64/0.99  
% 3.64/0.99  --schedule                              none
% 3.64/0.99  --add_important_lit                     false
% 3.64/0.99  --prop_solver_per_cl                    1000
% 3.64/0.99  --min_unsat_core                        false
% 3.64/0.99  --soft_assumptions                      false
% 3.64/0.99  --soft_lemma_size                       3
% 3.64/0.99  --prop_impl_unit_size                   0
% 3.64/0.99  --prop_impl_unit                        []
% 3.64/0.99  --share_sel_clauses                     true
% 3.64/0.99  --reset_solvers                         false
% 3.64/0.99  --bc_imp_inh                            [conj_cone]
% 3.64/0.99  --conj_cone_tolerance                   3.
% 3.64/0.99  --extra_neg_conj                        none
% 3.64/0.99  --large_theory_mode                     true
% 3.64/0.99  --prolific_symb_bound                   200
% 3.64/0.99  --lt_threshold                          2000
% 3.64/0.99  --clause_weak_htbl                      true
% 3.64/0.99  --gc_record_bc_elim                     false
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing Options
% 3.64/0.99  
% 3.64/0.99  --preprocessing_flag                    true
% 3.64/0.99  --time_out_prep_mult                    0.1
% 3.64/0.99  --splitting_mode                        input
% 3.64/0.99  --splitting_grd                         true
% 3.64/0.99  --splitting_cvd                         false
% 3.64/0.99  --splitting_cvd_svl                     false
% 3.64/0.99  --splitting_nvd                         32
% 3.64/0.99  --sub_typing                            true
% 3.64/0.99  --prep_gs_sim                           false
% 3.64/0.99  --prep_unflatten                        true
% 3.64/0.99  --prep_res_sim                          true
% 3.64/0.99  --prep_upred                            true
% 3.64/0.99  --prep_sem_filter                       exhaustive
% 3.64/0.99  --prep_sem_filter_out                   false
% 3.64/0.99  --pred_elim                             false
% 3.64/0.99  --res_sim_input                         true
% 3.64/0.99  --eq_ax_congr_red                       true
% 3.64/0.99  --pure_diseq_elim                       true
% 3.64/0.99  --brand_transform                       false
% 3.64/0.99  --non_eq_to_eq                          false
% 3.64/0.99  --prep_def_merge                        true
% 3.64/0.99  --prep_def_merge_prop_impl              false
% 3.64/0.99  --prep_def_merge_mbd                    true
% 3.64/0.99  --prep_def_merge_tr_red                 false
% 3.64/0.99  --prep_def_merge_tr_cl                  false
% 3.64/0.99  --smt_preprocessing                     true
% 3.64/0.99  --smt_ac_axioms                         fast
% 3.64/0.99  --preprocessed_out                      false
% 3.64/0.99  --preprocessed_stats                    false
% 3.64/0.99  
% 3.64/0.99  ------ Abstraction refinement Options
% 3.64/0.99  
% 3.64/0.99  --abstr_ref                             []
% 3.64/0.99  --abstr_ref_prep                        false
% 3.64/0.99  --abstr_ref_until_sat                   false
% 3.64/0.99  --abstr_ref_sig_restrict                funpre
% 3.64/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.64/0.99  --abstr_ref_under                       []
% 3.64/0.99  
% 3.64/0.99  ------ SAT Options
% 3.64/0.99  
% 3.64/0.99  --sat_mode                              false
% 3.64/0.99  --sat_fm_restart_options                ""
% 3.64/0.99  --sat_gr_def                            false
% 3.64/0.99  --sat_epr_types                         true
% 3.64/0.99  --sat_non_cyclic_types                  false
% 3.64/0.99  --sat_finite_models                     false
% 3.64/0.99  --sat_fm_lemmas                         false
% 3.64/0.99  --sat_fm_prep                           false
% 3.64/0.99  --sat_fm_uc_incr                        true
% 3.64/0.99  --sat_out_model                         small
% 3.64/0.99  --sat_out_clauses                       false
% 3.64/0.99  
% 3.64/0.99  ------ QBF Options
% 3.64/0.99  
% 3.64/0.99  --qbf_mode                              false
% 3.64/0.99  --qbf_elim_univ                         false
% 3.64/0.99  --qbf_dom_inst                          none
% 3.64/0.99  --qbf_dom_pre_inst                      false
% 3.64/0.99  --qbf_sk_in                             false
% 3.64/0.99  --qbf_pred_elim                         true
% 3.64/0.99  --qbf_split                             512
% 3.64/0.99  
% 3.64/0.99  ------ BMC1 Options
% 3.64/0.99  
% 3.64/0.99  --bmc1_incremental                      false
% 3.64/0.99  --bmc1_axioms                           reachable_all
% 3.64/0.99  --bmc1_min_bound                        0
% 3.64/0.99  --bmc1_max_bound                        -1
% 3.64/0.99  --bmc1_max_bound_default                -1
% 3.64/0.99  --bmc1_symbol_reachability              true
% 3.64/0.99  --bmc1_property_lemmas                  false
% 3.64/0.99  --bmc1_k_induction                      false
% 3.64/0.99  --bmc1_non_equiv_states                 false
% 3.64/0.99  --bmc1_deadlock                         false
% 3.64/0.99  --bmc1_ucm                              false
% 3.64/0.99  --bmc1_add_unsat_core                   none
% 3.64/0.99  --bmc1_unsat_core_children              false
% 3.64/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.64/0.99  --bmc1_out_stat                         full
% 3.64/0.99  --bmc1_ground_init                      false
% 3.64/0.99  --bmc1_pre_inst_next_state              false
% 3.64/0.99  --bmc1_pre_inst_state                   false
% 3.64/0.99  --bmc1_pre_inst_reach_state             false
% 3.64/0.99  --bmc1_out_unsat_core                   false
% 3.64/0.99  --bmc1_aig_witness_out                  false
% 3.64/0.99  --bmc1_verbose                          false
% 3.64/0.99  --bmc1_dump_clauses_tptp                false
% 3.64/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.64/0.99  --bmc1_dump_file                        -
% 3.64/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.64/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.64/0.99  --bmc1_ucm_extend_mode                  1
% 3.64/0.99  --bmc1_ucm_init_mode                    2
% 3.64/0.99  --bmc1_ucm_cone_mode                    none
% 3.64/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.64/0.99  --bmc1_ucm_relax_model                  4
% 3.64/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.64/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.64/0.99  --bmc1_ucm_layered_model                none
% 3.64/0.99  --bmc1_ucm_max_lemma_size               10
% 3.64/0.99  
% 3.64/0.99  ------ AIG Options
% 3.64/0.99  
% 3.64/0.99  --aig_mode                              false
% 3.64/0.99  
% 3.64/0.99  ------ Instantiation Options
% 3.64/0.99  
% 3.64/0.99  --instantiation_flag                    true
% 3.64/0.99  --inst_sos_flag                         false
% 3.64/0.99  --inst_sos_phase                        true
% 3.64/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.64/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.64/0.99  --inst_lit_sel_side                     num_symb
% 3.64/0.99  --inst_solver_per_active                1400
% 3.64/0.99  --inst_solver_calls_frac                1.
% 3.64/0.99  --inst_passive_queue_type               priority_queues
% 3.64/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.64/0.99  --inst_passive_queues_freq              [25;2]
% 3.64/0.99  --inst_dismatching                      true
% 3.64/0.99  --inst_eager_unprocessed_to_passive     true
% 3.64/0.99  --inst_prop_sim_given                   true
% 3.64/0.99  --inst_prop_sim_new                     false
% 3.64/0.99  --inst_subs_new                         false
% 3.64/0.99  --inst_eq_res_simp                      false
% 3.64/0.99  --inst_subs_given                       false
% 3.64/0.99  --inst_orphan_elimination               true
% 3.64/0.99  --inst_learning_loop_flag               true
% 3.64/0.99  --inst_learning_start                   3000
% 3.64/0.99  --inst_learning_factor                  2
% 3.64/0.99  --inst_start_prop_sim_after_learn       3
% 3.64/0.99  --inst_sel_renew                        solver
% 3.64/0.99  --inst_lit_activity_flag                true
% 3.64/0.99  --inst_restr_to_given                   false
% 3.64/0.99  --inst_activity_threshold               500
% 3.64/0.99  --inst_out_proof                        true
% 3.64/0.99  
% 3.64/0.99  ------ Resolution Options
% 3.64/0.99  
% 3.64/0.99  --resolution_flag                       true
% 3.64/0.99  --res_lit_sel                           adaptive
% 3.64/0.99  --res_lit_sel_side                      none
% 3.64/0.99  --res_ordering                          kbo
% 3.64/0.99  --res_to_prop_solver                    active
% 3.64/0.99  --res_prop_simpl_new                    false
% 3.64/0.99  --res_prop_simpl_given                  true
% 3.64/0.99  --res_passive_queue_type                priority_queues
% 3.64/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.64/0.99  --res_passive_queues_freq               [15;5]
% 3.64/0.99  --res_forward_subs                      full
% 3.64/0.99  --res_backward_subs                     full
% 3.64/0.99  --res_forward_subs_resolution           true
% 3.64/0.99  --res_backward_subs_resolution          true
% 3.64/0.99  --res_orphan_elimination                true
% 3.64/0.99  --res_time_limit                        2.
% 3.64/0.99  --res_out_proof                         true
% 3.64/0.99  
% 3.64/0.99  ------ Superposition Options
% 3.64/0.99  
% 3.64/0.99  --superposition_flag                    true
% 3.64/0.99  --sup_passive_queue_type                priority_queues
% 3.64/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.64/0.99  --sup_passive_queues_freq               [1;4]
% 3.64/0.99  --demod_completeness_check              fast
% 3.64/0.99  --demod_use_ground                      true
% 3.64/0.99  --sup_to_prop_solver                    passive
% 3.64/0.99  --sup_prop_simpl_new                    true
% 3.64/0.99  --sup_prop_simpl_given                  true
% 3.64/0.99  --sup_fun_splitting                     false
% 3.64/0.99  --sup_smt_interval                      50000
% 3.64/0.99  
% 3.64/0.99  ------ Superposition Simplification Setup
% 3.64/0.99  
% 3.64/0.99  --sup_indices_passive                   []
% 3.64/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.64/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_full_bw                           [BwDemod]
% 3.64/0.99  --sup_immed_triv                        [TrivRules]
% 3.64/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_immed_bw_main                     []
% 3.64/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.64/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.99  
% 3.64/0.99  ------ Combination Options
% 3.64/0.99  
% 3.64/0.99  --comb_res_mult                         3
% 3.64/0.99  --comb_sup_mult                         2
% 3.64/0.99  --comb_inst_mult                        10
% 3.64/0.99  
% 3.64/0.99  ------ Debug Options
% 3.64/0.99  
% 3.64/0.99  --dbg_backtrace                         false
% 3.64/0.99  --dbg_dump_prop_clauses                 false
% 3.64/0.99  --dbg_dump_prop_clauses_file            -
% 3.64/0.99  --dbg_out_stat                          false
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ Proving...
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  % SZS status Theorem for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99   Resolution empty clause
% 3.64/0.99  
% 3.64/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  fof(f15,conjecture,(
% 3.64/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f16,negated_conjecture,(
% 3.64/0.99    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 3.64/0.99    inference(negated_conjecture,[],[f15])).
% 3.64/0.99  
% 3.64/0.99  fof(f28,plain,(
% 3.64/0.99    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.64/0.99    inference(ennf_transformation,[],[f16])).
% 3.64/0.99  
% 3.64/0.99  fof(f29,plain,(
% 3.64/0.99    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.64/0.99    inference(flattening,[],[f28])).
% 3.64/0.99  
% 3.64/0.99  fof(f32,plain,(
% 3.64/0.99    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f33,plain,(
% 3.64/0.99    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32])).
% 3.64/0.99  
% 3.64/0.99  fof(f51,plain,(
% 3.64/0.99    v1_relat_1(sK2)),
% 3.64/0.99    inference(cnf_transformation,[],[f33])).
% 3.64/0.99  
% 3.64/0.99  fof(f13,axiom,(
% 3.64/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f25,plain,(
% 3.64/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.64/0.99    inference(ennf_transformation,[],[f13])).
% 3.64/0.99  
% 3.64/0.99  fof(f49,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f25])).
% 3.64/0.99  
% 3.64/0.99  fof(f8,axiom,(
% 3.64/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f43,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.64/0.99    inference(cnf_transformation,[],[f8])).
% 3.64/0.99  
% 3.64/0.99  fof(f5,axiom,(
% 3.64/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f40,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f5])).
% 3.64/0.99  
% 3.64/0.99  fof(f6,axiom,(
% 3.64/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f41,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f6])).
% 3.64/0.99  
% 3.64/0.99  fof(f7,axiom,(
% 3.64/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f42,plain,(
% 3.64/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f7])).
% 3.64/0.99  
% 3.64/0.99  fof(f54,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f41,f42])).
% 3.64/0.99  
% 3.64/0.99  fof(f55,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f40,f54])).
% 3.64/0.99  
% 3.64/0.99  fof(f56,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.64/0.99    inference(definition_unfolding,[],[f43,f55])).
% 3.64/0.99  
% 3.64/0.99  fof(f60,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f49,f56])).
% 3.64/0.99  
% 3.64/0.99  fof(f2,axiom,(
% 3.64/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f37,plain,(
% 3.64/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f2])).
% 3.64/0.99  
% 3.64/0.99  fof(f57,plain,(
% 3.64/0.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f37,f56])).
% 3.64/0.99  
% 3.64/0.99  fof(f11,axiom,(
% 3.64/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f22,plain,(
% 3.64/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 3.64/0.99    inference(ennf_transformation,[],[f11])).
% 3.64/0.99  
% 3.64/0.99  fof(f46,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f22])).
% 3.64/0.99  
% 3.64/0.99  fof(f14,axiom,(
% 3.64/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f26,plain,(
% 3.64/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.64/0.99    inference(ennf_transformation,[],[f14])).
% 3.64/0.99  
% 3.64/0.99  fof(f27,plain,(
% 3.64/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.64/0.99    inference(flattening,[],[f26])).
% 3.64/0.99  
% 3.64/0.99  fof(f50,plain,(
% 3.64/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f27])).
% 3.64/0.99  
% 3.64/0.99  fof(f52,plain,(
% 3.64/0.99    v1_funct_1(sK2)),
% 3.64/0.99    inference(cnf_transformation,[],[f33])).
% 3.64/0.99  
% 3.64/0.99  fof(f9,axiom,(
% 3.64/0.99    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f19,plain,(
% 3.64/0.99    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.64/0.99    inference(ennf_transformation,[],[f9])).
% 3.64/0.99  
% 3.64/0.99  fof(f44,plain,(
% 3.64/0.99    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f19])).
% 3.64/0.99  
% 3.64/0.99  fof(f12,axiom,(
% 3.64/0.99    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f23,plain,(
% 3.64/0.99    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.64/0.99    inference(ennf_transformation,[],[f12])).
% 3.64/0.99  
% 3.64/0.99  fof(f24,plain,(
% 3.64/0.99    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.64/0.99    inference(flattening,[],[f23])).
% 3.64/0.99  
% 3.64/0.99  fof(f48,plain,(
% 3.64/0.99    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f24])).
% 3.64/0.99  
% 3.64/0.99  fof(f3,axiom,(
% 3.64/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f17,plain,(
% 3.64/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.64/0.99    inference(ennf_transformation,[],[f3])).
% 3.64/0.99  
% 3.64/0.99  fof(f18,plain,(
% 3.64/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.64/0.99    inference(flattening,[],[f17])).
% 3.64/0.99  
% 3.64/0.99  fof(f38,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f18])).
% 3.64/0.99  
% 3.64/0.99  fof(f58,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f38,f56])).
% 3.64/0.99  
% 3.64/0.99  fof(f4,axiom,(
% 3.64/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f39,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f4])).
% 3.64/0.99  
% 3.64/0.99  fof(f59,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f39,f55,f55])).
% 3.64/0.99  
% 3.64/0.99  fof(f53,plain,(
% 3.64/0.99    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 3.64/0.99    inference(cnf_transformation,[],[f33])).
% 3.64/0.99  
% 3.64/0.99  fof(f61,plain,(
% 3.64/0.99    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k3_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))),
% 3.64/0.99    inference(definition_unfolding,[],[f53,f56,f56])).
% 3.64/0.99  
% 3.64/0.99  fof(f10,axiom,(
% 3.64/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f20,plain,(
% 3.64/0.99    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 3.64/0.99    inference(ennf_transformation,[],[f10])).
% 3.64/0.99  
% 3.64/0.99  fof(f21,plain,(
% 3.64/0.99    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 3.64/0.99    inference(flattening,[],[f20])).
% 3.64/0.99  
% 3.64/0.99  fof(f45,plain,(
% 3.64/0.99    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f21])).
% 3.64/0.99  
% 3.64/0.99  fof(f1,axiom,(
% 3.64/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f30,plain,(
% 3.64/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.64/0.99    inference(nnf_transformation,[],[f1])).
% 3.64/0.99  
% 3.64/0.99  fof(f31,plain,(
% 3.64/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.64/0.99    inference(flattening,[],[f30])).
% 3.64/0.99  
% 3.64/0.99  fof(f34,plain,(
% 3.64/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.64/0.99    inference(cnf_transformation,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f63,plain,(
% 3.64/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.64/0.99    inference(equality_resolution,[],[f34])).
% 3.64/0.99  
% 3.64/0.99  cnf(c_15,negated_conjecture,
% 3.64/0.99      ( v1_relat_1(sK2) ),
% 3.64/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_427,plain,
% 3.64/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_11,plain,
% 3.64/0.99      ( ~ v1_relat_1(X0)
% 3.64/0.99      | k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 3.64/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_431,plain,
% 3.64/0.99      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 3.64/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1027,plain,
% 3.64/0.99      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k10_relat_1(sK2,X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_427,c_431]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3,plain,
% 3.64/0.99      ( r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_437,plain,
% 3.64/0.99      ( r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1611,plain,
% 3.64/0.99      ( r1_tarski(k10_relat_1(k7_relat_1(sK2,X0),X1),X0) = iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1027,c_437]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_8,plain,
% 3.64/0.99      ( ~ r1_tarski(X0,X1)
% 3.64/0.99      | ~ v1_relat_1(X2)
% 3.64/0.99      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_433,plain,
% 3.64/0.99      ( k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
% 3.64/0.99      | r1_tarski(X2,X1) != iProver_top
% 3.64/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1784,plain,
% 3.64/0.99      ( k9_relat_1(k7_relat_1(X0,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k9_relat_1(X0,k10_relat_1(k7_relat_1(sK2,X1),X2))
% 3.64/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_1611,c_433]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2930,plain,
% 3.64/0.99      ( k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)) ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_427,c_1784]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_12,plain,
% 3.64/0.99      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.64/0.99      | ~ v1_funct_1(X0)
% 3.64/0.99      | ~ v1_relat_1(X0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_430,plain,
% 3.64/0.99      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 3.64/0.99      | v1_funct_1(X0) != iProver_top
% 3.64/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3111,plain,
% 3.64/0.99      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),X1) = iProver_top
% 3.64/0.99      | v1_funct_1(k7_relat_1(sK2,X0)) != iProver_top
% 3.64/0.99      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_2930,c_430]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_16,plain,
% 3.64/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_14,negated_conjecture,
% 3.64/0.99      ( v1_funct_1(sK2) ),
% 3.64/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_17,plain,
% 3.64/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_6,plain,
% 3.64/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.64/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_541,plain,
% 3.64/0.99      ( v1_relat_1(k7_relat_1(sK2,X0)) | ~ v1_relat_1(sK2) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_542,plain,
% 3.64/0.99      ( v1_relat_1(k7_relat_1(sK2,X0)) = iProver_top
% 3.64/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_9,plain,
% 3.64/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(k7_relat_1(X0,X1)) | ~ v1_relat_1(X0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_546,plain,
% 3.64/0.99      ( v1_funct_1(k7_relat_1(sK2,X0))
% 3.64/0.99      | ~ v1_funct_1(sK2)
% 3.64/0.99      | ~ v1_relat_1(sK2) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_547,plain,
% 3.64/0.99      ( v1_funct_1(k7_relat_1(sK2,X0)) = iProver_top
% 3.64/0.99      | v1_funct_1(sK2) != iProver_top
% 3.64/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_9976,plain,
% 3.64/0.99      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),X1) = iProver_top ),
% 3.64/0.99      inference(global_propositional_subsumption,
% 3.64/0.99                [status(thm)],
% 3.64/0.99                [c_3111,c_16,c_17,c_542,c_547]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_4,plain,
% 3.64/0.99      ( ~ r1_tarski(X0,X1)
% 3.64/0.99      | ~ r1_tarski(X0,X2)
% 3.64/0.99      | r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) ),
% 3.64/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_436,plain,
% 3.64/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.64/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.64/0.99      | r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5,plain,
% 3.64/0.99      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_13,negated_conjecture,
% 3.64/0.99      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k3_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
% 3.64/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_429,plain,
% 3.64/0.99      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k3_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_692,plain,
% 3.64/0.99      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_5,c_429]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1366,plain,
% 3.64/0.99      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) != iProver_top
% 3.64/0.99      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_436,c_692]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_7,plain,
% 3.64/0.99      ( ~ r1_tarski(X0,X1)
% 3.64/0.99      | ~ r1_tarski(X2,X3)
% 3.64/0.99      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
% 3.64/0.99      | ~ v1_relat_1(X3)
% 3.64/0.99      | ~ v1_relat_1(X2) ),
% 3.64/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1059,plain,
% 3.64/0.99      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
% 3.64/0.99      | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_4,c_13]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2266,plain,
% 3.64/0.99      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)
% 3.64/0.99      | ~ r1_tarski(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))),sK0)
% 3.64/0.99      | ~ r1_tarski(sK2,sK2)
% 3.64/0.99      | ~ v1_relat_1(sK2) ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_7,c_1059]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f63]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_826,plain,
% 3.64/0.99      ( r1_tarski(sK2,sK2) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2364,plain,
% 3.64/0.99      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)
% 3.64/0.99      | ~ r1_tarski(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1))),sK0) ),
% 3.64/0.99      inference(global_propositional_subsumption,
% 3.64/0.99                [status(thm)],
% 3.64/0.99                [c_2266,c_15,c_826]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2370,plain,
% 3.64/0.99      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
% 3.64/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2364,c_3]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2371,plain,
% 3.64/0.99      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_2370]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_7707,plain,
% 3.64/0.99      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
% 3.64/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1366,c_2371]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_7711,plain,
% 3.64/0.99      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top ),
% 3.64/0.99      inference(demodulation,[status(thm)],[c_7707,c_1027]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_9996,plain,
% 3.64/0.99      ( $false ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_9976,c_7711]) ).
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  ------                               Statistics
% 3.64/0.99  
% 3.64/0.99  ------ Selected
% 3.64/0.99  
% 3.64/0.99  total_time:                             0.341
% 3.64/0.99  
%------------------------------------------------------------------------------
