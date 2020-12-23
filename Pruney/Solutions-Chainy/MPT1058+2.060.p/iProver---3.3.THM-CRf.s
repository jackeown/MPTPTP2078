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
% DateTime   : Thu Dec  3 12:09:21 EST 2020

% Result     : Theorem 7.82s
% Output     : CNFRefutation 7.82s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 244 expanded)
%              Number of clauses        :   56 (  97 expanded)
%              Number of leaves         :   21 (  57 expanded)
%              Depth                    :   18
%              Number of atoms          :  245 ( 469 expanded)
%              Number of equality atoms :  136 ( 250 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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

fof(f41,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f40,f39])).

fof(f67,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f69])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f70])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f71])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f72])).

fof(f74,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f63,f74])).

fof(f65,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f61,f74])).

fof(f68,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_526,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_531,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_533,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_921,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_531,c_533])).

cnf(c_8,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_926,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_921,c_8])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_536,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1511,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_531,c_536])).

cnf(c_2633,plain,
    ( k9_relat_1(k6_relat_1(X0),X0) = k2_relat_1(k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_926,c_1511])).

cnf(c_7,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2634,plain,
    ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2633,c_7])).

cnf(c_15,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_527,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2886,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_527])).

cnf(c_2892,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2886,c_8])).

cnf(c_35,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_38,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_56,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2907,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2892,c_35,c_38,c_56])).

cnf(c_5,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_535,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1389,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_535])).

cnf(c_1520,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1389,c_35])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_539,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1644,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = X0
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1520,c_539])).

cnf(c_3521,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2907,c_1644])).

cnf(c_15417,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_526,c_3521])).

cnf(c_532,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_528,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1404,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0))
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_532,c_528])).

cnf(c_1412,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(k6_relat_1(X1),X1))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0))
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1404,c_8])).

cnf(c_1978,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(k6_relat_1(X1),X1))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1412,c_531])).

cnf(c_2883,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_2634,c_1978])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_524,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_530,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1854,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_524,c_530])).

cnf(c_3849,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
    inference(superposition,[status(thm)],[c_2883,c_1854])).

cnf(c_21903,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_15417,c_3849])).

cnf(c_22056,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_21903,c_2634])).

cnf(c_246,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_746,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_247,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_685,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != X0
    | k10_relat_1(sK0,sK2) != X0
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_745,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_16,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22056,c_746,c_745,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.82/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.82/1.49  
% 7.82/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.82/1.49  
% 7.82/1.49  ------  iProver source info
% 7.82/1.49  
% 7.82/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.82/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.82/1.49  git: non_committed_changes: false
% 7.82/1.49  git: last_make_outside_of_git: false
% 7.82/1.49  
% 7.82/1.49  ------ 
% 7.82/1.49  
% 7.82/1.49  ------ Input Options
% 7.82/1.49  
% 7.82/1.49  --out_options                           all
% 7.82/1.49  --tptp_safe_out                         true
% 7.82/1.49  --problem_path                          ""
% 7.82/1.49  --include_path                          ""
% 7.82/1.49  --clausifier                            res/vclausify_rel
% 7.82/1.49  --clausifier_options                    --mode clausify
% 7.82/1.49  --stdin                                 false
% 7.82/1.49  --stats_out                             sel
% 7.82/1.49  
% 7.82/1.49  ------ General Options
% 7.82/1.49  
% 7.82/1.49  --fof                                   false
% 7.82/1.49  --time_out_real                         604.99
% 7.82/1.49  --time_out_virtual                      -1.
% 7.82/1.49  --symbol_type_check                     false
% 7.82/1.49  --clausify_out                          false
% 7.82/1.49  --sig_cnt_out                           false
% 7.82/1.49  --trig_cnt_out                          false
% 7.82/1.49  --trig_cnt_out_tolerance                1.
% 7.82/1.49  --trig_cnt_out_sk_spl                   false
% 7.82/1.49  --abstr_cl_out                          false
% 7.82/1.49  
% 7.82/1.49  ------ Global Options
% 7.82/1.49  
% 7.82/1.49  --schedule                              none
% 7.82/1.49  --add_important_lit                     false
% 7.82/1.49  --prop_solver_per_cl                    1000
% 7.82/1.49  --min_unsat_core                        false
% 7.82/1.49  --soft_assumptions                      false
% 7.82/1.49  --soft_lemma_size                       3
% 7.82/1.49  --prop_impl_unit_size                   0
% 7.82/1.49  --prop_impl_unit                        []
% 7.82/1.49  --share_sel_clauses                     true
% 7.82/1.49  --reset_solvers                         false
% 7.82/1.49  --bc_imp_inh                            [conj_cone]
% 7.82/1.49  --conj_cone_tolerance                   3.
% 7.82/1.49  --extra_neg_conj                        none
% 7.82/1.49  --large_theory_mode                     true
% 7.82/1.49  --prolific_symb_bound                   200
% 7.82/1.49  --lt_threshold                          2000
% 7.82/1.49  --clause_weak_htbl                      true
% 7.82/1.49  --gc_record_bc_elim                     false
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing Options
% 7.82/1.49  
% 7.82/1.49  --preprocessing_flag                    true
% 7.82/1.49  --time_out_prep_mult                    0.1
% 7.82/1.49  --splitting_mode                        input
% 7.82/1.49  --splitting_grd                         true
% 7.82/1.49  --splitting_cvd                         false
% 7.82/1.49  --splitting_cvd_svl                     false
% 7.82/1.49  --splitting_nvd                         32
% 7.82/1.49  --sub_typing                            true
% 7.82/1.49  --prep_gs_sim                           false
% 7.82/1.49  --prep_unflatten                        true
% 7.82/1.49  --prep_res_sim                          true
% 7.82/1.49  --prep_upred                            true
% 7.82/1.49  --prep_sem_filter                       exhaustive
% 7.82/1.49  --prep_sem_filter_out                   false
% 7.82/1.49  --pred_elim                             false
% 7.82/1.49  --res_sim_input                         true
% 7.82/1.49  --eq_ax_congr_red                       true
% 7.82/1.49  --pure_diseq_elim                       true
% 7.82/1.49  --brand_transform                       false
% 7.82/1.49  --non_eq_to_eq                          false
% 7.82/1.49  --prep_def_merge                        true
% 7.82/1.49  --prep_def_merge_prop_impl              false
% 7.82/1.49  --prep_def_merge_mbd                    true
% 7.82/1.49  --prep_def_merge_tr_red                 false
% 7.82/1.49  --prep_def_merge_tr_cl                  false
% 7.82/1.49  --smt_preprocessing                     true
% 7.82/1.49  --smt_ac_axioms                         fast
% 7.82/1.49  --preprocessed_out                      false
% 7.82/1.49  --preprocessed_stats                    false
% 7.82/1.49  
% 7.82/1.49  ------ Abstraction refinement Options
% 7.82/1.49  
% 7.82/1.49  --abstr_ref                             []
% 7.82/1.49  --abstr_ref_prep                        false
% 7.82/1.49  --abstr_ref_until_sat                   false
% 7.82/1.49  --abstr_ref_sig_restrict                funpre
% 7.82/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.82/1.49  --abstr_ref_under                       []
% 7.82/1.49  
% 7.82/1.49  ------ SAT Options
% 7.82/1.49  
% 7.82/1.49  --sat_mode                              false
% 7.82/1.49  --sat_fm_restart_options                ""
% 7.82/1.49  --sat_gr_def                            false
% 7.82/1.49  --sat_epr_types                         true
% 7.82/1.49  --sat_non_cyclic_types                  false
% 7.82/1.49  --sat_finite_models                     false
% 7.82/1.49  --sat_fm_lemmas                         false
% 7.82/1.49  --sat_fm_prep                           false
% 7.82/1.49  --sat_fm_uc_incr                        true
% 7.82/1.49  --sat_out_model                         small
% 7.82/1.49  --sat_out_clauses                       false
% 7.82/1.49  
% 7.82/1.49  ------ QBF Options
% 7.82/1.49  
% 7.82/1.49  --qbf_mode                              false
% 7.82/1.49  --qbf_elim_univ                         false
% 7.82/1.49  --qbf_dom_inst                          none
% 7.82/1.49  --qbf_dom_pre_inst                      false
% 7.82/1.49  --qbf_sk_in                             false
% 7.82/1.49  --qbf_pred_elim                         true
% 7.82/1.49  --qbf_split                             512
% 7.82/1.49  
% 7.82/1.49  ------ BMC1 Options
% 7.82/1.49  
% 7.82/1.49  --bmc1_incremental                      false
% 7.82/1.49  --bmc1_axioms                           reachable_all
% 7.82/1.49  --bmc1_min_bound                        0
% 7.82/1.49  --bmc1_max_bound                        -1
% 7.82/1.49  --bmc1_max_bound_default                -1
% 7.82/1.49  --bmc1_symbol_reachability              true
% 7.82/1.49  --bmc1_property_lemmas                  false
% 7.82/1.49  --bmc1_k_induction                      false
% 7.82/1.49  --bmc1_non_equiv_states                 false
% 7.82/1.49  --bmc1_deadlock                         false
% 7.82/1.49  --bmc1_ucm                              false
% 7.82/1.49  --bmc1_add_unsat_core                   none
% 7.82/1.49  --bmc1_unsat_core_children              false
% 7.82/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.82/1.49  --bmc1_out_stat                         full
% 7.82/1.49  --bmc1_ground_init                      false
% 7.82/1.49  --bmc1_pre_inst_next_state              false
% 7.82/1.49  --bmc1_pre_inst_state                   false
% 7.82/1.49  --bmc1_pre_inst_reach_state             false
% 7.82/1.49  --bmc1_out_unsat_core                   false
% 7.82/1.49  --bmc1_aig_witness_out                  false
% 7.82/1.49  --bmc1_verbose                          false
% 7.82/1.49  --bmc1_dump_clauses_tptp                false
% 7.82/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.82/1.49  --bmc1_dump_file                        -
% 7.82/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.82/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.82/1.49  --bmc1_ucm_extend_mode                  1
% 7.82/1.49  --bmc1_ucm_init_mode                    2
% 7.82/1.49  --bmc1_ucm_cone_mode                    none
% 7.82/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.82/1.49  --bmc1_ucm_relax_model                  4
% 7.82/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.82/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.82/1.49  --bmc1_ucm_layered_model                none
% 7.82/1.49  --bmc1_ucm_max_lemma_size               10
% 7.82/1.49  
% 7.82/1.49  ------ AIG Options
% 7.82/1.49  
% 7.82/1.49  --aig_mode                              false
% 7.82/1.49  
% 7.82/1.49  ------ Instantiation Options
% 7.82/1.49  
% 7.82/1.49  --instantiation_flag                    true
% 7.82/1.49  --inst_sos_flag                         false
% 7.82/1.49  --inst_sos_phase                        true
% 7.82/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.82/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.82/1.49  --inst_lit_sel_side                     num_symb
% 7.82/1.49  --inst_solver_per_active                1400
% 7.82/1.49  --inst_solver_calls_frac                1.
% 7.82/1.49  --inst_passive_queue_type               priority_queues
% 7.82/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.82/1.49  --inst_passive_queues_freq              [25;2]
% 7.82/1.49  --inst_dismatching                      true
% 7.82/1.49  --inst_eager_unprocessed_to_passive     true
% 7.82/1.49  --inst_prop_sim_given                   true
% 7.82/1.49  --inst_prop_sim_new                     false
% 7.82/1.49  --inst_subs_new                         false
% 7.82/1.49  --inst_eq_res_simp                      false
% 7.82/1.49  --inst_subs_given                       false
% 7.82/1.49  --inst_orphan_elimination               true
% 7.82/1.49  --inst_learning_loop_flag               true
% 7.82/1.49  --inst_learning_start                   3000
% 7.82/1.49  --inst_learning_factor                  2
% 7.82/1.49  --inst_start_prop_sim_after_learn       3
% 7.82/1.49  --inst_sel_renew                        solver
% 7.82/1.49  --inst_lit_activity_flag                true
% 7.82/1.49  --inst_restr_to_given                   false
% 7.82/1.49  --inst_activity_threshold               500
% 7.82/1.49  --inst_out_proof                        true
% 7.82/1.49  
% 7.82/1.49  ------ Resolution Options
% 7.82/1.49  
% 7.82/1.49  --resolution_flag                       true
% 7.82/1.49  --res_lit_sel                           adaptive
% 7.82/1.49  --res_lit_sel_side                      none
% 7.82/1.49  --res_ordering                          kbo
% 7.82/1.49  --res_to_prop_solver                    active
% 7.82/1.49  --res_prop_simpl_new                    false
% 7.82/1.49  --res_prop_simpl_given                  true
% 7.82/1.49  --res_passive_queue_type                priority_queues
% 7.82/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.82/1.49  --res_passive_queues_freq               [15;5]
% 7.82/1.49  --res_forward_subs                      full
% 7.82/1.49  --res_backward_subs                     full
% 7.82/1.49  --res_forward_subs_resolution           true
% 7.82/1.49  --res_backward_subs_resolution          true
% 7.82/1.49  --res_orphan_elimination                true
% 7.82/1.49  --res_time_limit                        2.
% 7.82/1.49  --res_out_proof                         true
% 7.82/1.49  
% 7.82/1.49  ------ Superposition Options
% 7.82/1.49  
% 7.82/1.49  --superposition_flag                    true
% 7.82/1.49  --sup_passive_queue_type                priority_queues
% 7.82/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.82/1.49  --sup_passive_queues_freq               [1;4]
% 7.82/1.49  --demod_completeness_check              fast
% 7.82/1.49  --demod_use_ground                      true
% 7.82/1.49  --sup_to_prop_solver                    passive
% 7.82/1.49  --sup_prop_simpl_new                    true
% 7.82/1.49  --sup_prop_simpl_given                  true
% 7.82/1.49  --sup_fun_splitting                     false
% 7.82/1.49  --sup_smt_interval                      50000
% 7.82/1.49  
% 7.82/1.49  ------ Superposition Simplification Setup
% 7.82/1.49  
% 7.82/1.49  --sup_indices_passive                   []
% 7.82/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.82/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.49  --sup_full_bw                           [BwDemod]
% 7.82/1.49  --sup_immed_triv                        [TrivRules]
% 7.82/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.49  --sup_immed_bw_main                     []
% 7.82/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.82/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.82/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.82/1.49  
% 7.82/1.49  ------ Combination Options
% 7.82/1.49  
% 7.82/1.49  --comb_res_mult                         3
% 7.82/1.49  --comb_sup_mult                         2
% 7.82/1.49  --comb_inst_mult                        10
% 7.82/1.49  
% 7.82/1.49  ------ Debug Options
% 7.82/1.49  
% 7.82/1.49  --dbg_backtrace                         false
% 7.82/1.49  --dbg_dump_prop_clauses                 false
% 7.82/1.49  --dbg_dump_prop_clauses_file            -
% 7.82/1.49  --dbg_out_stat                          false
% 7.82/1.49  ------ Parsing...
% 7.82/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.49  ------ Proving...
% 7.82/1.49  ------ Problem Properties 
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  clauses                                 19
% 7.82/1.49  conjectures                             4
% 7.82/1.49  EPR                                     5
% 7.82/1.49  Horn                                    19
% 7.82/1.49  unary                                   9
% 7.82/1.49  binary                                  5
% 7.82/1.49  lits                                    36
% 7.82/1.49  lits eq                                 9
% 7.82/1.49  fd_pure                                 0
% 7.82/1.49  fd_pseudo                               0
% 7.82/1.49  fd_cond                                 0
% 7.82/1.49  fd_pseudo_cond                          1
% 7.82/1.49  AC symbols                              0
% 7.82/1.49  
% 7.82/1.49  ------ Input Options Time Limit: Unbounded
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  ------ 
% 7.82/1.49  Current options:
% 7.82/1.49  ------ 
% 7.82/1.49  
% 7.82/1.49  ------ Input Options
% 7.82/1.49  
% 7.82/1.49  --out_options                           all
% 7.82/1.49  --tptp_safe_out                         true
% 7.82/1.49  --problem_path                          ""
% 7.82/1.49  --include_path                          ""
% 7.82/1.49  --clausifier                            res/vclausify_rel
% 7.82/1.49  --clausifier_options                    --mode clausify
% 7.82/1.49  --stdin                                 false
% 7.82/1.49  --stats_out                             sel
% 7.82/1.49  
% 7.82/1.49  ------ General Options
% 7.82/1.49  
% 7.82/1.49  --fof                                   false
% 7.82/1.49  --time_out_real                         604.99
% 7.82/1.49  --time_out_virtual                      -1.
% 7.82/1.49  --symbol_type_check                     false
% 7.82/1.49  --clausify_out                          false
% 7.82/1.49  --sig_cnt_out                           false
% 7.82/1.49  --trig_cnt_out                          false
% 7.82/1.49  --trig_cnt_out_tolerance                1.
% 7.82/1.49  --trig_cnt_out_sk_spl                   false
% 7.82/1.49  --abstr_cl_out                          false
% 7.82/1.49  
% 7.82/1.49  ------ Global Options
% 7.82/1.49  
% 7.82/1.49  --schedule                              none
% 7.82/1.49  --add_important_lit                     false
% 7.82/1.49  --prop_solver_per_cl                    1000
% 7.82/1.49  --min_unsat_core                        false
% 7.82/1.49  --soft_assumptions                      false
% 7.82/1.49  --soft_lemma_size                       3
% 7.82/1.49  --prop_impl_unit_size                   0
% 7.82/1.49  --prop_impl_unit                        []
% 7.82/1.49  --share_sel_clauses                     true
% 7.82/1.49  --reset_solvers                         false
% 7.82/1.49  --bc_imp_inh                            [conj_cone]
% 7.82/1.49  --conj_cone_tolerance                   3.
% 7.82/1.49  --extra_neg_conj                        none
% 7.82/1.49  --large_theory_mode                     true
% 7.82/1.49  --prolific_symb_bound                   200
% 7.82/1.49  --lt_threshold                          2000
% 7.82/1.49  --clause_weak_htbl                      true
% 7.82/1.49  --gc_record_bc_elim                     false
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing Options
% 7.82/1.49  
% 7.82/1.49  --preprocessing_flag                    true
% 7.82/1.49  --time_out_prep_mult                    0.1
% 7.82/1.49  --splitting_mode                        input
% 7.82/1.49  --splitting_grd                         true
% 7.82/1.49  --splitting_cvd                         false
% 7.82/1.49  --splitting_cvd_svl                     false
% 7.82/1.49  --splitting_nvd                         32
% 7.82/1.49  --sub_typing                            true
% 7.82/1.49  --prep_gs_sim                           false
% 7.82/1.49  --prep_unflatten                        true
% 7.82/1.49  --prep_res_sim                          true
% 7.82/1.49  --prep_upred                            true
% 7.82/1.49  --prep_sem_filter                       exhaustive
% 7.82/1.49  --prep_sem_filter_out                   false
% 7.82/1.49  --pred_elim                             false
% 7.82/1.49  --res_sim_input                         true
% 7.82/1.49  --eq_ax_congr_red                       true
% 7.82/1.49  --pure_diseq_elim                       true
% 7.82/1.49  --brand_transform                       false
% 7.82/1.49  --non_eq_to_eq                          false
% 7.82/1.49  --prep_def_merge                        true
% 7.82/1.49  --prep_def_merge_prop_impl              false
% 7.82/1.49  --prep_def_merge_mbd                    true
% 7.82/1.49  --prep_def_merge_tr_red                 false
% 7.82/1.49  --prep_def_merge_tr_cl                  false
% 7.82/1.49  --smt_preprocessing                     true
% 7.82/1.49  --smt_ac_axioms                         fast
% 7.82/1.49  --preprocessed_out                      false
% 7.82/1.49  --preprocessed_stats                    false
% 7.82/1.49  
% 7.82/1.49  ------ Abstraction refinement Options
% 7.82/1.49  
% 7.82/1.49  --abstr_ref                             []
% 7.82/1.49  --abstr_ref_prep                        false
% 7.82/1.49  --abstr_ref_until_sat                   false
% 7.82/1.49  --abstr_ref_sig_restrict                funpre
% 7.82/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.82/1.49  --abstr_ref_under                       []
% 7.82/1.49  
% 7.82/1.49  ------ SAT Options
% 7.82/1.49  
% 7.82/1.49  --sat_mode                              false
% 7.82/1.49  --sat_fm_restart_options                ""
% 7.82/1.49  --sat_gr_def                            false
% 7.82/1.49  --sat_epr_types                         true
% 7.82/1.49  --sat_non_cyclic_types                  false
% 7.82/1.49  --sat_finite_models                     false
% 7.82/1.49  --sat_fm_lemmas                         false
% 7.82/1.49  --sat_fm_prep                           false
% 7.82/1.49  --sat_fm_uc_incr                        true
% 7.82/1.49  --sat_out_model                         small
% 7.82/1.49  --sat_out_clauses                       false
% 7.82/1.49  
% 7.82/1.49  ------ QBF Options
% 7.82/1.49  
% 7.82/1.49  --qbf_mode                              false
% 7.82/1.49  --qbf_elim_univ                         false
% 7.82/1.49  --qbf_dom_inst                          none
% 7.82/1.49  --qbf_dom_pre_inst                      false
% 7.82/1.49  --qbf_sk_in                             false
% 7.82/1.49  --qbf_pred_elim                         true
% 7.82/1.49  --qbf_split                             512
% 7.82/1.49  
% 7.82/1.49  ------ BMC1 Options
% 7.82/1.49  
% 7.82/1.49  --bmc1_incremental                      false
% 7.82/1.49  --bmc1_axioms                           reachable_all
% 7.82/1.49  --bmc1_min_bound                        0
% 7.82/1.49  --bmc1_max_bound                        -1
% 7.82/1.49  --bmc1_max_bound_default                -1
% 7.82/1.49  --bmc1_symbol_reachability              true
% 7.82/1.49  --bmc1_property_lemmas                  false
% 7.82/1.49  --bmc1_k_induction                      false
% 7.82/1.49  --bmc1_non_equiv_states                 false
% 7.82/1.49  --bmc1_deadlock                         false
% 7.82/1.49  --bmc1_ucm                              false
% 7.82/1.49  --bmc1_add_unsat_core                   none
% 7.82/1.49  --bmc1_unsat_core_children              false
% 7.82/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.82/1.49  --bmc1_out_stat                         full
% 7.82/1.49  --bmc1_ground_init                      false
% 7.82/1.49  --bmc1_pre_inst_next_state              false
% 7.82/1.49  --bmc1_pre_inst_state                   false
% 7.82/1.49  --bmc1_pre_inst_reach_state             false
% 7.82/1.49  --bmc1_out_unsat_core                   false
% 7.82/1.49  --bmc1_aig_witness_out                  false
% 7.82/1.49  --bmc1_verbose                          false
% 7.82/1.49  --bmc1_dump_clauses_tptp                false
% 7.82/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.82/1.49  --bmc1_dump_file                        -
% 7.82/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.82/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.82/1.49  --bmc1_ucm_extend_mode                  1
% 7.82/1.49  --bmc1_ucm_init_mode                    2
% 7.82/1.49  --bmc1_ucm_cone_mode                    none
% 7.82/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.82/1.49  --bmc1_ucm_relax_model                  4
% 7.82/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.82/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.82/1.49  --bmc1_ucm_layered_model                none
% 7.82/1.49  --bmc1_ucm_max_lemma_size               10
% 7.82/1.49  
% 7.82/1.49  ------ AIG Options
% 7.82/1.49  
% 7.82/1.49  --aig_mode                              false
% 7.82/1.49  
% 7.82/1.49  ------ Instantiation Options
% 7.82/1.49  
% 7.82/1.49  --instantiation_flag                    true
% 7.82/1.49  --inst_sos_flag                         false
% 7.82/1.49  --inst_sos_phase                        true
% 7.82/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.82/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.82/1.49  --inst_lit_sel_side                     num_symb
% 7.82/1.49  --inst_solver_per_active                1400
% 7.82/1.49  --inst_solver_calls_frac                1.
% 7.82/1.49  --inst_passive_queue_type               priority_queues
% 7.82/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.82/1.49  --inst_passive_queues_freq              [25;2]
% 7.82/1.49  --inst_dismatching                      true
% 7.82/1.49  --inst_eager_unprocessed_to_passive     true
% 7.82/1.49  --inst_prop_sim_given                   true
% 7.82/1.49  --inst_prop_sim_new                     false
% 7.82/1.49  --inst_subs_new                         false
% 7.82/1.49  --inst_eq_res_simp                      false
% 7.82/1.49  --inst_subs_given                       false
% 7.82/1.49  --inst_orphan_elimination               true
% 7.82/1.49  --inst_learning_loop_flag               true
% 7.82/1.49  --inst_learning_start                   3000
% 7.82/1.49  --inst_learning_factor                  2
% 7.82/1.49  --inst_start_prop_sim_after_learn       3
% 7.82/1.49  --inst_sel_renew                        solver
% 7.82/1.49  --inst_lit_activity_flag                true
% 7.82/1.49  --inst_restr_to_given                   false
% 7.82/1.49  --inst_activity_threshold               500
% 7.82/1.49  --inst_out_proof                        true
% 7.82/1.49  
% 7.82/1.49  ------ Resolution Options
% 7.82/1.49  
% 7.82/1.49  --resolution_flag                       true
% 7.82/1.49  --res_lit_sel                           adaptive
% 7.82/1.49  --res_lit_sel_side                      none
% 7.82/1.49  --res_ordering                          kbo
% 7.82/1.49  --res_to_prop_solver                    active
% 7.82/1.49  --res_prop_simpl_new                    false
% 7.82/1.49  --res_prop_simpl_given                  true
% 7.82/1.49  --res_passive_queue_type                priority_queues
% 7.82/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.82/1.49  --res_passive_queues_freq               [15;5]
% 7.82/1.49  --res_forward_subs                      full
% 7.82/1.49  --res_backward_subs                     full
% 7.82/1.49  --res_forward_subs_resolution           true
% 7.82/1.49  --res_backward_subs_resolution          true
% 7.82/1.49  --res_orphan_elimination                true
% 7.82/1.49  --res_time_limit                        2.
% 7.82/1.49  --res_out_proof                         true
% 7.82/1.49  
% 7.82/1.49  ------ Superposition Options
% 7.82/1.49  
% 7.82/1.49  --superposition_flag                    true
% 7.82/1.49  --sup_passive_queue_type                priority_queues
% 7.82/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.82/1.49  --sup_passive_queues_freq               [1;4]
% 7.82/1.49  --demod_completeness_check              fast
% 7.82/1.49  --demod_use_ground                      true
% 7.82/1.49  --sup_to_prop_solver                    passive
% 7.82/1.49  --sup_prop_simpl_new                    true
% 7.82/1.49  --sup_prop_simpl_given                  true
% 7.82/1.49  --sup_fun_splitting                     false
% 7.82/1.49  --sup_smt_interval                      50000
% 7.82/1.49  
% 7.82/1.49  ------ Superposition Simplification Setup
% 7.82/1.49  
% 7.82/1.49  --sup_indices_passive                   []
% 7.82/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.82/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.49  --sup_full_bw                           [BwDemod]
% 7.82/1.49  --sup_immed_triv                        [TrivRules]
% 7.82/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.49  --sup_immed_bw_main                     []
% 7.82/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.82/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.82/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.82/1.49  
% 7.82/1.49  ------ Combination Options
% 7.82/1.49  
% 7.82/1.49  --comb_res_mult                         3
% 7.82/1.49  --comb_sup_mult                         2
% 7.82/1.49  --comb_inst_mult                        10
% 7.82/1.49  
% 7.82/1.49  ------ Debug Options
% 7.82/1.49  
% 7.82/1.49  --dbg_backtrace                         false
% 7.82/1.49  --dbg_dump_prop_clauses                 false
% 7.82/1.49  --dbg_dump_prop_clauses_file            -
% 7.82/1.49  --dbg_out_stat                          false
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  ------ Proving...
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  % SZS status Theorem for theBenchmark.p
% 7.82/1.49  
% 7.82/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.82/1.49  
% 7.82/1.49  fof(f20,conjecture,(
% 7.82/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f21,negated_conjecture,(
% 7.82/1.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.82/1.49    inference(negated_conjecture,[],[f20])).
% 7.82/1.49  
% 7.82/1.49  fof(f35,plain,(
% 7.82/1.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 7.82/1.49    inference(ennf_transformation,[],[f21])).
% 7.82/1.49  
% 7.82/1.49  fof(f36,plain,(
% 7.82/1.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.82/1.49    inference(flattening,[],[f35])).
% 7.82/1.49  
% 7.82/1.49  fof(f40,plain,(
% 7.82/1.49    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2) & r1_tarski(k10_relat_1(X0,sK2),sK1))) )),
% 7.82/1.49    introduced(choice_axiom,[])).
% 7.82/1.49  
% 7.82/1.49  fof(f39,plain,(
% 7.82/1.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 7.82/1.49    introduced(choice_axiom,[])).
% 7.82/1.49  
% 7.82/1.49  fof(f41,plain,(
% 7.82/1.49    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 7.82/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f40,f39])).
% 7.82/1.49  
% 7.82/1.49  fof(f67,plain,(
% 7.82/1.49    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 7.82/1.49    inference(cnf_transformation,[],[f41])).
% 7.82/1.49  
% 7.82/1.49  fof(f15,axiom,(
% 7.82/1.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f59,plain,(
% 7.82/1.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.82/1.49    inference(cnf_transformation,[],[f15])).
% 7.82/1.49  
% 7.82/1.49  fof(f14,axiom,(
% 7.82/1.49    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f27,plain,(
% 7.82/1.49    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 7.82/1.49    inference(ennf_transformation,[],[f14])).
% 7.82/1.49  
% 7.82/1.49  fof(f58,plain,(
% 7.82/1.49    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f27])).
% 7.82/1.49  
% 7.82/1.49  fof(f13,axiom,(
% 7.82/1.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f56,plain,(
% 7.82/1.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.82/1.49    inference(cnf_transformation,[],[f13])).
% 7.82/1.49  
% 7.82/1.49  fof(f10,axiom,(
% 7.82/1.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f24,plain,(
% 7.82/1.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.82/1.49    inference(ennf_transformation,[],[f10])).
% 7.82/1.49  
% 7.82/1.49  fof(f53,plain,(
% 7.82/1.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f24])).
% 7.82/1.49  
% 7.82/1.49  fof(f57,plain,(
% 7.82/1.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.82/1.49    inference(cnf_transformation,[],[f13])).
% 7.82/1.49  
% 7.82/1.49  fof(f19,axiom,(
% 7.82/1.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f33,plain,(
% 7.82/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.82/1.49    inference(ennf_transformation,[],[f19])).
% 7.82/1.49  
% 7.82/1.49  fof(f34,plain,(
% 7.82/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.82/1.49    inference(flattening,[],[f33])).
% 7.82/1.49  
% 7.82/1.49  fof(f64,plain,(
% 7.82/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f34])).
% 7.82/1.49  
% 7.82/1.49  fof(f60,plain,(
% 7.82/1.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 7.82/1.49    inference(cnf_transformation,[],[f15])).
% 7.82/1.49  
% 7.82/1.49  fof(f1,axiom,(
% 7.82/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f37,plain,(
% 7.82/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.82/1.49    inference(nnf_transformation,[],[f1])).
% 7.82/1.49  
% 7.82/1.49  fof(f38,plain,(
% 7.82/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.82/1.49    inference(flattening,[],[f37])).
% 7.82/1.49  
% 7.82/1.49  fof(f42,plain,(
% 7.82/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.82/1.49    inference(cnf_transformation,[],[f38])).
% 7.82/1.49  
% 7.82/1.49  fof(f78,plain,(
% 7.82/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.82/1.49    inference(equality_resolution,[],[f42])).
% 7.82/1.49  
% 7.82/1.49  fof(f11,axiom,(
% 7.82/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f25,plain,(
% 7.82/1.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.82/1.49    inference(ennf_transformation,[],[f11])).
% 7.82/1.49  
% 7.82/1.49  fof(f54,plain,(
% 7.82/1.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f25])).
% 7.82/1.49  
% 7.82/1.49  fof(f44,plain,(
% 7.82/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f38])).
% 7.82/1.49  
% 7.82/1.49  fof(f18,axiom,(
% 7.82/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f31,plain,(
% 7.82/1.49    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.82/1.49    inference(ennf_transformation,[],[f18])).
% 7.82/1.49  
% 7.82/1.49  fof(f32,plain,(
% 7.82/1.49    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.82/1.49    inference(flattening,[],[f31])).
% 7.82/1.49  
% 7.82/1.49  fof(f63,plain,(
% 7.82/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f32])).
% 7.82/1.49  
% 7.82/1.49  fof(f9,axiom,(
% 7.82/1.49    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f52,plain,(
% 7.82/1.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f9])).
% 7.82/1.49  
% 7.82/1.49  fof(f3,axiom,(
% 7.82/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f46,plain,(
% 7.82/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f3])).
% 7.82/1.49  
% 7.82/1.49  fof(f4,axiom,(
% 7.82/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f47,plain,(
% 7.82/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f4])).
% 7.82/1.49  
% 7.82/1.49  fof(f5,axiom,(
% 7.82/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f48,plain,(
% 7.82/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f5])).
% 7.82/1.49  
% 7.82/1.49  fof(f6,axiom,(
% 7.82/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f49,plain,(
% 7.82/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f6])).
% 7.82/1.49  
% 7.82/1.49  fof(f7,axiom,(
% 7.82/1.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f50,plain,(
% 7.82/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f7])).
% 7.82/1.49  
% 7.82/1.49  fof(f8,axiom,(
% 7.82/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f51,plain,(
% 7.82/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f8])).
% 7.82/1.49  
% 7.82/1.49  fof(f69,plain,(
% 7.82/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.82/1.49    inference(definition_unfolding,[],[f50,f51])).
% 7.82/1.49  
% 7.82/1.49  fof(f70,plain,(
% 7.82/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.82/1.49    inference(definition_unfolding,[],[f49,f69])).
% 7.82/1.49  
% 7.82/1.49  fof(f71,plain,(
% 7.82/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.82/1.49    inference(definition_unfolding,[],[f48,f70])).
% 7.82/1.49  
% 7.82/1.49  fof(f72,plain,(
% 7.82/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.82/1.49    inference(definition_unfolding,[],[f47,f71])).
% 7.82/1.49  
% 7.82/1.49  fof(f73,plain,(
% 7.82/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.82/1.49    inference(definition_unfolding,[],[f46,f72])).
% 7.82/1.49  
% 7.82/1.49  fof(f74,plain,(
% 7.82/1.49    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.82/1.49    inference(definition_unfolding,[],[f52,f73])).
% 7.82/1.49  
% 7.82/1.49  fof(f76,plain,(
% 7.82/1.49    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.82/1.49    inference(definition_unfolding,[],[f63,f74])).
% 7.82/1.49  
% 7.82/1.49  fof(f65,plain,(
% 7.82/1.49    v1_relat_1(sK0)),
% 7.82/1.49    inference(cnf_transformation,[],[f41])).
% 7.82/1.49  
% 7.82/1.49  fof(f16,axiom,(
% 7.82/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f28,plain,(
% 7.82/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.82/1.49    inference(ennf_transformation,[],[f16])).
% 7.82/1.49  
% 7.82/1.49  fof(f61,plain,(
% 7.82/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f28])).
% 7.82/1.49  
% 7.82/1.49  fof(f75,plain,(
% 7.82/1.49    ( ! [X2,X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.82/1.49    inference(definition_unfolding,[],[f61,f74])).
% 7.82/1.49  
% 7.82/1.49  fof(f68,plain,(
% 7.82/1.49    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 7.82/1.49    inference(cnf_transformation,[],[f41])).
% 7.82/1.49  
% 7.82/1.49  cnf(c_17,negated_conjecture,
% 7.82/1.49      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
% 7.82/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_526,plain,
% 7.82/1.49      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_11,plain,
% 7.82/1.49      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.82/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_531,plain,
% 7.82/1.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_9,plain,
% 7.82/1.49      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 7.82/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_533,plain,
% 7.82/1.49      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 7.82/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_921,plain,
% 7.82/1.49      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_531,c_533]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_8,plain,
% 7.82/1.49      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.82/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_926,plain,
% 7.82/1.49      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 7.82/1.49      inference(light_normalisation,[status(thm)],[c_921,c_8]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_4,plain,
% 7.82/1.49      ( ~ v1_relat_1(X0)
% 7.82/1.49      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.82/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_536,plain,
% 7.82/1.49      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.82/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1511,plain,
% 7.82/1.49      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_531,c_536]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_2633,plain,
% 7.82/1.49      ( k9_relat_1(k6_relat_1(X0),X0) = k2_relat_1(k6_relat_1(X0)) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_926,c_1511]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_7,plain,
% 7.82/1.49      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.82/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_2634,plain,
% 7.82/1.49      ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
% 7.82/1.49      inference(light_normalisation,[status(thm)],[c_2633,c_7]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_15,plain,
% 7.82/1.49      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 7.82/1.49      | ~ r1_tarski(X0,k1_relat_1(X1))
% 7.82/1.49      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 7.82/1.49      | ~ v1_funct_1(X1)
% 7.82/1.49      | ~ v1_relat_1(X1) ),
% 7.82/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_527,plain,
% 7.82/1.49      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 7.82/1.49      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 7.82/1.49      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 7.82/1.49      | v1_funct_1(X1) != iProver_top
% 7.82/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_2886,plain,
% 7.82/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.82/1.49      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 7.82/1.49      | r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) != iProver_top
% 7.82/1.49      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 7.82/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_2634,c_527]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_2892,plain,
% 7.82/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.82/1.49      | r1_tarski(X0,X0) != iProver_top
% 7.82/1.49      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 7.82/1.49      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 7.82/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.82/1.49      inference(light_normalisation,[status(thm)],[c_2886,c_8]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_35,plain,
% 7.82/1.49      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_10,plain,
% 7.82/1.49      ( v1_funct_1(k6_relat_1(X0)) ),
% 7.82/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_38,plain,
% 7.82/1.49      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_2,plain,
% 7.82/1.49      ( r1_tarski(X0,X0) ),
% 7.82/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_56,plain,
% 7.82/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_2907,plain,
% 7.82/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.82/1.49      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 7.82/1.49      inference(global_propositional_subsumption,
% 7.82/1.49                [status(thm)],
% 7.82/1.49                [c_2892,c_35,c_38,c_56]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_5,plain,
% 7.82/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.82/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_535,plain,
% 7.82/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.82/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1389,plain,
% 7.82/1.49      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top
% 7.82/1.49      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_8,c_535]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1520,plain,
% 7.82/1.49      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
% 7.82/1.49      inference(global_propositional_subsumption,
% 7.82/1.49                [status(thm)],
% 7.82/1.49                [c_1389,c_35]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_0,plain,
% 7.82/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.82/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_539,plain,
% 7.82/1.49      ( X0 = X1
% 7.82/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.82/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1644,plain,
% 7.82/1.49      ( k10_relat_1(k6_relat_1(X0),X1) = X0
% 7.82/1.49      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_1520,c_539]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_3521,plain,
% 7.82/1.49      ( k10_relat_1(k6_relat_1(X0),X1) = X0
% 7.82/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_2907,c_1644]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_15417,plain,
% 7.82/1.49      ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k10_relat_1(sK0,sK2) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_526,c_3521]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_532,plain,
% 7.82/1.49      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_14,plain,
% 7.82/1.49      ( ~ v1_funct_1(X0)
% 7.82/1.49      | ~ v1_relat_1(X0)
% 7.82/1.49      | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 7.82/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_528,plain,
% 7.82/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
% 7.82/1.49      | v1_funct_1(X1) != iProver_top
% 7.82/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1404,plain,
% 7.82/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0))
% 7.82/1.49      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_532,c_528]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1412,plain,
% 7.82/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(k6_relat_1(X1),X1))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0))
% 7.82/1.49      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_1404,c_8]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1978,plain,
% 7.82/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(k6_relat_1(X1),X1))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
% 7.82/1.49      inference(forward_subsumption_resolution,
% 7.82/1.49                [status(thm)],
% 7.82/1.49                [c_1412,c_531]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_2883,plain,
% 7.82/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_2634,c_1978]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_19,negated_conjecture,
% 7.82/1.49      ( v1_relat_1(sK0) ),
% 7.82/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_524,plain,
% 7.82/1.49      ( v1_relat_1(sK0) = iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_12,plain,
% 7.82/1.49      ( ~ v1_relat_1(X0)
% 7.82/1.49      | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 7.82/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_530,plain,
% 7.82/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 7.82/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1854,plain,
% 7.82/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_524,c_530]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_3849,plain,
% 7.82/1.49      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1)) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_2883,c_1854]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_21903,plain,
% 7.82/1.49      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_15417,c_3849]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_22056,plain,
% 7.82/1.49      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
% 7.82/1.49      inference(demodulation,[status(thm)],[c_21903,c_2634]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_246,plain,( X0 = X0 ),theory(equality) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_746,plain,
% 7.82/1.49      ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_246]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_247,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_685,plain,
% 7.82/1.49      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != X0
% 7.82/1.49      | k10_relat_1(sK0,sK2) != X0
% 7.82/1.49      | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_247]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_745,plain,
% 7.82/1.49      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
% 7.82/1.49      | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
% 7.82/1.49      | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_685]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_16,negated_conjecture,
% 7.82/1.49      ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 7.82/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(contradiction,plain,
% 7.82/1.49      ( $false ),
% 7.82/1.49      inference(minisat,[status(thm)],[c_22056,c_746,c_745,c_16]) ).
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.82/1.49  
% 7.82/1.49  ------                               Statistics
% 7.82/1.49  
% 7.82/1.49  ------ Selected
% 7.82/1.49  
% 7.82/1.49  total_time:                             0.611
% 7.82/1.49  
%------------------------------------------------------------------------------
