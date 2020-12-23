%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:14 EST 2020

% Result     : Theorem 55.82s
% Output     : CNFRefutation 55.82s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 936 expanded)
%              Number of clauses        :  109 ( 395 expanded)
%              Number of leaves         :   16 ( 179 expanded)
%              Depth                    :   27
%              Number of atoms          :  412 (2928 expanded)
%              Number of equality atoms :  207 ( 683 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f35])).

fof(f57,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_863,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_160201,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_164556,plain,
    ( ~ r1_tarski(k10_relat_1(X0,k9_relat_1(X0,sK1)),sK1)
    | ~ r1_tarski(sK0,k10_relat_1(X0,k9_relat_1(X0,sK1)))
    | r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_160201])).

cnf(c_164559,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),sK1)
    | ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
    | r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_164556])).

cnf(c_13,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_602,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_609,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1671,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_602,c_609])).

cnf(c_8,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_9,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1676,plain,
    ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1671,c_8,c_9])).

cnf(c_14,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_600,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) = iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1850,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X0),X0) = iProver_top
    | v2_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1676,c_600])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_607,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1539,plain,
    ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_602,c_607])).

cnf(c_1544,plain,
    ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1539,c_8,c_9])).

cnf(c_1855,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | v2_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1850,c_1544])).

cnf(c_36,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_39,plain,
    ( v2_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_43,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9540,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1855,c_36,c_39,c_43])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_596,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_611,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2011,plain,
    ( r1_tarski(X0,k1_relat_1(sK2)) = iProver_top
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_596,c_611])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_593,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1540,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_593,c_607])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_606,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2044,plain,
    ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1540,c_606])).

cnf(c_23,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4733,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2044,c_23])).

cnf(c_4734,plain,
    ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4733])).

cnf(c_4744,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k2_relat_1(sK2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4734,c_611])).

cnf(c_14699,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(sK2,X2)) = iProver_top
    | r1_tarski(X1,k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k2_relat_1(sK2),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4744,c_611])).

cnf(c_96413,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(sK2,X2)) = iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k2_relat_1(sK2),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2011,c_14699])).

cnf(c_103037,plain,
    ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top
    | r1_tarski(sK0,k10_relat_1(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_596,c_96413])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_18,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7602,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_7607,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7602])).

cnf(c_7,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_604,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3296,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k6_relat_1(X0))
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_604])).

cnf(c_3310,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = X0
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3296,c_9])).

cnf(c_3582,plain,
    ( v1_relat_1(X1) != iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3310,c_36])).

cnf(c_3583,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = X0
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3582])).

cnf(c_3592,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_596,c_3583])).

cnf(c_4107,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3592,c_23])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_610,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1823,plain,
    ( k9_relat_1(k5_relat_1(X0,X1),k1_relat_1(k5_relat_1(X0,X1))) = k2_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_609])).

cnf(c_4780,plain,
    ( k9_relat_1(k5_relat_1(k6_relat_1(X0),X1),k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_602,c_1823])).

cnf(c_8332,plain,
    ( k9_relat_1(k5_relat_1(k6_relat_1(X0),sK2),k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) ),
    inference(superposition,[status(thm)],[c_593,c_4780])).

cnf(c_8350,plain,
    ( k9_relat_1(k5_relat_1(k6_relat_1(sK0),sK2),sK0) = k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_4107,c_8332])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k5_relat_1(X0,X1),X2) = k9_relat_1(X1,k9_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_608,plain,
    ( k9_relat_1(k5_relat_1(X0,X1),X2) = k9_relat_1(X1,k9_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2365,plain,
    ( k9_relat_1(X0,k9_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_602,c_608])).

cnf(c_5214,plain,
    ( k9_relat_1(sK2,k9_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) ),
    inference(superposition,[status(thm)],[c_593,c_2365])).

cnf(c_8882,plain,
    ( k9_relat_1(sK2,k9_relat_1(k6_relat_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_8350,c_5214])).

cnf(c_8884,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) = k9_relat_1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_8882,c_1676])).

cnf(c_1824,plain,
    ( k10_relat_1(k5_relat_1(X0,X1),k2_relat_1(k5_relat_1(X0,X1))) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_607])).

cnf(c_6405,plain,
    ( k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),k2_relat_1(k5_relat_1(k6_relat_1(X0),X1))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_602,c_1824])).

cnf(c_10111,plain,
    ( k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),k2_relat_1(k5_relat_1(k6_relat_1(X0),sK2))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) ),
    inference(superposition,[status(thm)],[c_593,c_6405])).

cnf(c_10129,plain,
    ( k10_relat_1(k5_relat_1(k6_relat_1(sK0),sK2),k9_relat_1(sK2,sK0)) = k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_8884,c_10111])).

cnf(c_10150,plain,
    ( k10_relat_1(k5_relat_1(k6_relat_1(sK0),sK2),k9_relat_1(sK2,sK0)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_10129,c_4107])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_605,plain,
    ( k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2333,plain,
    ( k10_relat_1(k6_relat_1(X0),k10_relat_1(X1,X2)) = k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_602,c_605])).

cnf(c_601,plain,
    ( v2_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_599,plain,
    ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1159,plain,
    ( k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1) = k10_relat_1(k6_relat_1(X0),X1)
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_601,c_599])).

cnf(c_16,plain,
    ( k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1160,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1)
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1159,c_16])).

cnf(c_3333,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1160,c_36,c_43])).

cnf(c_4985,plain,
    ( k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k9_relat_1(k6_relat_1(X0),k10_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2333,c_3333])).

cnf(c_4993,plain,
    ( k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k9_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) ),
    inference(superposition,[status(thm)],[c_593,c_4985])).

cnf(c_10455,plain,
    ( k9_relat_1(k6_relat_1(sK0),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) = sK0 ),
    inference(superposition,[status(thm)],[c_10150,c_4993])).

cnf(c_3342,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top
    | v2_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3333,c_600])).

cnf(c_39823,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3342,c_36,c_39,c_43])).

cnf(c_39832,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(sK0),sK0),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10455,c_39823])).

cnf(c_39920,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_39832,c_1676])).

cnf(c_103075,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) != iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(sK0,k10_relat_1(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_39920,c_96413])).

cnf(c_104038,plain,
    ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(sK0,k10_relat_1(sK2,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_103037,c_23,c_24,c_27,c_7607,c_103075])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_595,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2048,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,k10_relat_1(X3,X0)) != iProver_top
    | r1_tarski(X2,k10_relat_1(X3,X1)) = iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_606,c_611])).

cnf(c_14041,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(k10_relat_1(X3,X0),k10_relat_1(X3,X2)) = iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_606,c_2048])).

cnf(c_63456,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(sK2,sK0)),k10_relat_1(X0,X1)) = iProver_top
    | r1_tarski(k9_relat_1(sK2,sK1),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_595,c_14041])).

cnf(c_65495,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(sK2,sK0))) != iProver_top
    | r1_tarski(k9_relat_1(sK2,sK1),X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_63456,c_611])).

cnf(c_104068,plain,
    ( r1_tarski(k9_relat_1(sK2,sK1),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK0)) != iProver_top
    | r1_tarski(sK0,k10_relat_1(sK2,X0)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_104038,c_65495])).

cnf(c_90196,plain,
    ( r1_tarski(k9_relat_1(sK2,sK1),X0) != iProver_top
    | r1_tarski(sK0,k10_relat_1(sK2,X0)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_39920,c_65495])).

cnf(c_126376,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,X0)) = iProver_top
    | r1_tarski(k9_relat_1(sK2,sK1),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_104068,c_23,c_90196])).

cnf(c_126377,plain,
    ( r1_tarski(k9_relat_1(sK2,sK1),X0) != iProver_top
    | r1_tarski(sK0,k10_relat_1(sK2,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_126376])).

cnf(c_126384,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9540,c_126377])).

cnf(c_126480,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_126384])).

cnf(c_1233,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),sK1)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_164559,c_126480,c_1233,c_17,c_18,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:25:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 55.82/7.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 55.82/7.50  
% 55.82/7.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.82/7.50  
% 55.82/7.50  ------  iProver source info
% 55.82/7.50  
% 55.82/7.50  git: date: 2020-06-30 10:37:57 +0100
% 55.82/7.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.82/7.50  git: non_committed_changes: false
% 55.82/7.50  git: last_make_outside_of_git: false
% 55.82/7.50  
% 55.82/7.50  ------ 
% 55.82/7.50  ------ Parsing...
% 55.82/7.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.82/7.50  
% 55.82/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 55.82/7.50  
% 55.82/7.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.82/7.50  
% 55.82/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.82/7.50  ------ Proving...
% 55.82/7.50  ------ Problem Properties 
% 55.82/7.50  
% 55.82/7.50  
% 55.82/7.50  clauses                                 22
% 55.82/7.50  conjectures                             6
% 55.82/7.50  EPR                                     5
% 55.82/7.50  Horn                                    22
% 55.82/7.50  unary                                   12
% 55.82/7.50  binary                                  2
% 55.82/7.50  lits                                    43
% 55.82/7.50  lits eq                                 9
% 55.82/7.50  fd_pure                                 0
% 55.82/7.50  fd_pseudo                               0
% 55.82/7.50  fd_cond                                 0
% 55.82/7.50  fd_pseudo_cond                          0
% 55.82/7.50  AC symbols                              0
% 55.82/7.50  
% 55.82/7.50  ------ Input Options Time Limit: Unbounded
% 55.82/7.50  
% 55.82/7.50  
% 55.82/7.50  ------ 
% 55.82/7.50  Current options:
% 55.82/7.50  ------ 
% 55.82/7.50  
% 55.82/7.50  
% 55.82/7.50  
% 55.82/7.50  
% 55.82/7.50  ------ Proving...
% 55.82/7.50  
% 55.82/7.50  
% 55.82/7.50  % SZS status Theorem for theBenchmark.p
% 55.82/7.50  
% 55.82/7.50  % SZS output start CNFRefutation for theBenchmark.p
% 55.82/7.50  
% 55.82/7.50  fof(f1,axiom,(
% 55.82/7.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 55.82/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.82/7.50  
% 55.82/7.50  fof(f17,plain,(
% 55.82/7.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 55.82/7.50    inference(ennf_transformation,[],[f1])).
% 55.82/7.50  
% 55.82/7.50  fof(f18,plain,(
% 55.82/7.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 55.82/7.50    inference(flattening,[],[f17])).
% 55.82/7.50  
% 55.82/7.50  fof(f37,plain,(
% 55.82/7.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 55.82/7.50    inference(cnf_transformation,[],[f18])).
% 55.82/7.50  
% 55.82/7.50  fof(f11,axiom,(
% 55.82/7.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 55.82/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.82/7.50  
% 55.82/7.50  fof(f49,plain,(
% 55.82/7.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 55.82/7.50    inference(cnf_transformation,[],[f11])).
% 55.82/7.50  
% 55.82/7.50  fof(f3,axiom,(
% 55.82/7.50    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 55.82/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.82/7.50  
% 55.82/7.50  fof(f21,plain,(
% 55.82/7.50    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 55.82/7.50    inference(ennf_transformation,[],[f3])).
% 55.82/7.50  
% 55.82/7.50  fof(f39,plain,(
% 55.82/7.50    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 55.82/7.50    inference(cnf_transformation,[],[f21])).
% 55.82/7.50  
% 55.82/7.50  fof(f9,axiom,(
% 55.82/7.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 55.82/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.82/7.50  
% 55.82/7.50  fof(f46,plain,(
% 55.82/7.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 55.82/7.50    inference(cnf_transformation,[],[f9])).
% 55.82/7.50  
% 55.82/7.50  fof(f45,plain,(
% 55.82/7.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 55.82/7.50    inference(cnf_transformation,[],[f9])).
% 55.82/7.50  
% 55.82/7.50  fof(f12,axiom,(
% 55.82/7.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 55.82/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.82/7.50  
% 55.82/7.50  fof(f29,plain,(
% 55.82/7.50    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 55.82/7.50    inference(ennf_transformation,[],[f12])).
% 55.82/7.50  
% 55.82/7.50  fof(f30,plain,(
% 55.82/7.50    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 55.82/7.50    inference(flattening,[],[f29])).
% 55.82/7.50  
% 55.82/7.50  fof(f51,plain,(
% 55.82/7.50    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 55.82/7.50    inference(cnf_transformation,[],[f30])).
% 55.82/7.50  
% 55.82/7.50  fof(f5,axiom,(
% 55.82/7.50    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 55.82/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.82/7.50  
% 55.82/7.50  fof(f23,plain,(
% 55.82/7.50    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 55.82/7.50    inference(ennf_transformation,[],[f5])).
% 55.82/7.50  
% 55.82/7.50  fof(f41,plain,(
% 55.82/7.50    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 55.82/7.50    inference(cnf_transformation,[],[f23])).
% 55.82/7.50  
% 55.82/7.50  fof(f50,plain,(
% 55.82/7.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 55.82/7.50    inference(cnf_transformation,[],[f11])).
% 55.82/7.50  
% 55.82/7.50  fof(f10,axiom,(
% 55.82/7.50    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 55.82/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.82/7.50  
% 55.82/7.50  fof(f48,plain,(
% 55.82/7.50    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 55.82/7.50    inference(cnf_transformation,[],[f10])).
% 55.82/7.50  
% 55.82/7.50  fof(f15,conjecture,(
% 55.82/7.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 55.82/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.82/7.50  
% 55.82/7.50  fof(f16,negated_conjecture,(
% 55.82/7.50    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 55.82/7.50    inference(negated_conjecture,[],[f15])).
% 55.82/7.50  
% 55.82/7.50  fof(f33,plain,(
% 55.82/7.50    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 55.82/7.50    inference(ennf_transformation,[],[f16])).
% 55.82/7.50  
% 55.82/7.50  fof(f34,plain,(
% 55.82/7.50    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 55.82/7.50    inference(flattening,[],[f33])).
% 55.82/7.50  
% 55.82/7.50  fof(f35,plain,(
% 55.82/7.50    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 55.82/7.50    introduced(choice_axiom,[])).
% 55.82/7.50  
% 55.82/7.50  fof(f36,plain,(
% 55.82/7.50    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 55.82/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f35])).
% 55.82/7.50  
% 55.82/7.50  fof(f57,plain,(
% 55.82/7.50    r1_tarski(sK0,k1_relat_1(sK2))),
% 55.82/7.50    inference(cnf_transformation,[],[f36])).
% 55.82/7.50  
% 55.82/7.50  fof(f54,plain,(
% 55.82/7.50    v1_relat_1(sK2)),
% 55.82/7.50    inference(cnf_transformation,[],[f36])).
% 55.82/7.50  
% 55.82/7.50  fof(f6,axiom,(
% 55.82/7.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 55.82/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.82/7.50  
% 55.82/7.50  fof(f24,plain,(
% 55.82/7.50    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 55.82/7.50    inference(ennf_transformation,[],[f6])).
% 55.82/7.50  
% 55.82/7.50  fof(f25,plain,(
% 55.82/7.50    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 55.82/7.50    inference(flattening,[],[f24])).
% 55.82/7.50  
% 55.82/7.50  fof(f42,plain,(
% 55.82/7.50    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 55.82/7.50    inference(cnf_transformation,[],[f25])).
% 55.82/7.50  
% 55.82/7.50  fof(f55,plain,(
% 55.82/7.50    v1_funct_1(sK2)),
% 55.82/7.50    inference(cnf_transformation,[],[f36])).
% 55.82/7.50  
% 55.82/7.50  fof(f58,plain,(
% 55.82/7.50    v2_funct_1(sK2)),
% 55.82/7.50    inference(cnf_transformation,[],[f36])).
% 55.82/7.50  
% 55.82/7.50  fof(f8,axiom,(
% 55.82/7.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 55.82/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.82/7.50  
% 55.82/7.50  fof(f27,plain,(
% 55.82/7.50    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 55.82/7.50    inference(ennf_transformation,[],[f8])).
% 55.82/7.50  
% 55.82/7.50  fof(f28,plain,(
% 55.82/7.50    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 55.82/7.50    inference(flattening,[],[f27])).
% 55.82/7.50  
% 55.82/7.50  fof(f44,plain,(
% 55.82/7.50    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 55.82/7.50    inference(cnf_transformation,[],[f28])).
% 55.82/7.50  
% 55.82/7.50  fof(f2,axiom,(
% 55.82/7.50    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 55.82/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.82/7.50  
% 55.82/7.50  fof(f19,plain,(
% 55.82/7.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 55.82/7.50    inference(ennf_transformation,[],[f2])).
% 55.82/7.50  
% 55.82/7.50  fof(f20,plain,(
% 55.82/7.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 55.82/7.50    inference(flattening,[],[f19])).
% 55.82/7.50  
% 55.82/7.50  fof(f38,plain,(
% 55.82/7.50    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 55.82/7.50    inference(cnf_transformation,[],[f20])).
% 55.82/7.50  
% 55.82/7.50  fof(f4,axiom,(
% 55.82/7.50    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0)))),
% 55.82/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.82/7.50  
% 55.82/7.50  fof(f22,plain,(
% 55.82/7.50    ! [X0,X1] : (! [X2] : (k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 55.82/7.50    inference(ennf_transformation,[],[f4])).
% 55.82/7.50  
% 55.82/7.50  fof(f40,plain,(
% 55.82/7.50    ( ! [X2,X0,X1] : (k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 55.82/7.50    inference(cnf_transformation,[],[f22])).
% 55.82/7.50  
% 55.82/7.50  fof(f7,axiom,(
% 55.82/7.50    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)))),
% 55.82/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.82/7.50  
% 55.82/7.50  fof(f26,plain,(
% 55.82/7.50    ! [X0,X1] : (! [X2] : (k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 55.82/7.50    inference(ennf_transformation,[],[f7])).
% 55.82/7.50  
% 55.82/7.50  fof(f43,plain,(
% 55.82/7.50    ( ! [X2,X0,X1] : (k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 55.82/7.50    inference(cnf_transformation,[],[f26])).
% 55.82/7.50  
% 55.82/7.50  fof(f13,axiom,(
% 55.82/7.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 55.82/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.82/7.50  
% 55.82/7.50  fof(f31,plain,(
% 55.82/7.50    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 55.82/7.50    inference(ennf_transformation,[],[f13])).
% 55.82/7.50  
% 55.82/7.50  fof(f32,plain,(
% 55.82/7.50    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 55.82/7.50    inference(flattening,[],[f31])).
% 55.82/7.50  
% 55.82/7.50  fof(f52,plain,(
% 55.82/7.50    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 55.82/7.50    inference(cnf_transformation,[],[f32])).
% 55.82/7.50  
% 55.82/7.50  fof(f14,axiom,(
% 55.82/7.50    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 55.82/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.82/7.50  
% 55.82/7.50  fof(f53,plain,(
% 55.82/7.50    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 55.82/7.50    inference(cnf_transformation,[],[f14])).
% 55.82/7.50  
% 55.82/7.50  fof(f56,plain,(
% 55.82/7.50    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 55.82/7.50    inference(cnf_transformation,[],[f36])).
% 55.82/7.50  
% 55.82/7.50  fof(f59,plain,(
% 55.82/7.50    ~r1_tarski(sK0,sK1)),
% 55.82/7.50    inference(cnf_transformation,[],[f36])).
% 55.82/7.50  
% 55.82/7.50  cnf(c_0,plain,
% 55.82/7.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 55.82/7.50      inference(cnf_transformation,[],[f37]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_863,plain,
% 55.82/7.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(sK0,X0) | r1_tarski(sK0,X1) ),
% 55.82/7.50      inference(instantiation,[status(thm)],[c_0]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_160201,plain,
% 55.82/7.50      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK0,X0) | r1_tarski(sK0,sK1) ),
% 55.82/7.50      inference(instantiation,[status(thm)],[c_863]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_164556,plain,
% 55.82/7.50      ( ~ r1_tarski(k10_relat_1(X0,k9_relat_1(X0,sK1)),sK1)
% 55.82/7.50      | ~ r1_tarski(sK0,k10_relat_1(X0,k9_relat_1(X0,sK1)))
% 55.82/7.50      | r1_tarski(sK0,sK1) ),
% 55.82/7.50      inference(instantiation,[status(thm)],[c_160201]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_164559,plain,
% 55.82/7.50      ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),sK1)
% 55.82/7.50      | ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
% 55.82/7.50      | r1_tarski(sK0,sK1) ),
% 55.82/7.50      inference(instantiation,[status(thm)],[c_164556]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_13,plain,
% 55.82/7.50      ( v1_relat_1(k6_relat_1(X0)) ),
% 55.82/7.50      inference(cnf_transformation,[],[f49]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_602,plain,
% 55.82/7.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_2,plain,
% 55.82/7.50      ( ~ v1_relat_1(X0)
% 55.82/7.50      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 55.82/7.50      inference(cnf_transformation,[],[f39]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_609,plain,
% 55.82/7.50      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 55.82/7.50      | v1_relat_1(X0) != iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_1671,plain,
% 55.82/7.50      ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(X0)) ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_602,c_609]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_8,plain,
% 55.82/7.50      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 55.82/7.50      inference(cnf_transformation,[],[f46]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_9,plain,
% 55.82/7.50      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 55.82/7.50      inference(cnf_transformation,[],[f45]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_1676,plain,
% 55.82/7.50      ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
% 55.82/7.50      inference(light_normalisation,[status(thm)],[c_1671,c_8,c_9]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_14,plain,
% 55.82/7.50      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 55.82/7.50      | ~ v2_funct_1(X0)
% 55.82/7.50      | ~ v1_funct_1(X0)
% 55.82/7.50      | ~ v1_relat_1(X0) ),
% 55.82/7.50      inference(cnf_transformation,[],[f51]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_600,plain,
% 55.82/7.50      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) = iProver_top
% 55.82/7.50      | v2_funct_1(X0) != iProver_top
% 55.82/7.50      | v1_funct_1(X0) != iProver_top
% 55.82/7.50      | v1_relat_1(X0) != iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_1850,plain,
% 55.82/7.50      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X0),X0) = iProver_top
% 55.82/7.50      | v2_funct_1(k6_relat_1(X0)) != iProver_top
% 55.82/7.50      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 55.82/7.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_1676,c_600]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_4,plain,
% 55.82/7.50      ( ~ v1_relat_1(X0)
% 55.82/7.50      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 55.82/7.50      inference(cnf_transformation,[],[f41]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_607,plain,
% 55.82/7.50      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 55.82/7.50      | v1_relat_1(X0) != iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_1539,plain,
% 55.82/7.50      ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_602,c_607]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_1544,plain,
% 55.82/7.50      ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
% 55.82/7.50      inference(light_normalisation,[status(thm)],[c_1539,c_8,c_9]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_1855,plain,
% 55.82/7.50      ( r1_tarski(X0,X0) = iProver_top
% 55.82/7.50      | v2_funct_1(k6_relat_1(X0)) != iProver_top
% 55.82/7.50      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 55.82/7.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 55.82/7.50      inference(light_normalisation,[status(thm)],[c_1850,c_1544]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_36,plain,
% 55.82/7.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_12,plain,
% 55.82/7.50      ( v2_funct_1(k6_relat_1(X0)) ),
% 55.82/7.50      inference(cnf_transformation,[],[f50]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_39,plain,
% 55.82/7.50      ( v2_funct_1(k6_relat_1(X0)) = iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_10,plain,
% 55.82/7.50      ( v1_funct_1(k6_relat_1(X0)) ),
% 55.82/7.50      inference(cnf_transformation,[],[f48]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_43,plain,
% 55.82/7.50      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_9540,plain,
% 55.82/7.50      ( r1_tarski(X0,X0) = iProver_top ),
% 55.82/7.50      inference(global_propositional_subsumption,
% 55.82/7.50                [status(thm)],
% 55.82/7.50                [c_1855,c_36,c_39,c_43]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_19,negated_conjecture,
% 55.82/7.50      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 55.82/7.50      inference(cnf_transformation,[],[f57]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_596,plain,
% 55.82/7.50      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_611,plain,
% 55.82/7.50      ( r1_tarski(X0,X1) != iProver_top
% 55.82/7.50      | r1_tarski(X2,X0) != iProver_top
% 55.82/7.50      | r1_tarski(X2,X1) = iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_2011,plain,
% 55.82/7.50      ( r1_tarski(X0,k1_relat_1(sK2)) = iProver_top
% 55.82/7.50      | r1_tarski(X0,sK0) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_596,c_611]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_22,negated_conjecture,
% 55.82/7.50      ( v1_relat_1(sK2) ),
% 55.82/7.50      inference(cnf_transformation,[],[f54]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_593,plain,
% 55.82/7.50      ( v1_relat_1(sK2) = iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_1540,plain,
% 55.82/7.50      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_593,c_607]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_5,plain,
% 55.82/7.50      ( ~ r1_tarski(X0,X1)
% 55.82/7.50      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
% 55.82/7.50      | ~ v1_relat_1(X2) ),
% 55.82/7.50      inference(cnf_transformation,[],[f42]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_606,plain,
% 55.82/7.50      ( r1_tarski(X0,X1) != iProver_top
% 55.82/7.50      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = iProver_top
% 55.82/7.50      | v1_relat_1(X2) != iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_2044,plain,
% 55.82/7.50      ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 55.82/7.50      | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top
% 55.82/7.50      | v1_relat_1(sK2) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_1540,c_606]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_23,plain,
% 55.82/7.50      ( v1_relat_1(sK2) = iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_4733,plain,
% 55.82/7.50      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top
% 55.82/7.50      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
% 55.82/7.50      inference(global_propositional_subsumption,
% 55.82/7.50                [status(thm)],
% 55.82/7.50                [c_2044,c_23]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_4734,plain,
% 55.82/7.50      ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 55.82/7.50      | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top ),
% 55.82/7.50      inference(renaming,[status(thm)],[c_4733]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_4744,plain,
% 55.82/7.50      ( r1_tarski(X0,k10_relat_1(sK2,X1)) = iProver_top
% 55.82/7.50      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 55.82/7.50      | r1_tarski(k2_relat_1(sK2),X1) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_4734,c_611]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_14699,plain,
% 55.82/7.50      ( r1_tarski(X0,X1) != iProver_top
% 55.82/7.50      | r1_tarski(X0,k10_relat_1(sK2,X2)) = iProver_top
% 55.82/7.50      | r1_tarski(X1,k1_relat_1(sK2)) != iProver_top
% 55.82/7.50      | r1_tarski(k2_relat_1(sK2),X2) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_4744,c_611]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_96413,plain,
% 55.82/7.50      ( r1_tarski(X0,X1) != iProver_top
% 55.82/7.50      | r1_tarski(X0,k10_relat_1(sK2,X2)) = iProver_top
% 55.82/7.50      | r1_tarski(X1,sK0) != iProver_top
% 55.82/7.50      | r1_tarski(k2_relat_1(sK2),X2) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_2011,c_14699]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_103037,plain,
% 55.82/7.50      ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 55.82/7.50      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top
% 55.82/7.50      | r1_tarski(sK0,k10_relat_1(sK2,X0)) = iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_596,c_96413]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_21,negated_conjecture,
% 55.82/7.50      ( v1_funct_1(sK2) ),
% 55.82/7.50      inference(cnf_transformation,[],[f55]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_24,plain,
% 55.82/7.50      ( v1_funct_1(sK2) = iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_18,negated_conjecture,
% 55.82/7.50      ( v2_funct_1(sK2) ),
% 55.82/7.50      inference(cnf_transformation,[],[f58]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_27,plain,
% 55.82/7.50      ( v2_funct_1(sK2) = iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_7602,plain,
% 55.82/7.50      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)
% 55.82/7.50      | ~ v2_funct_1(sK2)
% 55.82/7.50      | ~ v1_funct_1(sK2)
% 55.82/7.50      | ~ v1_relat_1(sK2) ),
% 55.82/7.50      inference(instantiation,[status(thm)],[c_14]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_7607,plain,
% 55.82/7.50      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) = iProver_top
% 55.82/7.50      | v2_funct_1(sK2) != iProver_top
% 55.82/7.50      | v1_funct_1(sK2) != iProver_top
% 55.82/7.50      | v1_relat_1(sK2) != iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_7602]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_7,plain,
% 55.82/7.50      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 55.82/7.50      | ~ v1_relat_1(X1)
% 55.82/7.50      | ~ v1_relat_1(X0)
% 55.82/7.50      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 55.82/7.50      inference(cnf_transformation,[],[f44]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_604,plain,
% 55.82/7.50      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 55.82/7.50      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 55.82/7.50      | v1_relat_1(X0) != iProver_top
% 55.82/7.50      | v1_relat_1(X1) != iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_3296,plain,
% 55.82/7.50      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k6_relat_1(X0))
% 55.82/7.50      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 55.82/7.50      | v1_relat_1(X1) != iProver_top
% 55.82/7.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_8,c_604]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_3310,plain,
% 55.82/7.50      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = X0
% 55.82/7.50      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 55.82/7.50      | v1_relat_1(X1) != iProver_top
% 55.82/7.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 55.82/7.50      inference(light_normalisation,[status(thm)],[c_3296,c_9]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_3582,plain,
% 55.82/7.50      ( v1_relat_1(X1) != iProver_top
% 55.82/7.50      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 55.82/7.50      | k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = X0 ),
% 55.82/7.50      inference(global_propositional_subsumption,
% 55.82/7.50                [status(thm)],
% 55.82/7.50                [c_3310,c_36]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_3583,plain,
% 55.82/7.50      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = X0
% 55.82/7.50      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 55.82/7.50      | v1_relat_1(X1) != iProver_top ),
% 55.82/7.50      inference(renaming,[status(thm)],[c_3582]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_3592,plain,
% 55.82/7.50      ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) = sK0
% 55.82/7.50      | v1_relat_1(sK2) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_596,c_3583]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_4107,plain,
% 55.82/7.50      ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) = sK0 ),
% 55.82/7.50      inference(global_propositional_subsumption,
% 55.82/7.50                [status(thm)],
% 55.82/7.50                [c_3592,c_23]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_1,plain,
% 55.82/7.50      ( ~ v1_relat_1(X0)
% 55.82/7.50      | ~ v1_relat_1(X1)
% 55.82/7.50      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 55.82/7.50      inference(cnf_transformation,[],[f38]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_610,plain,
% 55.82/7.50      ( v1_relat_1(X0) != iProver_top
% 55.82/7.50      | v1_relat_1(X1) != iProver_top
% 55.82/7.50      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_1823,plain,
% 55.82/7.50      ( k9_relat_1(k5_relat_1(X0,X1),k1_relat_1(k5_relat_1(X0,X1))) = k2_relat_1(k5_relat_1(X0,X1))
% 55.82/7.50      | v1_relat_1(X1) != iProver_top
% 55.82/7.50      | v1_relat_1(X0) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_610,c_609]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_4780,plain,
% 55.82/7.50      ( k9_relat_1(k5_relat_1(k6_relat_1(X0),X1),k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),X1))
% 55.82/7.50      | v1_relat_1(X1) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_602,c_1823]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_8332,plain,
% 55.82/7.50      ( k9_relat_1(k5_relat_1(k6_relat_1(X0),sK2),k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_593,c_4780]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_8350,plain,
% 55.82/7.50      ( k9_relat_1(k5_relat_1(k6_relat_1(sK0),sK2),sK0) = k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_4107,c_8332]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_3,plain,
% 55.82/7.50      ( ~ v1_relat_1(X0)
% 55.82/7.50      | ~ v1_relat_1(X1)
% 55.82/7.50      | k9_relat_1(k5_relat_1(X0,X1),X2) = k9_relat_1(X1,k9_relat_1(X0,X2)) ),
% 55.82/7.50      inference(cnf_transformation,[],[f40]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_608,plain,
% 55.82/7.50      ( k9_relat_1(k5_relat_1(X0,X1),X2) = k9_relat_1(X1,k9_relat_1(X0,X2))
% 55.82/7.50      | v1_relat_1(X0) != iProver_top
% 55.82/7.50      | v1_relat_1(X1) != iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_2365,plain,
% 55.82/7.50      ( k9_relat_1(X0,k9_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2)
% 55.82/7.50      | v1_relat_1(X0) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_602,c_608]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_5214,plain,
% 55.82/7.50      ( k9_relat_1(sK2,k9_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_593,c_2365]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_8882,plain,
% 55.82/7.50      ( k9_relat_1(sK2,k9_relat_1(k6_relat_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_8350,c_5214]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_8884,plain,
% 55.82/7.50      ( k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) = k9_relat_1(sK2,sK0) ),
% 55.82/7.50      inference(demodulation,[status(thm)],[c_8882,c_1676]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_1824,plain,
% 55.82/7.50      ( k10_relat_1(k5_relat_1(X0,X1),k2_relat_1(k5_relat_1(X0,X1))) = k1_relat_1(k5_relat_1(X0,X1))
% 55.82/7.50      | v1_relat_1(X1) != iProver_top
% 55.82/7.50      | v1_relat_1(X0) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_610,c_607]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_6405,plain,
% 55.82/7.50      ( k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),k2_relat_1(k5_relat_1(k6_relat_1(X0),X1))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
% 55.82/7.50      | v1_relat_1(X1) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_602,c_1824]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_10111,plain,
% 55.82/7.50      ( k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),k2_relat_1(k5_relat_1(k6_relat_1(X0),sK2))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_593,c_6405]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_10129,plain,
% 55.82/7.50      ( k10_relat_1(k5_relat_1(k6_relat_1(sK0),sK2),k9_relat_1(sK2,sK0)) = k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK2)) ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_8884,c_10111]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_10150,plain,
% 55.82/7.50      ( k10_relat_1(k5_relat_1(k6_relat_1(sK0),sK2),k9_relat_1(sK2,sK0)) = sK0 ),
% 55.82/7.50      inference(light_normalisation,[status(thm)],[c_10129,c_4107]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_6,plain,
% 55.82/7.50      ( ~ v1_relat_1(X0)
% 55.82/7.50      | ~ v1_relat_1(X1)
% 55.82/7.50      | k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2)) ),
% 55.82/7.50      inference(cnf_transformation,[],[f43]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_605,plain,
% 55.82/7.50      ( k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2))
% 55.82/7.50      | v1_relat_1(X0) != iProver_top
% 55.82/7.50      | v1_relat_1(X1) != iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_2333,plain,
% 55.82/7.50      ( k10_relat_1(k6_relat_1(X0),k10_relat_1(X1,X2)) = k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2)
% 55.82/7.50      | v1_relat_1(X1) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_602,c_605]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_601,plain,
% 55.82/7.50      ( v2_funct_1(k6_relat_1(X0)) = iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_15,plain,
% 55.82/7.50      ( ~ v2_funct_1(X0)
% 55.82/7.50      | ~ v1_funct_1(X0)
% 55.82/7.50      | ~ v1_relat_1(X0)
% 55.82/7.50      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 55.82/7.50      inference(cnf_transformation,[],[f52]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_599,plain,
% 55.82/7.50      ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 55.82/7.50      | v2_funct_1(X0) != iProver_top
% 55.82/7.50      | v1_funct_1(X0) != iProver_top
% 55.82/7.50      | v1_relat_1(X0) != iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_1159,plain,
% 55.82/7.50      ( k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1) = k10_relat_1(k6_relat_1(X0),X1)
% 55.82/7.50      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 55.82/7.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_601,c_599]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_16,plain,
% 55.82/7.50      ( k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
% 55.82/7.50      inference(cnf_transformation,[],[f53]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_1160,plain,
% 55.82/7.50      ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1)
% 55.82/7.50      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 55.82/7.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 55.82/7.50      inference(light_normalisation,[status(thm)],[c_1159,c_16]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_3333,plain,
% 55.82/7.50      ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1) ),
% 55.82/7.50      inference(global_propositional_subsumption,
% 55.82/7.50                [status(thm)],
% 55.82/7.50                [c_1160,c_36,c_43]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_4985,plain,
% 55.82/7.50      ( k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k9_relat_1(k6_relat_1(X0),k10_relat_1(X1,X2))
% 55.82/7.50      | v1_relat_1(X1) != iProver_top ),
% 55.82/7.50      inference(demodulation,[status(thm)],[c_2333,c_3333]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_4993,plain,
% 55.82/7.50      ( k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k9_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_593,c_4985]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_10455,plain,
% 55.82/7.50      ( k9_relat_1(k6_relat_1(sK0),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) = sK0 ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_10150,c_4993]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_3342,plain,
% 55.82/7.50      ( r1_tarski(k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top
% 55.82/7.50      | v2_funct_1(k6_relat_1(X0)) != iProver_top
% 55.82/7.50      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 55.82/7.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_3333,c_600]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_39823,plain,
% 55.82/7.50      ( r1_tarski(k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
% 55.82/7.50      inference(global_propositional_subsumption,
% 55.82/7.50                [status(thm)],
% 55.82/7.50                [c_3342,c_36,c_39,c_43]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_39832,plain,
% 55.82/7.50      ( r1_tarski(k9_relat_1(k6_relat_1(sK0),sK0),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) = iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_10455,c_39823]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_39920,plain,
% 55.82/7.50      ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) = iProver_top ),
% 55.82/7.50      inference(demodulation,[status(thm)],[c_39832,c_1676]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_103075,plain,
% 55.82/7.50      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) != iProver_top
% 55.82/7.50      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 55.82/7.50      | r1_tarski(sK0,k10_relat_1(sK2,X0)) = iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_39920,c_96413]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_104038,plain,
% 55.82/7.50      ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 55.82/7.50      | r1_tarski(sK0,k10_relat_1(sK2,X0)) = iProver_top ),
% 55.82/7.50      inference(global_propositional_subsumption,
% 55.82/7.50                [status(thm)],
% 55.82/7.50                [c_103037,c_23,c_24,c_27,c_7607,c_103075]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_20,negated_conjecture,
% 55.82/7.50      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 55.82/7.50      inference(cnf_transformation,[],[f56]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_595,plain,
% 55.82/7.50      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 55.82/7.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_2048,plain,
% 55.82/7.50      ( r1_tarski(X0,X1) != iProver_top
% 55.82/7.50      | r1_tarski(X2,k10_relat_1(X3,X0)) != iProver_top
% 55.82/7.50      | r1_tarski(X2,k10_relat_1(X3,X1)) = iProver_top
% 55.82/7.50      | v1_relat_1(X3) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_606,c_611]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_14041,plain,
% 55.82/7.50      ( r1_tarski(X0,X1) != iProver_top
% 55.82/7.50      | r1_tarski(X1,X2) != iProver_top
% 55.82/7.50      | r1_tarski(k10_relat_1(X3,X0),k10_relat_1(X3,X2)) = iProver_top
% 55.82/7.50      | v1_relat_1(X3) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_606,c_2048]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_63456,plain,
% 55.82/7.50      ( r1_tarski(k10_relat_1(X0,k9_relat_1(sK2,sK0)),k10_relat_1(X0,X1)) = iProver_top
% 55.82/7.50      | r1_tarski(k9_relat_1(sK2,sK1),X1) != iProver_top
% 55.82/7.50      | v1_relat_1(X0) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_595,c_14041]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_65495,plain,
% 55.82/7.50      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 55.82/7.50      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(sK2,sK0))) != iProver_top
% 55.82/7.50      | r1_tarski(k9_relat_1(sK2,sK1),X2) != iProver_top
% 55.82/7.50      | v1_relat_1(X1) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_63456,c_611]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_104068,plain,
% 55.82/7.50      ( r1_tarski(k9_relat_1(sK2,sK1),X0) != iProver_top
% 55.82/7.50      | r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK0)) != iProver_top
% 55.82/7.50      | r1_tarski(sK0,k10_relat_1(sK2,X0)) = iProver_top
% 55.82/7.50      | v1_relat_1(sK2) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_104038,c_65495]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_90196,plain,
% 55.82/7.50      ( r1_tarski(k9_relat_1(sK2,sK1),X0) != iProver_top
% 55.82/7.50      | r1_tarski(sK0,k10_relat_1(sK2,X0)) = iProver_top
% 55.82/7.50      | v1_relat_1(sK2) != iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_39920,c_65495]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_126376,plain,
% 55.82/7.50      ( r1_tarski(sK0,k10_relat_1(sK2,X0)) = iProver_top
% 55.82/7.50      | r1_tarski(k9_relat_1(sK2,sK1),X0) != iProver_top ),
% 55.82/7.50      inference(global_propositional_subsumption,
% 55.82/7.50                [status(thm)],
% 55.82/7.50                [c_104068,c_23,c_90196]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_126377,plain,
% 55.82/7.50      ( r1_tarski(k9_relat_1(sK2,sK1),X0) != iProver_top
% 55.82/7.50      | r1_tarski(sK0,k10_relat_1(sK2,X0)) = iProver_top ),
% 55.82/7.50      inference(renaming,[status(thm)],[c_126376]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_126384,plain,
% 55.82/7.50      ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) = iProver_top ),
% 55.82/7.50      inference(superposition,[status(thm)],[c_9540,c_126377]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_126480,plain,
% 55.82/7.50      ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) ),
% 55.82/7.50      inference(predicate_to_equality_rev,[status(thm)],[c_126384]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_1233,plain,
% 55.82/7.50      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),sK1)
% 55.82/7.50      | ~ v2_funct_1(sK2)
% 55.82/7.50      | ~ v1_funct_1(sK2)
% 55.82/7.50      | ~ v1_relat_1(sK2) ),
% 55.82/7.50      inference(instantiation,[status(thm)],[c_14]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(c_17,negated_conjecture,
% 55.82/7.50      ( ~ r1_tarski(sK0,sK1) ),
% 55.82/7.50      inference(cnf_transformation,[],[f59]) ).
% 55.82/7.50  
% 55.82/7.50  cnf(contradiction,plain,
% 55.82/7.50      ( $false ),
% 55.82/7.50      inference(minisat,
% 55.82/7.50                [status(thm)],
% 55.82/7.50                [c_164559,c_126480,c_1233,c_17,c_18,c_21,c_22]) ).
% 55.82/7.50  
% 55.82/7.50  
% 55.82/7.50  % SZS output end CNFRefutation for theBenchmark.p
% 55.82/7.50  
% 55.82/7.50  ------                               Statistics
% 55.82/7.50  
% 55.82/7.50  ------ Selected
% 55.82/7.50  
% 55.82/7.50  total_time:                             6.883
% 55.82/7.50  
%------------------------------------------------------------------------------
