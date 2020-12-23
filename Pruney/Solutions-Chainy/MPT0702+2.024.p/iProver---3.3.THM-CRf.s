%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:10 EST 2020

% Result     : Theorem 19.12s
% Output     : CNFRefutation 19.12s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 574 expanded)
%              Number of clauses        :   97 ( 220 expanded)
%              Number of leaves         :   21 ( 118 expanded)
%              Depth                    :   24
%              Number of atoms          :  348 (1639 expanded)
%              Number of equality atoms :  153 ( 397 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f49,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f53,plain,
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

fof(f54,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f53])).

fof(f88,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f22,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f76,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f86,f64])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f101,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f99,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f61,f64])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f74,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f92,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_31,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1028,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_23,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1033,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1037,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5534,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1033,c_1037])).

cnf(c_26111,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) ),
    inference(superposition,[status(thm)],[c_1028,c_5534])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1034,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2074,plain,
    ( k5_relat_1(k6_relat_1(X0),sK2) = k7_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1028,c_1034])).

cnf(c_26113,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(sK2)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_26111,c_2074])).

cnf(c_2073,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_1033,c_1034])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1030,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_17,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_19,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1036,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4183,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_1036])).

cnf(c_44,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7292,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4183,c_44])).

cnf(c_7293,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7292])).

cnf(c_7303,plain,
    ( k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(sK2))) = k6_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_1030,c_7293])).

cnf(c_9358,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(sK2)),sK0) = k6_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_2073,c_7303])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1039,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3370,plain,
    ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_1033,c_1039])).

cnf(c_18,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3375,plain,
    ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3370,c_17,c_18])).

cnf(c_24,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(X1,k4_xboole_0(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1032,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1954,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(k6_relat_1(X1),X2))) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(superposition,[status(thm)],[c_1033,c_1032])).

cnf(c_16645,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3375,c_1954])).

cnf(c_16790,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK2))) = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_9358,c_16645])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1045,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2364,plain,
    ( k4_xboole_0(sK0,k1_relat_1(sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1030,c_1045])).

cnf(c_16914,plain,
    ( k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_16790,c_2364])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1432,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1442,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1432,c_9])).

cnf(c_16915,plain,
    ( k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_16914,c_1442])).

cnf(c_27020,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_26113,c_16915])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1042,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1041,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3596,plain,
    ( k9_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1))) = k2_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_1041])).

cnf(c_18002,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_1028,c_3596])).

cnf(c_38201,plain,
    ( k9_relat_1(k7_relat_1(sK2,sK0),sK0) = k2_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(superposition,[status(thm)],[c_27020,c_18002])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1046,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1040,plain,
    ( k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
    | r1_tarski(X2,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7002,plain,
    ( k9_relat_1(k7_relat_1(X0,X1),X1) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1046,c_1040])).

cnf(c_23645,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0),X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1028,c_7002])).

cnf(c_38237,plain,
    ( k2_relat_1(k7_relat_1(sK2,sK0)) = k9_relat_1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_38201,c_23645])).

cnf(c_3369,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_1039])).

cnf(c_16400,plain,
    ( k10_relat_1(k7_relat_1(sK2,X0),k2_relat_1(k7_relat_1(sK2,X0))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_1028,c_3369])).

cnf(c_38534,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK0)) = k1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(superposition,[status(thm)],[c_38237,c_16400])).

cnf(c_38544,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK0)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_38534,c_27020])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1029,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1038,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5857,plain,
    ( k4_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k1_xboole_0
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1038,c_1045])).

cnf(c_82923,plain,
    ( k4_xboole_0(k10_relat_1(X0,k9_relat_1(sK2,sK0)),k10_relat_1(X0,k9_relat_1(sK2,sK1))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_5857])).

cnf(c_84328,plain,
    ( k4_xboole_0(k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(sK2,sK0)),k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(sK2,sK1))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_82923])).

cnf(c_89779,plain,
    ( k4_xboole_0(k10_relat_1(k7_relat_1(sK2,X0),k9_relat_1(sK2,sK0)),k10_relat_1(k7_relat_1(sK2,X0),k9_relat_1(sK2,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1028,c_84328])).

cnf(c_90702,plain,
    ( k4_xboole_0(sK0,k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_38544,c_89779])).

cnf(c_1332,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK2,X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_1028,c_1032])).

cnf(c_1597,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(k7_relat_1(sK2,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK2,X1))) ),
    inference(superposition,[status(thm)],[c_1332,c_0])).

cnf(c_1604,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(k7_relat_1(sK2,X0),X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1597,c_1332])).

cnf(c_91135,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_90702,c_1604])).

cnf(c_91141,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = sK0 ),
    inference(demodulation,[status(thm)],[c_91135,c_9])).

cnf(c_1598,plain,
    ( k5_xboole_0(X0,k10_relat_1(k7_relat_1(sK2,X0),X1)) = k4_xboole_0(X0,k10_relat_1(sK2,X1)) ),
    inference(superposition,[status(thm)],[c_1332,c_0])).

cnf(c_93103,plain,
    ( k4_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_91141,c_1598])).

cnf(c_2474,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,k1_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2364,c_0])).

cnf(c_2475,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2474,c_2364])).

cnf(c_2477,plain,
    ( k5_xboole_0(sK0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2475,c_1442])).

cnf(c_93164,plain,
    ( k4_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_93103,c_2477])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1348,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
    | k4_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_25,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_339,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_27])).

cnf(c_340,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_344,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_340,c_31,c_30])).

cnf(c_1268,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),sK1) ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1195,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1267,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),sK1)
    | ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
    | r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1195])).

cnf(c_26,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_93164,c_1348,c_1268,c_1267,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:56:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 19.12/2.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.12/2.98  
% 19.12/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.12/2.98  
% 19.12/2.98  ------  iProver source info
% 19.12/2.98  
% 19.12/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.12/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.12/2.98  git: non_committed_changes: false
% 19.12/2.98  git: last_make_outside_of_git: false
% 19.12/2.98  
% 19.12/2.98  ------ 
% 19.12/2.98  
% 19.12/2.98  ------ Input Options
% 19.12/2.98  
% 19.12/2.98  --out_options                           all
% 19.12/2.98  --tptp_safe_out                         true
% 19.12/2.98  --problem_path                          ""
% 19.12/2.98  --include_path                          ""
% 19.12/2.98  --clausifier                            res/vclausify_rel
% 19.12/2.98  --clausifier_options                    --mode clausify
% 19.12/2.98  --stdin                                 false
% 19.12/2.98  --stats_out                             all
% 19.12/2.98  
% 19.12/2.98  ------ General Options
% 19.12/2.98  
% 19.12/2.98  --fof                                   false
% 19.12/2.98  --time_out_real                         305.
% 19.12/2.98  --time_out_virtual                      -1.
% 19.12/2.98  --symbol_type_check                     false
% 19.12/2.98  --clausify_out                          false
% 19.12/2.98  --sig_cnt_out                           false
% 19.12/2.98  --trig_cnt_out                          false
% 19.12/2.98  --trig_cnt_out_tolerance                1.
% 19.12/2.98  --trig_cnt_out_sk_spl                   false
% 19.12/2.98  --abstr_cl_out                          false
% 19.12/2.98  
% 19.12/2.98  ------ Global Options
% 19.12/2.98  
% 19.12/2.98  --schedule                              default
% 19.12/2.98  --add_important_lit                     false
% 19.12/2.98  --prop_solver_per_cl                    1000
% 19.12/2.98  --min_unsat_core                        false
% 19.12/2.98  --soft_assumptions                      false
% 19.12/2.98  --soft_lemma_size                       3
% 19.12/2.98  --prop_impl_unit_size                   0
% 19.12/2.98  --prop_impl_unit                        []
% 19.12/2.98  --share_sel_clauses                     true
% 19.12/2.98  --reset_solvers                         false
% 19.12/2.98  --bc_imp_inh                            [conj_cone]
% 19.12/2.98  --conj_cone_tolerance                   3.
% 19.12/2.98  --extra_neg_conj                        none
% 19.12/2.98  --large_theory_mode                     true
% 19.12/2.98  --prolific_symb_bound                   200
% 19.12/2.98  --lt_threshold                          2000
% 19.12/2.98  --clause_weak_htbl                      true
% 19.12/2.98  --gc_record_bc_elim                     false
% 19.12/2.98  
% 19.12/2.98  ------ Preprocessing Options
% 19.12/2.98  
% 19.12/2.98  --preprocessing_flag                    true
% 19.12/2.98  --time_out_prep_mult                    0.1
% 19.12/2.98  --splitting_mode                        input
% 19.12/2.98  --splitting_grd                         true
% 19.12/2.98  --splitting_cvd                         false
% 19.12/2.98  --splitting_cvd_svl                     false
% 19.12/2.98  --splitting_nvd                         32
% 19.12/2.98  --sub_typing                            true
% 19.12/2.98  --prep_gs_sim                           true
% 19.12/2.98  --prep_unflatten                        true
% 19.12/2.98  --prep_res_sim                          true
% 19.12/2.98  --prep_upred                            true
% 19.12/2.98  --prep_sem_filter                       exhaustive
% 19.12/2.98  --prep_sem_filter_out                   false
% 19.12/2.98  --pred_elim                             true
% 19.12/2.98  --res_sim_input                         true
% 19.12/2.98  --eq_ax_congr_red                       true
% 19.12/2.98  --pure_diseq_elim                       true
% 19.12/2.98  --brand_transform                       false
% 19.12/2.98  --non_eq_to_eq                          false
% 19.12/2.98  --prep_def_merge                        true
% 19.12/2.98  --prep_def_merge_prop_impl              false
% 19.12/2.98  --prep_def_merge_mbd                    true
% 19.12/2.98  --prep_def_merge_tr_red                 false
% 19.12/2.98  --prep_def_merge_tr_cl                  false
% 19.12/2.98  --smt_preprocessing                     true
% 19.12/2.98  --smt_ac_axioms                         fast
% 19.12/2.98  --preprocessed_out                      false
% 19.12/2.98  --preprocessed_stats                    false
% 19.12/2.98  
% 19.12/2.98  ------ Abstraction refinement Options
% 19.12/2.98  
% 19.12/2.98  --abstr_ref                             []
% 19.12/2.98  --abstr_ref_prep                        false
% 19.12/2.98  --abstr_ref_until_sat                   false
% 19.12/2.98  --abstr_ref_sig_restrict                funpre
% 19.12/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.12/2.98  --abstr_ref_under                       []
% 19.12/2.98  
% 19.12/2.98  ------ SAT Options
% 19.12/2.98  
% 19.12/2.98  --sat_mode                              false
% 19.12/2.98  --sat_fm_restart_options                ""
% 19.12/2.98  --sat_gr_def                            false
% 19.12/2.98  --sat_epr_types                         true
% 19.12/2.98  --sat_non_cyclic_types                  false
% 19.12/2.98  --sat_finite_models                     false
% 19.12/2.98  --sat_fm_lemmas                         false
% 19.12/2.98  --sat_fm_prep                           false
% 19.12/2.98  --sat_fm_uc_incr                        true
% 19.12/2.98  --sat_out_model                         small
% 19.12/2.98  --sat_out_clauses                       false
% 19.12/2.98  
% 19.12/2.98  ------ QBF Options
% 19.12/2.98  
% 19.12/2.98  --qbf_mode                              false
% 19.12/2.98  --qbf_elim_univ                         false
% 19.12/2.98  --qbf_dom_inst                          none
% 19.12/2.98  --qbf_dom_pre_inst                      false
% 19.12/2.98  --qbf_sk_in                             false
% 19.12/2.98  --qbf_pred_elim                         true
% 19.12/2.98  --qbf_split                             512
% 19.12/2.98  
% 19.12/2.98  ------ BMC1 Options
% 19.12/2.98  
% 19.12/2.98  --bmc1_incremental                      false
% 19.12/2.98  --bmc1_axioms                           reachable_all
% 19.12/2.98  --bmc1_min_bound                        0
% 19.12/2.98  --bmc1_max_bound                        -1
% 19.12/2.98  --bmc1_max_bound_default                -1
% 19.12/2.98  --bmc1_symbol_reachability              true
% 19.12/2.98  --bmc1_property_lemmas                  false
% 19.12/2.98  --bmc1_k_induction                      false
% 19.12/2.98  --bmc1_non_equiv_states                 false
% 19.12/2.98  --bmc1_deadlock                         false
% 19.12/2.98  --bmc1_ucm                              false
% 19.12/2.98  --bmc1_add_unsat_core                   none
% 19.12/2.98  --bmc1_unsat_core_children              false
% 19.12/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.12/2.98  --bmc1_out_stat                         full
% 19.12/2.98  --bmc1_ground_init                      false
% 19.12/2.98  --bmc1_pre_inst_next_state              false
% 19.12/2.98  --bmc1_pre_inst_state                   false
% 19.12/2.98  --bmc1_pre_inst_reach_state             false
% 19.12/2.98  --bmc1_out_unsat_core                   false
% 19.12/2.98  --bmc1_aig_witness_out                  false
% 19.12/2.98  --bmc1_verbose                          false
% 19.12/2.98  --bmc1_dump_clauses_tptp                false
% 19.12/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.12/2.98  --bmc1_dump_file                        -
% 19.12/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.12/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.12/2.98  --bmc1_ucm_extend_mode                  1
% 19.12/2.98  --bmc1_ucm_init_mode                    2
% 19.12/2.98  --bmc1_ucm_cone_mode                    none
% 19.12/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.12/2.98  --bmc1_ucm_relax_model                  4
% 19.12/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.12/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.12/2.98  --bmc1_ucm_layered_model                none
% 19.12/2.98  --bmc1_ucm_max_lemma_size               10
% 19.12/2.98  
% 19.12/2.98  ------ AIG Options
% 19.12/2.98  
% 19.12/2.98  --aig_mode                              false
% 19.12/2.98  
% 19.12/2.98  ------ Instantiation Options
% 19.12/2.98  
% 19.12/2.98  --instantiation_flag                    true
% 19.12/2.98  --inst_sos_flag                         false
% 19.12/2.98  --inst_sos_phase                        true
% 19.12/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.12/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.12/2.98  --inst_lit_sel_side                     num_symb
% 19.12/2.98  --inst_solver_per_active                1400
% 19.12/2.98  --inst_solver_calls_frac                1.
% 19.12/2.98  --inst_passive_queue_type               priority_queues
% 19.12/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.12/2.98  --inst_passive_queues_freq              [25;2]
% 19.12/2.98  --inst_dismatching                      true
% 19.12/2.98  --inst_eager_unprocessed_to_passive     true
% 19.12/2.98  --inst_prop_sim_given                   true
% 19.12/2.98  --inst_prop_sim_new                     false
% 19.12/2.98  --inst_subs_new                         false
% 19.12/2.98  --inst_eq_res_simp                      false
% 19.12/2.98  --inst_subs_given                       false
% 19.12/2.98  --inst_orphan_elimination               true
% 19.12/2.98  --inst_learning_loop_flag               true
% 19.12/2.98  --inst_learning_start                   3000
% 19.12/2.98  --inst_learning_factor                  2
% 19.12/2.98  --inst_start_prop_sim_after_learn       3
% 19.12/2.98  --inst_sel_renew                        solver
% 19.12/2.98  --inst_lit_activity_flag                true
% 19.12/2.98  --inst_restr_to_given                   false
% 19.12/2.98  --inst_activity_threshold               500
% 19.12/2.98  --inst_out_proof                        true
% 19.12/2.98  
% 19.12/2.98  ------ Resolution Options
% 19.12/2.98  
% 19.12/2.98  --resolution_flag                       true
% 19.12/2.98  --res_lit_sel                           adaptive
% 19.12/2.98  --res_lit_sel_side                      none
% 19.12/2.98  --res_ordering                          kbo
% 19.12/2.98  --res_to_prop_solver                    active
% 19.12/2.98  --res_prop_simpl_new                    false
% 19.12/2.98  --res_prop_simpl_given                  true
% 19.12/2.98  --res_passive_queue_type                priority_queues
% 19.12/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.12/2.98  --res_passive_queues_freq               [15;5]
% 19.12/2.98  --res_forward_subs                      full
% 19.12/2.98  --res_backward_subs                     full
% 19.12/2.98  --res_forward_subs_resolution           true
% 19.12/2.98  --res_backward_subs_resolution          true
% 19.12/2.98  --res_orphan_elimination                true
% 19.12/2.98  --res_time_limit                        2.
% 19.12/2.98  --res_out_proof                         true
% 19.12/2.98  
% 19.12/2.98  ------ Superposition Options
% 19.12/2.98  
% 19.12/2.98  --superposition_flag                    true
% 19.12/2.98  --sup_passive_queue_type                priority_queues
% 19.12/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.12/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.12/2.98  --demod_completeness_check              fast
% 19.12/2.98  --demod_use_ground                      true
% 19.12/2.98  --sup_to_prop_solver                    passive
% 19.12/2.98  --sup_prop_simpl_new                    true
% 19.12/2.98  --sup_prop_simpl_given                  true
% 19.12/2.98  --sup_fun_splitting                     false
% 19.12/2.98  --sup_smt_interval                      50000
% 19.12/2.98  
% 19.12/2.98  ------ Superposition Simplification Setup
% 19.12/2.98  
% 19.12/2.98  --sup_indices_passive                   []
% 19.12/2.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.12/2.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.12/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.12/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.12/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.12/2.98  --sup_full_bw                           [BwDemod]
% 19.12/2.98  --sup_immed_triv                        [TrivRules]
% 19.12/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.12/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.12/2.98  --sup_immed_bw_main                     []
% 19.12/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.12/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.12/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.12/2.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.12/2.98  
% 19.12/2.98  ------ Combination Options
% 19.12/2.98  
% 19.12/2.98  --comb_res_mult                         3
% 19.12/2.98  --comb_sup_mult                         2
% 19.12/2.98  --comb_inst_mult                        10
% 19.12/2.98  
% 19.12/2.98  ------ Debug Options
% 19.12/2.98  
% 19.12/2.98  --dbg_backtrace                         false
% 19.12/2.98  --dbg_dump_prop_clauses                 false
% 19.12/2.98  --dbg_dump_prop_clauses_file            -
% 19.12/2.98  --dbg_out_stat                          false
% 19.12/2.98  ------ Parsing...
% 19.12/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.12/2.98  
% 19.12/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 19.12/2.98  
% 19.12/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.12/2.98  
% 19.12/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.12/2.98  ------ Proving...
% 19.12/2.98  ------ Problem Properties 
% 19.12/2.98  
% 19.12/2.98  
% 19.12/2.98  clauses                                 28
% 19.12/2.98  conjectures                             4
% 19.12/2.98  EPR                                     5
% 19.12/2.98  Horn                                    28
% 19.12/2.98  unary                                   14
% 19.12/2.98  binary                                  8
% 19.12/2.98  lits                                    48
% 19.12/2.98  lits eq                                 17
% 19.12/2.98  fd_pure                                 0
% 19.12/2.98  fd_pseudo                               0
% 19.12/2.98  fd_cond                                 0
% 19.12/2.98  fd_pseudo_cond                          1
% 19.12/2.98  AC symbols                              0
% 19.12/2.98  
% 19.12/2.98  ------ Schedule dynamic 5 is on 
% 19.12/2.98  
% 19.12/2.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.12/2.98  
% 19.12/2.98  
% 19.12/2.98  ------ 
% 19.12/2.98  Current options:
% 19.12/2.98  ------ 
% 19.12/2.98  
% 19.12/2.98  ------ Input Options
% 19.12/2.98  
% 19.12/2.98  --out_options                           all
% 19.12/2.98  --tptp_safe_out                         true
% 19.12/2.98  --problem_path                          ""
% 19.12/2.98  --include_path                          ""
% 19.12/2.98  --clausifier                            res/vclausify_rel
% 19.12/2.98  --clausifier_options                    --mode clausify
% 19.12/2.98  --stdin                                 false
% 19.12/2.98  --stats_out                             all
% 19.12/2.98  
% 19.12/2.98  ------ General Options
% 19.12/2.98  
% 19.12/2.98  --fof                                   false
% 19.12/2.98  --time_out_real                         305.
% 19.12/2.98  --time_out_virtual                      -1.
% 19.12/2.98  --symbol_type_check                     false
% 19.12/2.98  --clausify_out                          false
% 19.12/2.98  --sig_cnt_out                           false
% 19.12/2.98  --trig_cnt_out                          false
% 19.12/2.98  --trig_cnt_out_tolerance                1.
% 19.12/2.98  --trig_cnt_out_sk_spl                   false
% 19.12/2.98  --abstr_cl_out                          false
% 19.12/2.98  
% 19.12/2.98  ------ Global Options
% 19.12/2.98  
% 19.12/2.98  --schedule                              default
% 19.12/2.98  --add_important_lit                     false
% 19.12/2.98  --prop_solver_per_cl                    1000
% 19.12/2.98  --min_unsat_core                        false
% 19.12/2.98  --soft_assumptions                      false
% 19.12/2.98  --soft_lemma_size                       3
% 19.12/2.98  --prop_impl_unit_size                   0
% 19.12/2.98  --prop_impl_unit                        []
% 19.12/2.98  --share_sel_clauses                     true
% 19.12/2.98  --reset_solvers                         false
% 19.12/2.98  --bc_imp_inh                            [conj_cone]
% 19.12/2.98  --conj_cone_tolerance                   3.
% 19.12/2.98  --extra_neg_conj                        none
% 19.12/2.98  --large_theory_mode                     true
% 19.12/2.98  --prolific_symb_bound                   200
% 19.12/2.98  --lt_threshold                          2000
% 19.12/2.98  --clause_weak_htbl                      true
% 19.12/2.98  --gc_record_bc_elim                     false
% 19.12/2.98  
% 19.12/2.98  ------ Preprocessing Options
% 19.12/2.98  
% 19.12/2.98  --preprocessing_flag                    true
% 19.12/2.98  --time_out_prep_mult                    0.1
% 19.12/2.98  --splitting_mode                        input
% 19.12/2.98  --splitting_grd                         true
% 19.12/2.98  --splitting_cvd                         false
% 19.12/2.98  --splitting_cvd_svl                     false
% 19.12/2.98  --splitting_nvd                         32
% 19.12/2.98  --sub_typing                            true
% 19.12/2.98  --prep_gs_sim                           true
% 19.12/2.98  --prep_unflatten                        true
% 19.12/2.98  --prep_res_sim                          true
% 19.12/2.98  --prep_upred                            true
% 19.12/2.98  --prep_sem_filter                       exhaustive
% 19.12/2.98  --prep_sem_filter_out                   false
% 19.12/2.98  --pred_elim                             true
% 19.12/2.98  --res_sim_input                         true
% 19.12/2.98  --eq_ax_congr_red                       true
% 19.12/2.98  --pure_diseq_elim                       true
% 19.12/2.98  --brand_transform                       false
% 19.12/2.98  --non_eq_to_eq                          false
% 19.12/2.98  --prep_def_merge                        true
% 19.12/2.98  --prep_def_merge_prop_impl              false
% 19.12/2.98  --prep_def_merge_mbd                    true
% 19.12/2.98  --prep_def_merge_tr_red                 false
% 19.12/2.98  --prep_def_merge_tr_cl                  false
% 19.12/2.98  --smt_preprocessing                     true
% 19.12/2.98  --smt_ac_axioms                         fast
% 19.12/2.98  --preprocessed_out                      false
% 19.12/2.98  --preprocessed_stats                    false
% 19.12/2.98  
% 19.12/2.98  ------ Abstraction refinement Options
% 19.12/2.98  
% 19.12/2.98  --abstr_ref                             []
% 19.12/2.98  --abstr_ref_prep                        false
% 19.12/2.98  --abstr_ref_until_sat                   false
% 19.12/2.98  --abstr_ref_sig_restrict                funpre
% 19.12/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.12/2.98  --abstr_ref_under                       []
% 19.12/2.98  
% 19.12/2.98  ------ SAT Options
% 19.12/2.98  
% 19.12/2.98  --sat_mode                              false
% 19.12/2.98  --sat_fm_restart_options                ""
% 19.12/2.98  --sat_gr_def                            false
% 19.12/2.98  --sat_epr_types                         true
% 19.12/2.98  --sat_non_cyclic_types                  false
% 19.12/2.98  --sat_finite_models                     false
% 19.12/2.98  --sat_fm_lemmas                         false
% 19.12/2.98  --sat_fm_prep                           false
% 19.12/2.98  --sat_fm_uc_incr                        true
% 19.12/2.98  --sat_out_model                         small
% 19.12/2.98  --sat_out_clauses                       false
% 19.12/2.98  
% 19.12/2.98  ------ QBF Options
% 19.12/2.98  
% 19.12/2.98  --qbf_mode                              false
% 19.12/2.98  --qbf_elim_univ                         false
% 19.12/2.98  --qbf_dom_inst                          none
% 19.12/2.98  --qbf_dom_pre_inst                      false
% 19.12/2.98  --qbf_sk_in                             false
% 19.12/2.98  --qbf_pred_elim                         true
% 19.12/2.98  --qbf_split                             512
% 19.12/2.98  
% 19.12/2.98  ------ BMC1 Options
% 19.12/2.98  
% 19.12/2.98  --bmc1_incremental                      false
% 19.12/2.98  --bmc1_axioms                           reachable_all
% 19.12/2.98  --bmc1_min_bound                        0
% 19.12/2.98  --bmc1_max_bound                        -1
% 19.12/2.98  --bmc1_max_bound_default                -1
% 19.12/2.98  --bmc1_symbol_reachability              true
% 19.12/2.98  --bmc1_property_lemmas                  false
% 19.12/2.98  --bmc1_k_induction                      false
% 19.12/2.98  --bmc1_non_equiv_states                 false
% 19.12/2.98  --bmc1_deadlock                         false
% 19.12/2.98  --bmc1_ucm                              false
% 19.12/2.98  --bmc1_add_unsat_core                   none
% 19.12/2.98  --bmc1_unsat_core_children              false
% 19.12/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.12/2.98  --bmc1_out_stat                         full
% 19.12/2.98  --bmc1_ground_init                      false
% 19.12/2.98  --bmc1_pre_inst_next_state              false
% 19.12/2.98  --bmc1_pre_inst_state                   false
% 19.12/2.98  --bmc1_pre_inst_reach_state             false
% 19.12/2.98  --bmc1_out_unsat_core                   false
% 19.12/2.98  --bmc1_aig_witness_out                  false
% 19.12/2.98  --bmc1_verbose                          false
% 19.12/2.98  --bmc1_dump_clauses_tptp                false
% 19.12/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.12/2.98  --bmc1_dump_file                        -
% 19.12/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.12/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.12/2.98  --bmc1_ucm_extend_mode                  1
% 19.12/2.98  --bmc1_ucm_init_mode                    2
% 19.12/2.98  --bmc1_ucm_cone_mode                    none
% 19.12/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.12/2.98  --bmc1_ucm_relax_model                  4
% 19.12/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.12/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.12/2.98  --bmc1_ucm_layered_model                none
% 19.12/2.98  --bmc1_ucm_max_lemma_size               10
% 19.12/2.98  
% 19.12/2.98  ------ AIG Options
% 19.12/2.98  
% 19.12/2.98  --aig_mode                              false
% 19.12/2.98  
% 19.12/2.98  ------ Instantiation Options
% 19.12/2.98  
% 19.12/2.98  --instantiation_flag                    true
% 19.12/2.98  --inst_sos_flag                         false
% 19.12/2.98  --inst_sos_phase                        true
% 19.12/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.12/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.12/2.98  --inst_lit_sel_side                     none
% 19.12/2.98  --inst_solver_per_active                1400
% 19.12/2.98  --inst_solver_calls_frac                1.
% 19.12/2.98  --inst_passive_queue_type               priority_queues
% 19.12/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.12/2.98  --inst_passive_queues_freq              [25;2]
% 19.12/2.98  --inst_dismatching                      true
% 19.12/2.98  --inst_eager_unprocessed_to_passive     true
% 19.12/2.98  --inst_prop_sim_given                   true
% 19.12/2.98  --inst_prop_sim_new                     false
% 19.12/2.98  --inst_subs_new                         false
% 19.12/2.98  --inst_eq_res_simp                      false
% 19.12/2.98  --inst_subs_given                       false
% 19.12/2.98  --inst_orphan_elimination               true
% 19.12/2.98  --inst_learning_loop_flag               true
% 19.12/2.98  --inst_learning_start                   3000
% 19.12/2.98  --inst_learning_factor                  2
% 19.12/2.98  --inst_start_prop_sim_after_learn       3
% 19.12/2.98  --inst_sel_renew                        solver
% 19.12/2.98  --inst_lit_activity_flag                true
% 19.12/2.98  --inst_restr_to_given                   false
% 19.12/2.98  --inst_activity_threshold               500
% 19.12/2.98  --inst_out_proof                        true
% 19.12/2.98  
% 19.12/2.98  ------ Resolution Options
% 19.12/2.98  
% 19.12/2.98  --resolution_flag                       false
% 19.12/2.98  --res_lit_sel                           adaptive
% 19.12/2.98  --res_lit_sel_side                      none
% 19.12/2.98  --res_ordering                          kbo
% 19.12/2.98  --res_to_prop_solver                    active
% 19.12/2.98  --res_prop_simpl_new                    false
% 19.12/2.98  --res_prop_simpl_given                  true
% 19.12/2.98  --res_passive_queue_type                priority_queues
% 19.12/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.12/2.98  --res_passive_queues_freq               [15;5]
% 19.12/2.98  --res_forward_subs                      full
% 19.12/2.98  --res_backward_subs                     full
% 19.12/2.98  --res_forward_subs_resolution           true
% 19.12/2.98  --res_backward_subs_resolution          true
% 19.12/2.98  --res_orphan_elimination                true
% 19.12/2.98  --res_time_limit                        2.
% 19.12/2.98  --res_out_proof                         true
% 19.12/2.98  
% 19.12/2.98  ------ Superposition Options
% 19.12/2.98  
% 19.12/2.98  --superposition_flag                    true
% 19.12/2.98  --sup_passive_queue_type                priority_queues
% 19.12/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.12/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.12/2.98  --demod_completeness_check              fast
% 19.12/2.98  --demod_use_ground                      true
% 19.12/2.98  --sup_to_prop_solver                    passive
% 19.12/2.98  --sup_prop_simpl_new                    true
% 19.12/2.98  --sup_prop_simpl_given                  true
% 19.12/2.98  --sup_fun_splitting                     false
% 19.12/2.98  --sup_smt_interval                      50000
% 19.12/2.98  
% 19.12/2.98  ------ Superposition Simplification Setup
% 19.12/2.98  
% 19.12/2.98  --sup_indices_passive                   []
% 19.12/2.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.12/2.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.12/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.12/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.12/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.12/2.98  --sup_full_bw                           [BwDemod]
% 19.12/2.98  --sup_immed_triv                        [TrivRules]
% 19.12/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.12/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.12/2.98  --sup_immed_bw_main                     []
% 19.12/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.12/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.12/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.12/2.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.12/2.98  
% 19.12/2.98  ------ Combination Options
% 19.12/2.98  
% 19.12/2.98  --comb_res_mult                         3
% 19.12/2.98  --comb_sup_mult                         2
% 19.12/2.98  --comb_inst_mult                        10
% 19.12/2.98  
% 19.12/2.98  ------ Debug Options
% 19.12/2.98  
% 19.12/2.98  --dbg_backtrace                         false
% 19.12/2.98  --dbg_dump_prop_clauses                 false
% 19.12/2.98  --dbg_dump_prop_clauses_file            -
% 19.12/2.98  --dbg_out_stat                          false
% 19.12/2.98  
% 19.12/2.98  
% 19.12/2.98  
% 19.12/2.98  
% 19.12/2.98  ------ Proving...
% 19.12/2.98  
% 19.12/2.98  
% 19.12/2.98  % SZS status Theorem for theBenchmark.p
% 19.12/2.98  
% 19.12/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.12/2.98  
% 19.12/2.98  fof(f29,conjecture,(
% 19.12/2.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f30,negated_conjecture,(
% 19.12/2.98    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 19.12/2.98    inference(negated_conjecture,[],[f29])).
% 19.12/2.98  
% 19.12/2.98  fof(f48,plain,(
% 19.12/2.98    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 19.12/2.98    inference(ennf_transformation,[],[f30])).
% 19.12/2.98  
% 19.12/2.98  fof(f49,plain,(
% 19.12/2.98    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 19.12/2.98    inference(flattening,[],[f48])).
% 19.12/2.98  
% 19.12/2.98  fof(f53,plain,(
% 19.12/2.98    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 19.12/2.98    introduced(choice_axiom,[])).
% 19.12/2.98  
% 19.12/2.98  fof(f54,plain,(
% 19.12/2.98    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 19.12/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f53])).
% 19.12/2.98  
% 19.12/2.98  fof(f88,plain,(
% 19.12/2.98    v1_relat_1(sK2)),
% 19.12/2.98    inference(cnf_transformation,[],[f54])).
% 19.12/2.98  
% 19.12/2.98  fof(f26,axiom,(
% 19.12/2.98    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f84,plain,(
% 19.12/2.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 19.12/2.98    inference(cnf_transformation,[],[f26])).
% 19.12/2.98  
% 19.12/2.98  fof(f21,axiom,(
% 19.12/2.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f40,plain,(
% 19.12/2.98    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.12/2.98    inference(ennf_transformation,[],[f21])).
% 19.12/2.98  
% 19.12/2.98  fof(f78,plain,(
% 19.12/2.98    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.12/2.98    inference(cnf_transformation,[],[f40])).
% 19.12/2.98  
% 19.12/2.98  fof(f25,axiom,(
% 19.12/2.98    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f44,plain,(
% 19.12/2.98    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 19.12/2.98    inference(ennf_transformation,[],[f25])).
% 19.12/2.98  
% 19.12/2.98  fof(f83,plain,(
% 19.12/2.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 19.12/2.98    inference(cnf_transformation,[],[f44])).
% 19.12/2.98  
% 19.12/2.98  fof(f91,plain,(
% 19.12/2.98    r1_tarski(sK0,k1_relat_1(sK2))),
% 19.12/2.98    inference(cnf_transformation,[],[f54])).
% 19.12/2.98  
% 19.12/2.98  fof(f22,axiom,(
% 19.12/2.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f80,plain,(
% 19.12/2.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 19.12/2.98    inference(cnf_transformation,[],[f22])).
% 19.12/2.98  
% 19.12/2.98  fof(f23,axiom,(
% 19.12/2.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f41,plain,(
% 19.12/2.98    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 19.12/2.98    inference(ennf_transformation,[],[f23])).
% 19.12/2.98  
% 19.12/2.98  fof(f42,plain,(
% 19.12/2.98    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 19.12/2.98    inference(flattening,[],[f41])).
% 19.12/2.98  
% 19.12/2.98  fof(f81,plain,(
% 19.12/2.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 19.12/2.98    inference(cnf_transformation,[],[f42])).
% 19.12/2.98  
% 19.12/2.98  fof(f19,axiom,(
% 19.12/2.98    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f37,plain,(
% 19.12/2.98    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 19.12/2.98    inference(ennf_transformation,[],[f19])).
% 19.12/2.98  
% 19.12/2.98  fof(f76,plain,(
% 19.12/2.98    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 19.12/2.98    inference(cnf_transformation,[],[f37])).
% 19.12/2.98  
% 19.12/2.98  fof(f79,plain,(
% 19.12/2.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 19.12/2.98    inference(cnf_transformation,[],[f22])).
% 19.12/2.98  
% 19.12/2.98  fof(f27,axiom,(
% 19.12/2.98    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f45,plain,(
% 19.12/2.98    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 19.12/2.98    inference(ennf_transformation,[],[f27])).
% 19.12/2.98  
% 19.12/2.98  fof(f86,plain,(
% 19.12/2.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 19.12/2.98    inference(cnf_transformation,[],[f45])).
% 19.12/2.98  
% 19.12/2.98  fof(f7,axiom,(
% 19.12/2.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f64,plain,(
% 19.12/2.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 19.12/2.98    inference(cnf_transformation,[],[f7])).
% 19.12/2.98  
% 19.12/2.98  fof(f103,plain,(
% 19.12/2.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 19.12/2.98    inference(definition_unfolding,[],[f86,f64])).
% 19.12/2.98  
% 19.12/2.98  fof(f3,axiom,(
% 19.12/2.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f52,plain,(
% 19.12/2.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 19.12/2.98    inference(nnf_transformation,[],[f3])).
% 19.12/2.98  
% 19.12/2.98  fof(f60,plain,(
% 19.12/2.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 19.12/2.98    inference(cnf_transformation,[],[f52])).
% 19.12/2.98  
% 19.12/2.98  fof(f6,axiom,(
% 19.12/2.98    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f63,plain,(
% 19.12/2.98    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 19.12/2.98    inference(cnf_transformation,[],[f6])).
% 19.12/2.98  
% 19.12/2.98  fof(f101,plain,(
% 19.12/2.98    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 19.12/2.98    inference(definition_unfolding,[],[f63,f64])).
% 19.12/2.98  
% 19.12/2.98  fof(f4,axiom,(
% 19.12/2.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f61,plain,(
% 19.12/2.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 19.12/2.98    inference(cnf_transformation,[],[f4])).
% 19.12/2.98  
% 19.12/2.98  fof(f99,plain,(
% 19.12/2.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 19.12/2.98    inference(definition_unfolding,[],[f61,f64])).
% 19.12/2.98  
% 19.12/2.98  fof(f8,axiom,(
% 19.12/2.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f65,plain,(
% 19.12/2.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.12/2.98    inference(cnf_transformation,[],[f8])).
% 19.12/2.98  
% 19.12/2.98  fof(f16,axiom,(
% 19.12/2.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f34,plain,(
% 19.12/2.98    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 19.12/2.98    inference(ennf_transformation,[],[f16])).
% 19.12/2.98  
% 19.12/2.98  fof(f73,plain,(
% 19.12/2.98    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 19.12/2.98    inference(cnf_transformation,[],[f34])).
% 19.12/2.98  
% 19.12/2.98  fof(f17,axiom,(
% 19.12/2.98    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f35,plain,(
% 19.12/2.98    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 19.12/2.98    inference(ennf_transformation,[],[f17])).
% 19.12/2.98  
% 19.12/2.98  fof(f74,plain,(
% 19.12/2.98    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 19.12/2.98    inference(cnf_transformation,[],[f35])).
% 19.12/2.98  
% 19.12/2.98  fof(f2,axiom,(
% 19.12/2.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f50,plain,(
% 19.12/2.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.12/2.98    inference(nnf_transformation,[],[f2])).
% 19.12/2.98  
% 19.12/2.98  fof(f51,plain,(
% 19.12/2.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.12/2.98    inference(flattening,[],[f50])).
% 19.12/2.98  
% 19.12/2.98  fof(f56,plain,(
% 19.12/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.12/2.98    inference(cnf_transformation,[],[f51])).
% 19.12/2.98  
% 19.12/2.98  fof(f105,plain,(
% 19.12/2.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.12/2.98    inference(equality_resolution,[],[f56])).
% 19.12/2.98  
% 19.12/2.98  fof(f18,axiom,(
% 19.12/2.98    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f36,plain,(
% 19.12/2.98    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 19.12/2.98    inference(ennf_transformation,[],[f18])).
% 19.12/2.98  
% 19.12/2.98  fof(f75,plain,(
% 19.12/2.98    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 19.12/2.98    inference(cnf_transformation,[],[f36])).
% 19.12/2.98  
% 19.12/2.98  fof(f90,plain,(
% 19.12/2.98    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 19.12/2.98    inference(cnf_transformation,[],[f54])).
% 19.12/2.98  
% 19.12/2.98  fof(f20,axiom,(
% 19.12/2.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f38,plain,(
% 19.12/2.98    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 19.12/2.98    inference(ennf_transformation,[],[f20])).
% 19.12/2.98  
% 19.12/2.98  fof(f39,plain,(
% 19.12/2.98    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 19.12/2.98    inference(flattening,[],[f38])).
% 19.12/2.98  
% 19.12/2.98  fof(f77,plain,(
% 19.12/2.98    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 19.12/2.98    inference(cnf_transformation,[],[f39])).
% 19.12/2.98  
% 19.12/2.98  fof(f59,plain,(
% 19.12/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 19.12/2.98    inference(cnf_transformation,[],[f52])).
% 19.12/2.98  
% 19.12/2.98  fof(f28,axiom,(
% 19.12/2.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f46,plain,(
% 19.12/2.98    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 19.12/2.98    inference(ennf_transformation,[],[f28])).
% 19.12/2.98  
% 19.12/2.98  fof(f47,plain,(
% 19.12/2.98    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 19.12/2.98    inference(flattening,[],[f46])).
% 19.12/2.98  
% 19.12/2.98  fof(f87,plain,(
% 19.12/2.98    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.12/2.98    inference(cnf_transformation,[],[f47])).
% 19.12/2.98  
% 19.12/2.98  fof(f92,plain,(
% 19.12/2.98    v2_funct_1(sK2)),
% 19.12/2.98    inference(cnf_transformation,[],[f54])).
% 19.12/2.98  
% 19.12/2.98  fof(f89,plain,(
% 19.12/2.98    v1_funct_1(sK2)),
% 19.12/2.98    inference(cnf_transformation,[],[f54])).
% 19.12/2.98  
% 19.12/2.98  fof(f5,axiom,(
% 19.12/2.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 19.12/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.12/2.98  
% 19.12/2.98  fof(f32,plain,(
% 19.12/2.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 19.12/2.98    inference(ennf_transformation,[],[f5])).
% 19.12/2.98  
% 19.12/2.98  fof(f33,plain,(
% 19.12/2.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 19.12/2.98    inference(flattening,[],[f32])).
% 19.12/2.98  
% 19.12/2.98  fof(f62,plain,(
% 19.12/2.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 19.12/2.98    inference(cnf_transformation,[],[f33])).
% 19.12/2.98  
% 19.12/2.98  fof(f93,plain,(
% 19.12/2.98    ~r1_tarski(sK0,sK1)),
% 19.12/2.98    inference(cnf_transformation,[],[f54])).
% 19.12/2.98  
% 19.12/2.98  cnf(c_31,negated_conjecture,
% 19.12/2.98      ( v1_relat_1(sK2) ),
% 19.12/2.98      inference(cnf_transformation,[],[f88]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1028,plain,
% 19.12/2.98      ( v1_relat_1(sK2) = iProver_top ),
% 19.12/2.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_23,plain,
% 19.12/2.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 19.12/2.98      inference(cnf_transformation,[],[f84]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1033,plain,
% 19.12/2.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 19.12/2.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_16,plain,
% 19.12/2.98      ( ~ v1_relat_1(X0)
% 19.12/2.98      | ~ v1_relat_1(X1)
% 19.12/2.98      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 19.12/2.98      inference(cnf_transformation,[],[f78]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1037,plain,
% 19.12/2.98      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 19.12/2.98      | v1_relat_1(X0) != iProver_top
% 19.12/2.98      | v1_relat_1(X1) != iProver_top ),
% 19.12/2.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_5534,plain,
% 19.12/2.98      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
% 19.12/2.98      | v1_relat_1(X1) != iProver_top ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1033,c_1037]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_26111,plain,
% 19.12/2.98      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK2)) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1028,c_5534]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_21,plain,
% 19.12/2.98      ( ~ v1_relat_1(X0)
% 19.12/2.98      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 19.12/2.98      inference(cnf_transformation,[],[f83]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1034,plain,
% 19.12/2.98      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 19.12/2.98      | v1_relat_1(X1) != iProver_top ),
% 19.12/2.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_2074,plain,
% 19.12/2.98      ( k5_relat_1(k6_relat_1(X0),sK2) = k7_relat_1(sK2,X0) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1028,c_1034]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_26113,plain,
% 19.12/2.98      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(sK2)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 19.12/2.98      inference(light_normalisation,[status(thm)],[c_26111,c_2074]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_2073,plain,
% 19.12/2.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1033,c_1034]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_28,negated_conjecture,
% 19.12/2.98      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 19.12/2.98      inference(cnf_transformation,[],[f91]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1030,plain,
% 19.12/2.98      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 19.12/2.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_17,plain,
% 19.12/2.98      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 19.12/2.98      inference(cnf_transformation,[],[f80]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_19,plain,
% 19.12/2.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 19.12/2.98      | ~ v1_relat_1(X0)
% 19.12/2.98      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 19.12/2.98      inference(cnf_transformation,[],[f81]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1036,plain,
% 19.12/2.98      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 19.12/2.98      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 19.12/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.12/2.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_4183,plain,
% 19.12/2.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 19.12/2.98      | r1_tarski(X0,X1) != iProver_top
% 19.12/2.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_17,c_1036]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_44,plain,
% 19.12/2.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 19.12/2.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_7292,plain,
% 19.12/2.98      ( r1_tarski(X0,X1) != iProver_top
% 19.12/2.98      | k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0) ),
% 19.12/2.98      inference(global_propositional_subsumption,
% 19.12/2.98                [status(thm)],
% 19.12/2.98                [c_4183,c_44]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_7293,plain,
% 19.12/2.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 19.12/2.98      | r1_tarski(X0,X1) != iProver_top ),
% 19.12/2.98      inference(renaming,[status(thm)],[c_7292]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_7303,plain,
% 19.12/2.98      ( k5_relat_1(k6_relat_1(sK0),k6_relat_1(k1_relat_1(sK2))) = k6_relat_1(sK0) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1030,c_7293]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_9358,plain,
% 19.12/2.98      ( k7_relat_1(k6_relat_1(k1_relat_1(sK2)),sK0) = k6_relat_1(sK0) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_2073,c_7303]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_14,plain,
% 19.12/2.98      ( ~ v1_relat_1(X0)
% 19.12/2.98      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 19.12/2.98      inference(cnf_transformation,[],[f76]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1039,plain,
% 19.12/2.98      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 19.12/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.12/2.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_3370,plain,
% 19.12/2.98      ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1033,c_1039]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_18,plain,
% 19.12/2.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 19.12/2.98      inference(cnf_transformation,[],[f79]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_3375,plain,
% 19.12/2.98      ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
% 19.12/2.98      inference(light_normalisation,[status(thm)],[c_3370,c_17,c_18]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_24,plain,
% 19.12/2.98      ( ~ v1_relat_1(X0)
% 19.12/2.98      | k4_xboole_0(X1,k4_xboole_0(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 19.12/2.98      inference(cnf_transformation,[],[f103]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1032,plain,
% 19.12/2.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 19.12/2.98      | v1_relat_1(X1) != iProver_top ),
% 19.12/2.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1954,plain,
% 19.12/2.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(k6_relat_1(X1),X2))) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1033,c_1032]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_16645,plain,
% 19.12/2.98      ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_3375,c_1954]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_16790,plain,
% 19.12/2.98      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK2))) = k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK2)) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_9358,c_16645]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_5,plain,
% 19.12/2.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 19.12/2.98      inference(cnf_transformation,[],[f60]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1045,plain,
% 19.12/2.98      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 19.12/2.98      | r1_tarski(X0,X1) != iProver_top ),
% 19.12/2.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_2364,plain,
% 19.12/2.98      ( k4_xboole_0(sK0,k1_relat_1(sK2)) = k1_xboole_0 ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1030,c_1045]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_16914,plain,
% 19.12/2.98      ( k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 19.12/2.98      inference(light_normalisation,[status(thm)],[c_16790,c_2364]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_8,plain,
% 19.12/2.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 19.12/2.98      inference(cnf_transformation,[],[f101]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_0,plain,
% 19.12/2.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 19.12/2.98      inference(cnf_transformation,[],[f99]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1432,plain,
% 19.12/2.98      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_9,plain,
% 19.12/2.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.12/2.98      inference(cnf_transformation,[],[f65]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1442,plain,
% 19.12/2.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.12/2.98      inference(light_normalisation,[status(thm)],[c_1432,c_9]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_16915,plain,
% 19.12/2.98      ( k10_relat_1(k6_relat_1(sK0),k1_relat_1(sK2)) = sK0 ),
% 19.12/2.98      inference(demodulation,[status(thm)],[c_16914,c_1442]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_27020,plain,
% 19.12/2.98      ( k1_relat_1(k7_relat_1(sK2,sK0)) = sK0 ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_26113,c_16915]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_11,plain,
% 19.12/2.98      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 19.12/2.98      inference(cnf_transformation,[],[f73]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1042,plain,
% 19.12/2.98      ( v1_relat_1(X0) != iProver_top
% 19.12/2.98      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 19.12/2.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_12,plain,
% 19.12/2.98      ( ~ v1_relat_1(X0)
% 19.12/2.98      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 19.12/2.98      inference(cnf_transformation,[],[f74]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1041,plain,
% 19.12/2.98      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 19.12/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.12/2.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_3596,plain,
% 19.12/2.98      ( k9_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1))) = k2_relat_1(k7_relat_1(X0,X1))
% 19.12/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1042,c_1041]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_18002,plain,
% 19.12/2.98      ( k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0)) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1028,c_3596]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_38201,plain,
% 19.12/2.98      ( k9_relat_1(k7_relat_1(sK2,sK0),sK0) = k2_relat_1(k7_relat_1(sK2,sK0)) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_27020,c_18002]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_4,plain,
% 19.12/2.98      ( r1_tarski(X0,X0) ),
% 19.12/2.98      inference(cnf_transformation,[],[f105]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1046,plain,
% 19.12/2.98      ( r1_tarski(X0,X0) = iProver_top ),
% 19.12/2.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_13,plain,
% 19.12/2.98      ( ~ r1_tarski(X0,X1)
% 19.12/2.98      | ~ v1_relat_1(X2)
% 19.12/2.98      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 19.12/2.98      inference(cnf_transformation,[],[f75]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1040,plain,
% 19.12/2.98      ( k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
% 19.12/2.98      | r1_tarski(X2,X1) != iProver_top
% 19.12/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.12/2.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_7002,plain,
% 19.12/2.98      ( k9_relat_1(k7_relat_1(X0,X1),X1) = k9_relat_1(X0,X1)
% 19.12/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1046,c_1040]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_23645,plain,
% 19.12/2.98      ( k9_relat_1(k7_relat_1(sK2,X0),X0) = k9_relat_1(sK2,X0) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1028,c_7002]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_38237,plain,
% 19.12/2.98      ( k2_relat_1(k7_relat_1(sK2,sK0)) = k9_relat_1(sK2,sK0) ),
% 19.12/2.98      inference(demodulation,[status(thm)],[c_38201,c_23645]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_3369,plain,
% 19.12/2.98      ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
% 19.12/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1042,c_1039]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_16400,plain,
% 19.12/2.98      ( k10_relat_1(k7_relat_1(sK2,X0),k2_relat_1(k7_relat_1(sK2,X0))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1028,c_3369]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_38534,plain,
% 19.12/2.98      ( k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK0)) = k1_relat_1(k7_relat_1(sK2,sK0)) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_38237,c_16400]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_38544,plain,
% 19.12/2.98      ( k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK0)) = sK0 ),
% 19.12/2.98      inference(light_normalisation,[status(thm)],[c_38534,c_27020]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_29,negated_conjecture,
% 19.12/2.98      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 19.12/2.98      inference(cnf_transformation,[],[f90]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1029,plain,
% 19.12/2.98      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 19.12/2.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_15,plain,
% 19.12/2.98      ( ~ r1_tarski(X0,X1)
% 19.12/2.98      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
% 19.12/2.98      | ~ v1_relat_1(X2) ),
% 19.12/2.98      inference(cnf_transformation,[],[f77]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1038,plain,
% 19.12/2.98      ( r1_tarski(X0,X1) != iProver_top
% 19.12/2.98      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = iProver_top
% 19.12/2.98      | v1_relat_1(X2) != iProver_top ),
% 19.12/2.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_5857,plain,
% 19.12/2.98      ( k4_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k1_xboole_0
% 19.12/2.98      | r1_tarski(X1,X2) != iProver_top
% 19.12/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1038,c_1045]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_82923,plain,
% 19.12/2.98      ( k4_xboole_0(k10_relat_1(X0,k9_relat_1(sK2,sK0)),k10_relat_1(X0,k9_relat_1(sK2,sK1))) = k1_xboole_0
% 19.12/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1029,c_5857]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_84328,plain,
% 19.12/2.98      ( k4_xboole_0(k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(sK2,sK0)),k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(sK2,sK1))) = k1_xboole_0
% 19.12/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1042,c_82923]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_89779,plain,
% 19.12/2.98      ( k4_xboole_0(k10_relat_1(k7_relat_1(sK2,X0),k9_relat_1(sK2,sK0)),k10_relat_1(k7_relat_1(sK2,X0),k9_relat_1(sK2,sK1))) = k1_xboole_0 ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1028,c_84328]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_90702,plain,
% 19.12/2.98      ( k4_xboole_0(sK0,k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k1_xboole_0 ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_38544,c_89779]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1332,plain,
% 19.12/2.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK2,X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1028,c_1032]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1597,plain,
% 19.12/2.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(k7_relat_1(sK2,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK2,X1))) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1332,c_0]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1604,plain,
% 19.12/2.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(k7_relat_1(sK2,X0),X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
% 19.12/2.98      inference(light_normalisation,[status(thm)],[c_1597,c_1332]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_91135,plain,
% 19.12/2.98      ( k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_90702,c_1604]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_91141,plain,
% 19.12/2.98      ( k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = sK0 ),
% 19.12/2.98      inference(demodulation,[status(thm)],[c_91135,c_9]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1598,plain,
% 19.12/2.98      ( k5_xboole_0(X0,k10_relat_1(k7_relat_1(sK2,X0),X1)) = k4_xboole_0(X0,k10_relat_1(sK2,X1)) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_1332,c_0]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_93103,plain,
% 19.12/2.98      ( k4_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) = k5_xboole_0(sK0,sK0) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_91141,c_1598]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_2474,plain,
% 19.12/2.98      ( k5_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,k1_relat_1(sK2)) ),
% 19.12/2.98      inference(superposition,[status(thm)],[c_2364,c_0]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_2475,plain,
% 19.12/2.98      ( k5_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 19.12/2.98      inference(light_normalisation,[status(thm)],[c_2474,c_2364]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_2477,plain,
% 19.12/2.98      ( k5_xboole_0(sK0,sK0) = k1_xboole_0 ),
% 19.12/2.98      inference(demodulation,[status(thm)],[c_2475,c_1442]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_93164,plain,
% 19.12/2.98      ( k4_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) = k1_xboole_0 ),
% 19.12/2.98      inference(light_normalisation,[status(thm)],[c_93103,c_2477]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_6,plain,
% 19.12/2.98      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 19.12/2.98      inference(cnf_transformation,[],[f59]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1348,plain,
% 19.12/2.98      ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
% 19.12/2.98      | k4_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) != k1_xboole_0 ),
% 19.12/2.98      inference(instantiation,[status(thm)],[c_6]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_25,plain,
% 19.12/2.98      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 19.12/2.98      | ~ v2_funct_1(X0)
% 19.12/2.98      | ~ v1_funct_1(X0)
% 19.12/2.98      | ~ v1_relat_1(X0) ),
% 19.12/2.98      inference(cnf_transformation,[],[f87]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_27,negated_conjecture,
% 19.12/2.98      ( v2_funct_1(sK2) ),
% 19.12/2.98      inference(cnf_transformation,[],[f92]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_339,plain,
% 19.12/2.98      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 19.12/2.98      | ~ v1_funct_1(X0)
% 19.12/2.98      | ~ v1_relat_1(X0)
% 19.12/2.98      | sK2 != X0 ),
% 19.12/2.98      inference(resolution_lifted,[status(thm)],[c_25,c_27]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_340,plain,
% 19.12/2.98      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
% 19.12/2.98      | ~ v1_funct_1(sK2)
% 19.12/2.98      | ~ v1_relat_1(sK2) ),
% 19.12/2.98      inference(unflattening,[status(thm)],[c_339]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_30,negated_conjecture,
% 19.12/2.98      ( v1_funct_1(sK2) ),
% 19.12/2.98      inference(cnf_transformation,[],[f89]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_344,plain,
% 19.12/2.98      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ),
% 19.12/2.98      inference(global_propositional_subsumption,
% 19.12/2.98                [status(thm)],
% 19.12/2.98                [c_340,c_31,c_30]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1268,plain,
% 19.12/2.98      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),sK1) ),
% 19.12/2.98      inference(instantiation,[status(thm)],[c_344]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_7,plain,
% 19.12/2.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 19.12/2.98      inference(cnf_transformation,[],[f62]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1195,plain,
% 19.12/2.98      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK0,X0) | r1_tarski(sK0,sK1) ),
% 19.12/2.98      inference(instantiation,[status(thm)],[c_7]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_1267,plain,
% 19.12/2.98      ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK1)),sK1)
% 19.12/2.98      | ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
% 19.12/2.98      | r1_tarski(sK0,sK1) ),
% 19.12/2.98      inference(instantiation,[status(thm)],[c_1195]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(c_26,negated_conjecture,
% 19.12/2.98      ( ~ r1_tarski(sK0,sK1) ),
% 19.12/2.98      inference(cnf_transformation,[],[f93]) ).
% 19.12/2.98  
% 19.12/2.98  cnf(contradiction,plain,
% 19.12/2.98      ( $false ),
% 19.12/2.98      inference(minisat,[status(thm)],[c_93164,c_1348,c_1268,c_1267,c_26]) ).
% 19.12/2.98  
% 19.12/2.98  
% 19.12/2.98  % SZS output end CNFRefutation for theBenchmark.p
% 19.12/2.98  
% 19.12/2.98  ------                               Statistics
% 19.12/2.98  
% 19.12/2.98  ------ General
% 19.12/2.98  
% 19.12/2.98  abstr_ref_over_cycles:                  0
% 19.12/2.98  abstr_ref_under_cycles:                 0
% 19.12/2.98  gc_basic_clause_elim:                   0
% 19.12/2.98  forced_gc_time:                         0
% 19.12/2.98  parsing_time:                           0.009
% 19.12/2.98  unif_index_cands_time:                  0.
% 19.12/2.98  unif_index_add_time:                    0.
% 19.12/2.98  orderings_time:                         0.
% 19.12/2.98  out_proof_time:                         0.014
% 19.12/2.98  total_time:                             2.499
% 19.12/2.98  num_of_symbols:                         50
% 19.12/2.98  num_of_terms:                           83381
% 19.12/2.98  
% 19.12/2.98  ------ Preprocessing
% 19.12/2.98  
% 19.12/2.98  num_of_splits:                          0
% 19.12/2.98  num_of_split_atoms:                     0
% 19.12/2.98  num_of_reused_defs:                     0
% 19.12/2.98  num_eq_ax_congr_red:                    39
% 19.12/2.98  num_of_sem_filtered_clauses:            1
% 19.12/2.98  num_of_subtypes:                        0
% 19.12/2.98  monotx_restored_types:                  0
% 19.12/2.98  sat_num_of_epr_types:                   0
% 19.12/2.98  sat_num_of_non_cyclic_types:            0
% 19.12/2.98  sat_guarded_non_collapsed_types:        0
% 19.12/2.98  num_pure_diseq_elim:                    0
% 19.12/2.98  simp_replaced_by:                       0
% 19.12/2.98  res_preprocessed:                       140
% 19.12/2.98  prep_upred:                             0
% 19.12/2.98  prep_unflattend:                        1
% 19.12/2.98  smt_new_axioms:                         0
% 19.12/2.98  pred_elim_cands:                        2
% 19.12/2.98  pred_elim:                              2
% 19.12/2.98  pred_elim_cl:                           3
% 19.12/2.98  pred_elim_cycles:                       4
% 19.12/2.98  merged_defs:                            8
% 19.12/2.98  merged_defs_ncl:                        0
% 19.12/2.98  bin_hyper_res:                          8
% 19.12/2.98  prep_cycles:                            4
% 19.12/2.98  pred_elim_time:                         0.001
% 19.12/2.98  splitting_time:                         0.
% 19.12/2.98  sem_filter_time:                        0.
% 19.12/2.98  monotx_time:                            0.
% 19.12/2.98  subtype_inf_time:                       0.
% 19.12/2.98  
% 19.12/2.98  ------ Problem properties
% 19.12/2.98  
% 19.12/2.98  clauses:                                28
% 19.12/2.98  conjectures:                            4
% 19.12/2.98  epr:                                    5
% 19.12/2.98  horn:                                   28
% 19.12/2.98  ground:                                 4
% 19.12/2.98  unary:                                  14
% 19.12/2.98  binary:                                 8
% 19.12/2.98  lits:                                   48
% 19.12/2.98  lits_eq:                                17
% 19.12/2.98  fd_pure:                                0
% 19.12/2.98  fd_pseudo:                              0
% 19.12/2.98  fd_cond:                                0
% 19.12/2.98  fd_pseudo_cond:                         1
% 19.12/2.98  ac_symbols:                             0
% 19.12/2.98  
% 19.12/2.98  ------ Propositional Solver
% 19.12/2.98  
% 19.12/2.98  prop_solver_calls:                      34
% 19.12/2.98  prop_fast_solver_calls:                 1356
% 19.12/2.98  smt_solver_calls:                       0
% 19.12/2.98  smt_fast_solver_calls:                  0
% 19.12/2.98  prop_num_of_clauses:                    31861
% 19.12/2.98  prop_preprocess_simplified:             46673
% 19.12/2.98  prop_fo_subsumed:                       15
% 19.12/2.98  prop_solver_time:                       0.
% 19.12/2.98  smt_solver_time:                        0.
% 19.12/2.98  smt_fast_solver_time:                   0.
% 19.12/2.98  prop_fast_solver_time:                  0.
% 19.12/2.98  prop_unsat_core_time:                   0.004
% 19.12/2.98  
% 19.12/2.98  ------ QBF
% 19.12/2.98  
% 19.12/2.98  qbf_q_res:                              0
% 19.12/2.98  qbf_num_tautologies:                    0
% 19.12/2.98  qbf_prep_cycles:                        0
% 19.12/2.98  
% 19.12/2.98  ------ BMC1
% 19.12/2.98  
% 19.12/2.98  bmc1_current_bound:                     -1
% 19.12/2.98  bmc1_last_solved_bound:                 -1
% 19.12/2.98  bmc1_unsat_core_size:                   -1
% 19.12/2.98  bmc1_unsat_core_parents_size:           -1
% 19.12/2.98  bmc1_merge_next_fun:                    0
% 19.12/2.98  bmc1_unsat_core_clauses_time:           0.
% 19.12/2.98  
% 19.12/2.98  ------ Instantiation
% 19.12/2.98  
% 19.12/2.98  inst_num_of_clauses:                    7909
% 19.12/2.98  inst_num_in_passive:                    3002
% 19.12/2.98  inst_num_in_active:                     2521
% 19.12/2.98  inst_num_in_unprocessed:                2388
% 19.12/2.98  inst_num_of_loops:                      2720
% 19.12/2.98  inst_num_of_learning_restarts:          0
% 19.12/2.98  inst_num_moves_active_passive:          196
% 19.12/2.98  inst_lit_activity:                      0
% 19.12/2.98  inst_lit_activity_moves:                2
% 19.12/2.98  inst_num_tautologies:                   0
% 19.12/2.98  inst_num_prop_implied:                  0
% 19.12/2.98  inst_num_existing_simplified:           0
% 19.12/2.98  inst_num_eq_res_simplified:             0
% 19.12/2.98  inst_num_child_elim:                    0
% 19.12/2.98  inst_num_of_dismatching_blockings:      7856
% 19.12/2.98  inst_num_of_non_proper_insts:           10212
% 19.12/2.98  inst_num_of_duplicates:                 0
% 19.12/2.98  inst_inst_num_from_inst_to_res:         0
% 19.12/2.98  inst_dismatching_checking_time:         0.
% 19.12/2.98  
% 19.12/2.98  ------ Resolution
% 19.12/2.98  
% 19.12/2.98  res_num_of_clauses:                     0
% 19.12/2.98  res_num_in_passive:                     0
% 19.12/2.98  res_num_in_active:                      0
% 19.12/2.98  res_num_of_loops:                       144
% 19.12/2.98  res_forward_subset_subsumed:            1337
% 19.12/2.98  res_backward_subset_subsumed:           4
% 19.12/2.98  res_forward_subsumed:                   0
% 19.12/2.98  res_backward_subsumed:                  0
% 19.12/2.98  res_forward_subsumption_resolution:     0
% 19.12/2.98  res_backward_subsumption_resolution:    0
% 19.12/2.98  res_clause_to_clause_subsumption:       13777
% 19.12/2.98  res_orphan_elimination:                 0
% 19.12/2.98  res_tautology_del:                      1136
% 19.12/2.98  res_num_eq_res_simplified:              0
% 19.12/2.98  res_num_sel_changes:                    0
% 19.12/2.98  res_moves_from_active_to_pass:          0
% 19.12/2.98  
% 19.12/2.98  ------ Superposition
% 19.12/2.98  
% 19.12/2.98  sup_time_total:                         0.
% 19.12/2.98  sup_time_generating:                    0.
% 19.12/2.98  sup_time_sim_full:                      0.
% 19.12/2.98  sup_time_sim_immed:                     0.
% 19.12/2.98  
% 19.12/2.98  sup_num_of_clauses:                     3015
% 19.12/2.98  sup_num_in_active:                      486
% 19.12/2.98  sup_num_in_passive:                     2529
% 19.12/2.98  sup_num_of_loops:                       542
% 19.12/2.98  sup_fw_superposition:                   2491
% 19.12/2.98  sup_bw_superposition:                   3357
% 19.12/2.98  sup_immediate_simplified:               3138
% 19.12/2.98  sup_given_eliminated:                   14
% 19.12/2.98  comparisons_done:                       0
% 19.12/2.98  comparisons_avoided:                    0
% 19.12/2.98  
% 19.12/2.98  ------ Simplifications
% 19.12/2.98  
% 19.12/2.98  
% 19.12/2.98  sim_fw_subset_subsumed:                 67
% 19.12/2.98  sim_bw_subset_subsumed:                 11
% 19.12/2.98  sim_fw_subsumed:                        569
% 19.12/2.98  sim_bw_subsumed:                        11
% 19.12/2.98  sim_fw_subsumption_res:                 0
% 19.12/2.98  sim_bw_subsumption_res:                 0
% 19.12/2.98  sim_tautology_del:                      29
% 19.12/2.98  sim_eq_tautology_del:                   663
% 19.12/2.98  sim_eq_res_simp:                        9
% 19.12/2.98  sim_fw_demodulated:                     1383
% 19.12/2.98  sim_bw_demodulated:                     130
% 19.12/2.98  sim_light_normalised:                   1713
% 19.12/2.98  sim_joinable_taut:                      0
% 19.12/2.98  sim_joinable_simp:                      0
% 19.12/2.98  sim_ac_normalised:                      0
% 19.12/2.98  sim_smt_subsumption:                    0
% 19.12/2.98  
%------------------------------------------------------------------------------
