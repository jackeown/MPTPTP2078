%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:33 EST 2020

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 218 expanded)
%              Number of clauses        :   53 (  63 expanded)
%              Number of leaves         :   26 (  58 expanded)
%              Depth                    :   22
%              Number of atoms          :  236 ( 353 expanded)
%              Number of equality atoms :  123 ( 219 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f55,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f37,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(rectify,[],[f29])).

fof(f52,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f51,f56])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f62,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f66])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f67])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f68])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f69])).

fof(f74,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f62,f70,f70])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f19,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f20,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f22,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k6_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => k6_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f36,plain,(
    ? [X0] :
      ( k6_yellow_1(k1_xboole_0,X0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f40,plain,
    ( ? [X0] :
        ( k6_yellow_1(k1_xboole_0,X0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
        & l1_orders_2(X0) )
   => ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
    & l1_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f40])).

fof(f63,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f64,f70,f70])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => v1_yellow_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_4,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_426,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_147,plain,
    ( v1_funct_1(X0)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_148,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_147])).

cnf(c_6,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3,plain,
    ( v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_11,plain,
    ( ~ v1_partfun1(X0,k1_xboole_0)
    | ~ v4_relat_1(X0,k1_xboole_0)
    | ~ v1_yellow_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_212,plain,
    ( ~ v1_partfun1(X0,k1_xboole_0)
    | ~ v4_relat_1(X0,k1_xboole_0)
    | ~ v1_yellow_1(X0)
    | ~ v1_funct_1(X0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,X0)
    | k6_partfun1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_213,plain,
    ( ~ v1_partfun1(k6_partfun1(X0),k1_xboole_0)
    | ~ v4_relat_1(k6_partfun1(X0),k1_xboole_0)
    | ~ v1_yellow_1(k6_partfun1(X0))
    | ~ v1_funct_1(k6_partfun1(X0))
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0)) ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_239,plain,
    ( ~ v1_partfun1(k6_partfun1(X0),k1_xboole_0)
    | ~ v1_yellow_1(k6_partfun1(X0))
    | ~ v1_funct_1(k6_partfun1(X0))
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0))
    | k6_partfun1(X0) != k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_213])).

cnf(c_240,plain,
    ( ~ v1_partfun1(k6_partfun1(X0),k1_xboole_0)
    | ~ v1_yellow_1(k6_partfun1(X0))
    | ~ v1_funct_1(k6_partfun1(X0))
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0))
    | k6_partfun1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_266,plain,
    ( ~ v1_yellow_1(k6_partfun1(X0))
    | ~ v1_funct_1(k6_partfun1(X0))
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0))
    | k6_partfun1(X0) != k6_partfun1(X1)
    | k6_partfun1(X0) != k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_240])).

cnf(c_267,plain,
    ( ~ v1_yellow_1(k6_partfun1(X0))
    | ~ v1_funct_1(k6_partfun1(X0))
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0))
    | k6_partfun1(X0) != k6_partfun1(k1_xboole_0)
    | k6_partfun1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_293,plain,
    ( ~ v1_yellow_1(k6_partfun1(X0))
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0))
    | k6_partfun1(X0) != k6_partfun1(k1_xboole_0)
    | k6_partfun1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_148,c_267])).

cnf(c_419,plain,
    ( ~ v1_yellow_1(k6_partfun1(X0_44))
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0_44))
    | k6_partfun1(X0_44) != k6_partfun1(k1_xboole_0)
    | k6_partfun1(X0_44) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_293])).

cnf(c_511,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0_44))
    | k6_partfun1(X0_44) != k6_partfun1(k1_xboole_0)
    | k6_partfun1(X0_44) != k1_xboole_0
    | v1_yellow_1(k6_partfun1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_526,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0_44))
    | k6_partfun1(X0_44) != k1_xboole_0
    | v1_yellow_1(k6_partfun1(X0_44)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_511,c_426])).

cnf(c_683,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(k1_xboole_0))
    | v1_yellow_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_426,c_526])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10,plain,
    ( v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_165,plain,
    ( k2_funcop_1(k1_xboole_0,X0) != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_166,plain,
    ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) ),
    inference(unflattening,[status(thm)],[c_165])).

cnf(c_424,plain,
    ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0_46) ),
    inference(subtyping,[status(esa)],[c_166])).

cnf(c_8,plain,
    ( ~ l1_orders_2(X0)
    | k5_yellow_1(X1,k2_funcop_1(X1,X0)) = k6_yellow_1(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_13,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_200,plain,
    ( k5_yellow_1(X0,k2_funcop_1(X0,X1)) = k6_yellow_1(X0,X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_201,plain,
    ( k5_yellow_1(X0,k2_funcop_1(X0,sK1)) = k6_yellow_1(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_420,plain,
    ( k5_yellow_1(X0_44,k2_funcop_1(X0_44,sK1)) = k6_yellow_1(X0_44,sK1) ),
    inference(subtyping,[status(esa)],[c_201])).

cnf(c_594,plain,
    ( k5_yellow_1(k1_xboole_0,k1_xboole_0) = k6_yellow_1(k1_xboole_0,sK1) ),
    inference(superposition,[status(thm)],[c_424,c_420])).

cnf(c_684,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK1)
    | v1_yellow_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_683,c_426,c_594])).

cnf(c_431,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_549,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != X0_45
    | k6_yellow_1(k1_xboole_0,sK1) != X0_45
    | k6_yellow_1(k1_xboole_0,sK1) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_559,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK1)
    | k6_yellow_1(k1_xboole_0,sK1) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | k6_yellow_1(k1_xboole_0,sK1) != k6_yellow_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_436,plain,
    ( ~ v1_yellow_1(X0_44)
    | v1_yellow_1(X1_44)
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_544,plain,
    ( v1_yellow_1(X0_44)
    | ~ v1_yellow_1(k2_funcop_1(X1_44,sK1))
    | X0_44 != k2_funcop_1(X1_44,sK1) ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_545,plain,
    ( X0_44 != k2_funcop_1(X1_44,sK1)
    | v1_yellow_1(X0_44) = iProver_top
    | v1_yellow_1(k2_funcop_1(X1_44,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_547,plain,
    ( k1_xboole_0 != k2_funcop_1(k1_xboole_0,sK1)
    | v1_yellow_1(k2_funcop_1(k1_xboole_0,sK1)) != iProver_top
    | v1_yellow_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_449,plain,
    ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_424])).

cnf(c_12,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_425,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_428,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_447,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_428])).

cnf(c_433,plain,
    ( k6_yellow_1(X0_44,X0_46) = k6_yellow_1(X1_44,X0_46)
    | X0_44 != X1_44 ),
    theory(equality)).

cnf(c_440,plain,
    ( k6_yellow_1(k1_xboole_0,sK1) = k6_yellow_1(k1_xboole_0,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(c_9,plain,
    ( v1_yellow_1(k2_funcop_1(X0,X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_191,plain,
    ( v1_yellow_1(k2_funcop_1(X0,X1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_192,plain,
    ( v1_yellow_1(k2_funcop_1(X0,sK1)) ),
    inference(unflattening,[status(thm)],[c_191])).

cnf(c_193,plain,
    ( v1_yellow_1(k2_funcop_1(X0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_195,plain,
    ( v1_yellow_1(k2_funcop_1(k1_xboole_0,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_684,c_559,c_547,c_449,c_425,c_447,c_440,c_195])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:41:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.07/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.07/1.00  
% 1.07/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.07/1.00  
% 1.07/1.00  ------  iProver source info
% 1.07/1.00  
% 1.07/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.07/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.07/1.00  git: non_committed_changes: false
% 1.07/1.00  git: last_make_outside_of_git: false
% 1.07/1.00  
% 1.07/1.00  ------ 
% 1.07/1.00  
% 1.07/1.00  ------ Input Options
% 1.07/1.00  
% 1.07/1.00  --out_options                           all
% 1.07/1.00  --tptp_safe_out                         true
% 1.07/1.00  --problem_path                          ""
% 1.07/1.00  --include_path                          ""
% 1.07/1.00  --clausifier                            res/vclausify_rel
% 1.07/1.00  --clausifier_options                    --mode clausify
% 1.07/1.00  --stdin                                 false
% 1.07/1.00  --stats_out                             all
% 1.07/1.00  
% 1.07/1.00  ------ General Options
% 1.07/1.00  
% 1.07/1.00  --fof                                   false
% 1.07/1.00  --time_out_real                         305.
% 1.07/1.00  --time_out_virtual                      -1.
% 1.07/1.00  --symbol_type_check                     false
% 1.07/1.00  --clausify_out                          false
% 1.07/1.00  --sig_cnt_out                           false
% 1.07/1.00  --trig_cnt_out                          false
% 1.07/1.00  --trig_cnt_out_tolerance                1.
% 1.07/1.00  --trig_cnt_out_sk_spl                   false
% 1.07/1.00  --abstr_cl_out                          false
% 1.07/1.00  
% 1.07/1.00  ------ Global Options
% 1.07/1.00  
% 1.07/1.00  --schedule                              default
% 1.07/1.00  --add_important_lit                     false
% 1.07/1.00  --prop_solver_per_cl                    1000
% 1.07/1.00  --min_unsat_core                        false
% 1.07/1.00  --soft_assumptions                      false
% 1.07/1.00  --soft_lemma_size                       3
% 1.07/1.00  --prop_impl_unit_size                   0
% 1.07/1.00  --prop_impl_unit                        []
% 1.07/1.00  --share_sel_clauses                     true
% 1.07/1.00  --reset_solvers                         false
% 1.07/1.00  --bc_imp_inh                            [conj_cone]
% 1.07/1.00  --conj_cone_tolerance                   3.
% 1.07/1.00  --extra_neg_conj                        none
% 1.07/1.00  --large_theory_mode                     true
% 1.07/1.00  --prolific_symb_bound                   200
% 1.07/1.00  --lt_threshold                          2000
% 1.07/1.00  --clause_weak_htbl                      true
% 1.07/1.00  --gc_record_bc_elim                     false
% 1.07/1.00  
% 1.07/1.00  ------ Preprocessing Options
% 1.07/1.00  
% 1.07/1.00  --preprocessing_flag                    true
% 1.07/1.00  --time_out_prep_mult                    0.1
% 1.07/1.00  --splitting_mode                        input
% 1.07/1.00  --splitting_grd                         true
% 1.07/1.00  --splitting_cvd                         false
% 1.07/1.00  --splitting_cvd_svl                     false
% 1.07/1.00  --splitting_nvd                         32
% 1.07/1.00  --sub_typing                            true
% 1.07/1.00  --prep_gs_sim                           true
% 1.07/1.00  --prep_unflatten                        true
% 1.07/1.00  --prep_res_sim                          true
% 1.07/1.00  --prep_upred                            true
% 1.07/1.00  --prep_sem_filter                       exhaustive
% 1.07/1.00  --prep_sem_filter_out                   false
% 1.07/1.00  --pred_elim                             true
% 1.07/1.00  --res_sim_input                         true
% 1.07/1.00  --eq_ax_congr_red                       true
% 1.07/1.00  --pure_diseq_elim                       true
% 1.07/1.00  --brand_transform                       false
% 1.07/1.00  --non_eq_to_eq                          false
% 1.07/1.00  --prep_def_merge                        true
% 1.07/1.00  --prep_def_merge_prop_impl              false
% 1.07/1.00  --prep_def_merge_mbd                    true
% 1.07/1.00  --prep_def_merge_tr_red                 false
% 1.07/1.00  --prep_def_merge_tr_cl                  false
% 1.07/1.00  --smt_preprocessing                     true
% 1.07/1.00  --smt_ac_axioms                         fast
% 1.07/1.00  --preprocessed_out                      false
% 1.07/1.00  --preprocessed_stats                    false
% 1.07/1.00  
% 1.07/1.00  ------ Abstraction refinement Options
% 1.07/1.00  
% 1.07/1.00  --abstr_ref                             []
% 1.07/1.00  --abstr_ref_prep                        false
% 1.07/1.00  --abstr_ref_until_sat                   false
% 1.07/1.00  --abstr_ref_sig_restrict                funpre
% 1.07/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.07/1.00  --abstr_ref_under                       []
% 1.07/1.00  
% 1.07/1.00  ------ SAT Options
% 1.07/1.00  
% 1.07/1.00  --sat_mode                              false
% 1.07/1.00  --sat_fm_restart_options                ""
% 1.07/1.00  --sat_gr_def                            false
% 1.07/1.00  --sat_epr_types                         true
% 1.07/1.00  --sat_non_cyclic_types                  false
% 1.07/1.00  --sat_finite_models                     false
% 1.07/1.00  --sat_fm_lemmas                         false
% 1.07/1.00  --sat_fm_prep                           false
% 1.07/1.00  --sat_fm_uc_incr                        true
% 1.07/1.00  --sat_out_model                         small
% 1.07/1.00  --sat_out_clauses                       false
% 1.07/1.00  
% 1.07/1.00  ------ QBF Options
% 1.07/1.00  
% 1.07/1.00  --qbf_mode                              false
% 1.07/1.00  --qbf_elim_univ                         false
% 1.07/1.00  --qbf_dom_inst                          none
% 1.07/1.00  --qbf_dom_pre_inst                      false
% 1.07/1.00  --qbf_sk_in                             false
% 1.07/1.00  --qbf_pred_elim                         true
% 1.07/1.00  --qbf_split                             512
% 1.07/1.00  
% 1.07/1.00  ------ BMC1 Options
% 1.07/1.00  
% 1.07/1.00  --bmc1_incremental                      false
% 1.07/1.00  --bmc1_axioms                           reachable_all
% 1.07/1.00  --bmc1_min_bound                        0
% 1.07/1.00  --bmc1_max_bound                        -1
% 1.07/1.00  --bmc1_max_bound_default                -1
% 1.07/1.00  --bmc1_symbol_reachability              true
% 1.07/1.00  --bmc1_property_lemmas                  false
% 1.07/1.00  --bmc1_k_induction                      false
% 1.07/1.00  --bmc1_non_equiv_states                 false
% 1.07/1.00  --bmc1_deadlock                         false
% 1.07/1.00  --bmc1_ucm                              false
% 1.07/1.00  --bmc1_add_unsat_core                   none
% 1.07/1.00  --bmc1_unsat_core_children              false
% 1.07/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.07/1.00  --bmc1_out_stat                         full
% 1.07/1.00  --bmc1_ground_init                      false
% 1.07/1.00  --bmc1_pre_inst_next_state              false
% 1.07/1.00  --bmc1_pre_inst_state                   false
% 1.07/1.00  --bmc1_pre_inst_reach_state             false
% 1.07/1.00  --bmc1_out_unsat_core                   false
% 1.07/1.00  --bmc1_aig_witness_out                  false
% 1.07/1.00  --bmc1_verbose                          false
% 1.07/1.00  --bmc1_dump_clauses_tptp                false
% 1.07/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.07/1.00  --bmc1_dump_file                        -
% 1.07/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.07/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.07/1.00  --bmc1_ucm_extend_mode                  1
% 1.07/1.00  --bmc1_ucm_init_mode                    2
% 1.07/1.00  --bmc1_ucm_cone_mode                    none
% 1.07/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.07/1.00  --bmc1_ucm_relax_model                  4
% 1.07/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.07/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.07/1.00  --bmc1_ucm_layered_model                none
% 1.07/1.00  --bmc1_ucm_max_lemma_size               10
% 1.07/1.00  
% 1.07/1.00  ------ AIG Options
% 1.07/1.00  
% 1.07/1.00  --aig_mode                              false
% 1.07/1.00  
% 1.07/1.00  ------ Instantiation Options
% 1.07/1.00  
% 1.07/1.00  --instantiation_flag                    true
% 1.07/1.00  --inst_sos_flag                         false
% 1.07/1.00  --inst_sos_phase                        true
% 1.07/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.07/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.07/1.00  --inst_lit_sel_side                     num_symb
% 1.07/1.00  --inst_solver_per_active                1400
% 1.07/1.00  --inst_solver_calls_frac                1.
% 1.07/1.00  --inst_passive_queue_type               priority_queues
% 1.07/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.07/1.00  --inst_passive_queues_freq              [25;2]
% 1.07/1.00  --inst_dismatching                      true
% 1.07/1.00  --inst_eager_unprocessed_to_passive     true
% 1.07/1.00  --inst_prop_sim_given                   true
% 1.07/1.00  --inst_prop_sim_new                     false
% 1.07/1.00  --inst_subs_new                         false
% 1.07/1.00  --inst_eq_res_simp                      false
% 1.07/1.00  --inst_subs_given                       false
% 1.07/1.00  --inst_orphan_elimination               true
% 1.07/1.00  --inst_learning_loop_flag               true
% 1.07/1.00  --inst_learning_start                   3000
% 1.07/1.00  --inst_learning_factor                  2
% 1.07/1.00  --inst_start_prop_sim_after_learn       3
% 1.07/1.00  --inst_sel_renew                        solver
% 1.07/1.00  --inst_lit_activity_flag                true
% 1.07/1.00  --inst_restr_to_given                   false
% 1.07/1.00  --inst_activity_threshold               500
% 1.07/1.00  --inst_out_proof                        true
% 1.07/1.00  
% 1.07/1.00  ------ Resolution Options
% 1.07/1.00  
% 1.07/1.00  --resolution_flag                       true
% 1.07/1.00  --res_lit_sel                           adaptive
% 1.07/1.00  --res_lit_sel_side                      none
% 1.07/1.00  --res_ordering                          kbo
% 1.07/1.00  --res_to_prop_solver                    active
% 1.07/1.00  --res_prop_simpl_new                    false
% 1.07/1.00  --res_prop_simpl_given                  true
% 1.07/1.00  --res_passive_queue_type                priority_queues
% 1.07/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.07/1.00  --res_passive_queues_freq               [15;5]
% 1.07/1.00  --res_forward_subs                      full
% 1.07/1.00  --res_backward_subs                     full
% 1.07/1.00  --res_forward_subs_resolution           true
% 1.07/1.00  --res_backward_subs_resolution          true
% 1.07/1.00  --res_orphan_elimination                true
% 1.07/1.00  --res_time_limit                        2.
% 1.07/1.00  --res_out_proof                         true
% 1.07/1.00  
% 1.07/1.00  ------ Superposition Options
% 1.07/1.00  
% 1.07/1.00  --superposition_flag                    true
% 1.07/1.00  --sup_passive_queue_type                priority_queues
% 1.07/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.07/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.07/1.00  --demod_completeness_check              fast
% 1.07/1.00  --demod_use_ground                      true
% 1.07/1.00  --sup_to_prop_solver                    passive
% 1.07/1.00  --sup_prop_simpl_new                    true
% 1.07/1.00  --sup_prop_simpl_given                  true
% 1.07/1.00  --sup_fun_splitting                     false
% 1.07/1.00  --sup_smt_interval                      50000
% 1.07/1.00  
% 1.07/1.00  ------ Superposition Simplification Setup
% 1.07/1.00  
% 1.07/1.00  --sup_indices_passive                   []
% 1.07/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.07/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.00  --sup_full_bw                           [BwDemod]
% 1.07/1.00  --sup_immed_triv                        [TrivRules]
% 1.07/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.07/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.00  --sup_immed_bw_main                     []
% 1.07/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.07/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.00  
% 1.07/1.00  ------ Combination Options
% 1.07/1.00  
% 1.07/1.00  --comb_res_mult                         3
% 1.07/1.00  --comb_sup_mult                         2
% 1.07/1.00  --comb_inst_mult                        10
% 1.07/1.00  
% 1.07/1.00  ------ Debug Options
% 1.07/1.00  
% 1.07/1.00  --dbg_backtrace                         false
% 1.07/1.00  --dbg_dump_prop_clauses                 false
% 1.07/1.00  --dbg_dump_prop_clauses_file            -
% 1.07/1.00  --dbg_out_stat                          false
% 1.07/1.00  ------ Parsing...
% 1.07/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.07/1.00  
% 1.07/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.07/1.00  
% 1.07/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.07/1.00  
% 1.07/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.07/1.00  ------ Proving...
% 1.07/1.00  ------ Problem Properties 
% 1.07/1.00  
% 1.07/1.00  
% 1.07/1.00  clauses                                 8
% 1.07/1.00  conjectures                             1
% 1.07/1.00  EPR                                     0
% 1.07/1.00  Horn                                    8
% 1.07/1.00  unary                                   7
% 1.07/1.00  binary                                  0
% 1.07/1.00  lits                                    11
% 1.07/1.00  lits eq                                 8
% 1.07/1.00  fd_pure                                 0
% 1.07/1.00  fd_pseudo                               0
% 1.07/1.00  fd_cond                                 0
% 1.07/1.00  fd_pseudo_cond                          0
% 1.07/1.00  AC symbols                              0
% 1.07/1.00  
% 1.07/1.00  ------ Schedule dynamic 5 is on 
% 1.07/1.00  
% 1.07/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.07/1.00  
% 1.07/1.00  
% 1.07/1.00  ------ 
% 1.07/1.00  Current options:
% 1.07/1.00  ------ 
% 1.07/1.00  
% 1.07/1.00  ------ Input Options
% 1.07/1.00  
% 1.07/1.00  --out_options                           all
% 1.07/1.00  --tptp_safe_out                         true
% 1.07/1.00  --problem_path                          ""
% 1.07/1.00  --include_path                          ""
% 1.07/1.00  --clausifier                            res/vclausify_rel
% 1.07/1.00  --clausifier_options                    --mode clausify
% 1.07/1.00  --stdin                                 false
% 1.07/1.00  --stats_out                             all
% 1.07/1.00  
% 1.07/1.00  ------ General Options
% 1.07/1.00  
% 1.07/1.00  --fof                                   false
% 1.07/1.00  --time_out_real                         305.
% 1.07/1.00  --time_out_virtual                      -1.
% 1.07/1.00  --symbol_type_check                     false
% 1.07/1.00  --clausify_out                          false
% 1.07/1.00  --sig_cnt_out                           false
% 1.07/1.00  --trig_cnt_out                          false
% 1.07/1.00  --trig_cnt_out_tolerance                1.
% 1.07/1.00  --trig_cnt_out_sk_spl                   false
% 1.07/1.00  --abstr_cl_out                          false
% 1.07/1.00  
% 1.07/1.00  ------ Global Options
% 1.07/1.00  
% 1.07/1.00  --schedule                              default
% 1.07/1.00  --add_important_lit                     false
% 1.07/1.00  --prop_solver_per_cl                    1000
% 1.07/1.00  --min_unsat_core                        false
% 1.07/1.00  --soft_assumptions                      false
% 1.07/1.00  --soft_lemma_size                       3
% 1.07/1.00  --prop_impl_unit_size                   0
% 1.07/1.00  --prop_impl_unit                        []
% 1.07/1.00  --share_sel_clauses                     true
% 1.07/1.00  --reset_solvers                         false
% 1.07/1.00  --bc_imp_inh                            [conj_cone]
% 1.07/1.00  --conj_cone_tolerance                   3.
% 1.07/1.00  --extra_neg_conj                        none
% 1.07/1.00  --large_theory_mode                     true
% 1.07/1.00  --prolific_symb_bound                   200
% 1.07/1.00  --lt_threshold                          2000
% 1.07/1.00  --clause_weak_htbl                      true
% 1.07/1.00  --gc_record_bc_elim                     false
% 1.07/1.00  
% 1.07/1.00  ------ Preprocessing Options
% 1.07/1.00  
% 1.07/1.00  --preprocessing_flag                    true
% 1.07/1.00  --time_out_prep_mult                    0.1
% 1.07/1.00  --splitting_mode                        input
% 1.07/1.00  --splitting_grd                         true
% 1.07/1.00  --splitting_cvd                         false
% 1.07/1.00  --splitting_cvd_svl                     false
% 1.07/1.00  --splitting_nvd                         32
% 1.07/1.00  --sub_typing                            true
% 1.07/1.00  --prep_gs_sim                           true
% 1.07/1.00  --prep_unflatten                        true
% 1.07/1.00  --prep_res_sim                          true
% 1.07/1.00  --prep_upred                            true
% 1.07/1.00  --prep_sem_filter                       exhaustive
% 1.07/1.00  --prep_sem_filter_out                   false
% 1.07/1.00  --pred_elim                             true
% 1.07/1.00  --res_sim_input                         true
% 1.07/1.00  --eq_ax_congr_red                       true
% 1.07/1.00  --pure_diseq_elim                       true
% 1.07/1.00  --brand_transform                       false
% 1.07/1.00  --non_eq_to_eq                          false
% 1.07/1.00  --prep_def_merge                        true
% 1.07/1.00  --prep_def_merge_prop_impl              false
% 1.07/1.00  --prep_def_merge_mbd                    true
% 1.07/1.00  --prep_def_merge_tr_red                 false
% 1.07/1.00  --prep_def_merge_tr_cl                  false
% 1.07/1.00  --smt_preprocessing                     true
% 1.07/1.00  --smt_ac_axioms                         fast
% 1.07/1.00  --preprocessed_out                      false
% 1.07/1.00  --preprocessed_stats                    false
% 1.07/1.00  
% 1.07/1.00  ------ Abstraction refinement Options
% 1.07/1.00  
% 1.07/1.00  --abstr_ref                             []
% 1.07/1.00  --abstr_ref_prep                        false
% 1.07/1.00  --abstr_ref_until_sat                   false
% 1.07/1.00  --abstr_ref_sig_restrict                funpre
% 1.07/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.07/1.00  --abstr_ref_under                       []
% 1.07/1.00  
% 1.07/1.00  ------ SAT Options
% 1.07/1.00  
% 1.07/1.00  --sat_mode                              false
% 1.07/1.00  --sat_fm_restart_options                ""
% 1.07/1.00  --sat_gr_def                            false
% 1.07/1.00  --sat_epr_types                         true
% 1.07/1.00  --sat_non_cyclic_types                  false
% 1.07/1.00  --sat_finite_models                     false
% 1.07/1.00  --sat_fm_lemmas                         false
% 1.07/1.00  --sat_fm_prep                           false
% 1.07/1.00  --sat_fm_uc_incr                        true
% 1.07/1.00  --sat_out_model                         small
% 1.07/1.00  --sat_out_clauses                       false
% 1.07/1.00  
% 1.07/1.00  ------ QBF Options
% 1.07/1.00  
% 1.07/1.00  --qbf_mode                              false
% 1.07/1.00  --qbf_elim_univ                         false
% 1.07/1.00  --qbf_dom_inst                          none
% 1.07/1.00  --qbf_dom_pre_inst                      false
% 1.07/1.00  --qbf_sk_in                             false
% 1.07/1.00  --qbf_pred_elim                         true
% 1.07/1.00  --qbf_split                             512
% 1.07/1.00  
% 1.07/1.00  ------ BMC1 Options
% 1.07/1.00  
% 1.07/1.00  --bmc1_incremental                      false
% 1.07/1.00  --bmc1_axioms                           reachable_all
% 1.07/1.00  --bmc1_min_bound                        0
% 1.07/1.00  --bmc1_max_bound                        -1
% 1.07/1.00  --bmc1_max_bound_default                -1
% 1.07/1.00  --bmc1_symbol_reachability              true
% 1.07/1.00  --bmc1_property_lemmas                  false
% 1.07/1.00  --bmc1_k_induction                      false
% 1.07/1.00  --bmc1_non_equiv_states                 false
% 1.07/1.00  --bmc1_deadlock                         false
% 1.07/1.00  --bmc1_ucm                              false
% 1.07/1.00  --bmc1_add_unsat_core                   none
% 1.07/1.00  --bmc1_unsat_core_children              false
% 1.07/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.07/1.00  --bmc1_out_stat                         full
% 1.07/1.00  --bmc1_ground_init                      false
% 1.07/1.00  --bmc1_pre_inst_next_state              false
% 1.07/1.00  --bmc1_pre_inst_state                   false
% 1.07/1.00  --bmc1_pre_inst_reach_state             false
% 1.07/1.00  --bmc1_out_unsat_core                   false
% 1.07/1.00  --bmc1_aig_witness_out                  false
% 1.07/1.00  --bmc1_verbose                          false
% 1.07/1.00  --bmc1_dump_clauses_tptp                false
% 1.07/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.07/1.00  --bmc1_dump_file                        -
% 1.07/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.07/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.07/1.00  --bmc1_ucm_extend_mode                  1
% 1.07/1.00  --bmc1_ucm_init_mode                    2
% 1.07/1.00  --bmc1_ucm_cone_mode                    none
% 1.07/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.07/1.00  --bmc1_ucm_relax_model                  4
% 1.07/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.07/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.07/1.00  --bmc1_ucm_layered_model                none
% 1.07/1.00  --bmc1_ucm_max_lemma_size               10
% 1.07/1.00  
% 1.07/1.00  ------ AIG Options
% 1.07/1.00  
% 1.07/1.00  --aig_mode                              false
% 1.07/1.00  
% 1.07/1.00  ------ Instantiation Options
% 1.07/1.00  
% 1.07/1.00  --instantiation_flag                    true
% 1.07/1.00  --inst_sos_flag                         false
% 1.07/1.00  --inst_sos_phase                        true
% 1.07/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.07/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.07/1.00  --inst_lit_sel_side                     none
% 1.07/1.00  --inst_solver_per_active                1400
% 1.07/1.00  --inst_solver_calls_frac                1.
% 1.07/1.00  --inst_passive_queue_type               priority_queues
% 1.07/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.07/1.00  --inst_passive_queues_freq              [25;2]
% 1.07/1.00  --inst_dismatching                      true
% 1.07/1.00  --inst_eager_unprocessed_to_passive     true
% 1.07/1.00  --inst_prop_sim_given                   true
% 1.07/1.00  --inst_prop_sim_new                     false
% 1.07/1.00  --inst_subs_new                         false
% 1.07/1.00  --inst_eq_res_simp                      false
% 1.07/1.00  --inst_subs_given                       false
% 1.07/1.00  --inst_orphan_elimination               true
% 1.07/1.00  --inst_learning_loop_flag               true
% 1.07/1.00  --inst_learning_start                   3000
% 1.07/1.00  --inst_learning_factor                  2
% 1.07/1.00  --inst_start_prop_sim_after_learn       3
% 1.07/1.00  --inst_sel_renew                        solver
% 1.07/1.00  --inst_lit_activity_flag                true
% 1.07/1.00  --inst_restr_to_given                   false
% 1.07/1.00  --inst_activity_threshold               500
% 1.07/1.00  --inst_out_proof                        true
% 1.07/1.00  
% 1.07/1.00  ------ Resolution Options
% 1.07/1.00  
% 1.07/1.00  --resolution_flag                       false
% 1.07/1.00  --res_lit_sel                           adaptive
% 1.07/1.00  --res_lit_sel_side                      none
% 1.07/1.00  --res_ordering                          kbo
% 1.07/1.00  --res_to_prop_solver                    active
% 1.07/1.00  --res_prop_simpl_new                    false
% 1.07/1.00  --res_prop_simpl_given                  true
% 1.07/1.00  --res_passive_queue_type                priority_queues
% 1.07/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.07/1.00  --res_passive_queues_freq               [15;5]
% 1.07/1.00  --res_forward_subs                      full
% 1.07/1.00  --res_backward_subs                     full
% 1.07/1.00  --res_forward_subs_resolution           true
% 1.07/1.00  --res_backward_subs_resolution          true
% 1.07/1.00  --res_orphan_elimination                true
% 1.07/1.00  --res_time_limit                        2.
% 1.07/1.00  --res_out_proof                         true
% 1.07/1.00  
% 1.07/1.00  ------ Superposition Options
% 1.07/1.00  
% 1.07/1.00  --superposition_flag                    true
% 1.07/1.00  --sup_passive_queue_type                priority_queues
% 1.07/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.07/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.07/1.00  --demod_completeness_check              fast
% 1.07/1.00  --demod_use_ground                      true
% 1.07/1.00  --sup_to_prop_solver                    passive
% 1.07/1.00  --sup_prop_simpl_new                    true
% 1.07/1.00  --sup_prop_simpl_given                  true
% 1.07/1.00  --sup_fun_splitting                     false
% 1.07/1.00  --sup_smt_interval                      50000
% 1.07/1.00  
% 1.07/1.00  ------ Superposition Simplification Setup
% 1.07/1.00  
% 1.07/1.00  --sup_indices_passive                   []
% 1.07/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.07/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.00  --sup_full_bw                           [BwDemod]
% 1.07/1.00  --sup_immed_triv                        [TrivRules]
% 1.07/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.07/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.00  --sup_immed_bw_main                     []
% 1.07/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.07/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.00  
% 1.07/1.00  ------ Combination Options
% 1.07/1.00  
% 1.07/1.00  --comb_res_mult                         3
% 1.07/1.00  --comb_sup_mult                         2
% 1.07/1.00  --comb_inst_mult                        10
% 1.07/1.00  
% 1.07/1.00  ------ Debug Options
% 1.07/1.00  
% 1.07/1.00  --dbg_backtrace                         false
% 1.07/1.00  --dbg_dump_prop_clauses                 false
% 1.07/1.00  --dbg_dump_prop_clauses_file            -
% 1.07/1.00  --dbg_out_stat                          false
% 1.07/1.00  
% 1.07/1.00  
% 1.07/1.00  
% 1.07/1.00  
% 1.07/1.00  ------ Proving...
% 1.07/1.00  
% 1.07/1.00  
% 1.07/1.00  % SZS status Theorem for theBenchmark.p
% 1.07/1.00  
% 1.07/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.07/1.00  
% 1.07/1.00  fof(f12,axiom,(
% 1.07/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f53,plain,(
% 1.07/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.07/1.00    inference(cnf_transformation,[],[f12])).
% 1.07/1.00  
% 1.07/1.00  fof(f15,axiom,(
% 1.07/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f56,plain,(
% 1.07/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.07/1.00    inference(cnf_transformation,[],[f15])).
% 1.07/1.00  
% 1.07/1.00  fof(f72,plain,(
% 1.07/1.00    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.07/1.00    inference(definition_unfolding,[],[f53,f56])).
% 1.07/1.00  
% 1.07/1.00  fof(f1,axiom,(
% 1.07/1.00    v1_xboole_0(k1_xboole_0)),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f42,plain,(
% 1.07/1.00    v1_xboole_0(k1_xboole_0)),
% 1.07/1.00    inference(cnf_transformation,[],[f1])).
% 1.07/1.00  
% 1.07/1.00  fof(f13,axiom,(
% 1.07/1.00    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f31,plain,(
% 1.07/1.00    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 1.07/1.00    inference(ennf_transformation,[],[f13])).
% 1.07/1.00  
% 1.07/1.00  fof(f54,plain,(
% 1.07/1.00    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 1.07/1.00    inference(cnf_transformation,[],[f31])).
% 1.07/1.00  
% 1.07/1.00  fof(f14,axiom,(
% 1.07/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f28,plain,(
% 1.07/1.00    ! [X0] : v1_partfun1(k6_partfun1(X0),X0)),
% 1.07/1.00    inference(pure_predicate_removal,[],[f14])).
% 1.07/1.00  
% 1.07/1.00  fof(f55,plain,(
% 1.07/1.00    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 1.07/1.00    inference(cnf_transformation,[],[f28])).
% 1.07/1.00  
% 1.07/1.00  fof(f11,axiom,(
% 1.07/1.00    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f29,plain,(
% 1.07/1.00    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0)),
% 1.07/1.00    inference(pure_predicate_removal,[],[f11])).
% 1.07/1.00  
% 1.07/1.00  fof(f37,plain,(
% 1.07/1.00    ! [X0] : v4_relat_1(k1_xboole_0,X0)),
% 1.07/1.00    inference(rectify,[],[f29])).
% 1.07/1.00  
% 1.07/1.00  fof(f52,plain,(
% 1.07/1.00    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 1.07/1.00    inference(cnf_transformation,[],[f37])).
% 1.07/1.00  
% 1.07/1.00  fof(f10,axiom,(
% 1.07/1.00    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f51,plain,(
% 1.07/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.07/1.00    inference(cnf_transformation,[],[f10])).
% 1.07/1.00  
% 1.07/1.00  fof(f71,plain,(
% 1.07/1.00    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 1.07/1.00    inference(definition_unfolding,[],[f51,f56])).
% 1.07/1.00  
% 1.07/1.00  fof(f21,axiom,(
% 1.07/1.00    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f34,plain,(
% 1.07/1.00    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 1.07/1.00    inference(ennf_transformation,[],[f21])).
% 1.07/1.00  
% 1.07/1.00  fof(f35,plain,(
% 1.07/1.00    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.07/1.00    inference(flattening,[],[f34])).
% 1.07/1.00  
% 1.07/1.00  fof(f62,plain,(
% 1.07/1.00    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.07/1.00    inference(cnf_transformation,[],[f35])).
% 1.07/1.00  
% 1.07/1.00  fof(f3,axiom,(
% 1.07/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f44,plain,(
% 1.07/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.07/1.00    inference(cnf_transformation,[],[f3])).
% 1.07/1.00  
% 1.07/1.00  fof(f4,axiom,(
% 1.07/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f45,plain,(
% 1.07/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.07/1.00    inference(cnf_transformation,[],[f4])).
% 1.07/1.00  
% 1.07/1.00  fof(f5,axiom,(
% 1.07/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f46,plain,(
% 1.07/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.07/1.00    inference(cnf_transformation,[],[f5])).
% 1.07/1.00  
% 1.07/1.00  fof(f6,axiom,(
% 1.07/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f47,plain,(
% 1.07/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.07/1.00    inference(cnf_transformation,[],[f6])).
% 1.07/1.00  
% 1.07/1.00  fof(f7,axiom,(
% 1.07/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f48,plain,(
% 1.07/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.07/1.00    inference(cnf_transformation,[],[f7])).
% 1.07/1.00  
% 1.07/1.00  fof(f8,axiom,(
% 1.07/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f49,plain,(
% 1.07/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.07/1.00    inference(cnf_transformation,[],[f8])).
% 1.07/1.00  
% 1.07/1.00  fof(f9,axiom,(
% 1.07/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f50,plain,(
% 1.07/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.07/1.00    inference(cnf_transformation,[],[f9])).
% 1.07/1.00  
% 1.07/1.00  fof(f65,plain,(
% 1.07/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.07/1.00    inference(definition_unfolding,[],[f49,f50])).
% 1.07/1.00  
% 1.07/1.00  fof(f66,plain,(
% 1.07/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.07/1.00    inference(definition_unfolding,[],[f48,f65])).
% 1.07/1.00  
% 1.07/1.00  fof(f67,plain,(
% 1.07/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.07/1.00    inference(definition_unfolding,[],[f47,f66])).
% 1.07/1.00  
% 1.07/1.00  fof(f68,plain,(
% 1.07/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.07/1.00    inference(definition_unfolding,[],[f46,f67])).
% 1.07/1.00  
% 1.07/1.00  fof(f69,plain,(
% 1.07/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.07/1.00    inference(definition_unfolding,[],[f45,f68])).
% 1.07/1.00  
% 1.07/1.00  fof(f70,plain,(
% 1.07/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.07/1.00    inference(definition_unfolding,[],[f44,f69])).
% 1.07/1.00  
% 1.07/1.00  fof(f74,plain,(
% 1.07/1.00    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.07/1.00    inference(definition_unfolding,[],[f62,f70,f70])).
% 1.07/1.00  
% 1.07/1.00  fof(f2,axiom,(
% 1.07/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f30,plain,(
% 1.07/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.07/1.00    inference(ennf_transformation,[],[f2])).
% 1.07/1.00  
% 1.07/1.00  fof(f43,plain,(
% 1.07/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.07/1.00    inference(cnf_transformation,[],[f30])).
% 1.07/1.00  
% 1.07/1.00  fof(f19,axiom,(
% 1.07/1.00    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f60,plain,(
% 1.07/1.00    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 1.07/1.00    inference(cnf_transformation,[],[f19])).
% 1.07/1.00  
% 1.07/1.00  fof(f17,axiom,(
% 1.07/1.00    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f32,plain,(
% 1.07/1.00    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 1.07/1.00    inference(ennf_transformation,[],[f17])).
% 1.07/1.00  
% 1.07/1.00  fof(f58,plain,(
% 1.07/1.00    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 1.07/1.00    inference(cnf_transformation,[],[f32])).
% 1.07/1.00  
% 1.07/1.00  fof(f20,axiom,(
% 1.07/1.00    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f61,plain,(
% 1.07/1.00    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 1.07/1.00    inference(cnf_transformation,[],[f20])).
% 1.07/1.00  
% 1.07/1.00  fof(f73,plain,(
% 1.07/1.00    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 1.07/1.00    inference(definition_unfolding,[],[f58,f61])).
% 1.07/1.00  
% 1.07/1.00  fof(f22,conjecture,(
% 1.07/1.00    ! [X0] : (l1_orders_2(X0) => k6_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f23,negated_conjecture,(
% 1.07/1.00    ~! [X0] : (l1_orders_2(X0) => k6_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 1.07/1.00    inference(negated_conjecture,[],[f22])).
% 1.07/1.00  
% 1.07/1.00  fof(f36,plain,(
% 1.07/1.00    ? [X0] : (k6_yellow_1(k1_xboole_0,X0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) & l1_orders_2(X0))),
% 1.07/1.00    inference(ennf_transformation,[],[f23])).
% 1.07/1.00  
% 1.07/1.00  fof(f40,plain,(
% 1.07/1.00    ? [X0] : (k6_yellow_1(k1_xboole_0,X0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) & l1_orders_2(X0)) => (k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) & l1_orders_2(sK1))),
% 1.07/1.00    introduced(choice_axiom,[])).
% 1.07/1.00  
% 1.07/1.00  fof(f41,plain,(
% 1.07/1.00    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) & l1_orders_2(sK1)),
% 1.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f40])).
% 1.07/1.00  
% 1.07/1.00  fof(f63,plain,(
% 1.07/1.00    l1_orders_2(sK1)),
% 1.07/1.00    inference(cnf_transformation,[],[f41])).
% 1.07/1.00  
% 1.07/1.00  fof(f64,plain,(
% 1.07/1.00    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))),
% 1.07/1.00    inference(cnf_transformation,[],[f41])).
% 1.07/1.00  
% 1.07/1.00  fof(f75,plain,(
% 1.07/1.00    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 1.07/1.00    inference(definition_unfolding,[],[f64,f70,f70])).
% 1.07/1.00  
% 1.07/1.00  fof(f18,axiom,(
% 1.07/1.00    ! [X0,X1] : (l1_orders_2(X1) => v1_yellow_1(k2_funcop_1(X0,X1)))),
% 1.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.00  
% 1.07/1.00  fof(f33,plain,(
% 1.07/1.00    ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 1.07/1.00    inference(ennf_transformation,[],[f18])).
% 1.07/1.00  
% 1.07/1.00  fof(f59,plain,(
% 1.07/1.00    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 1.07/1.00    inference(cnf_transformation,[],[f33])).
% 1.07/1.00  
% 1.07/1.00  cnf(c_4,plain,
% 1.07/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 1.07/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_426,plain,
% 1.07/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 1.07/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_0,plain,
% 1.07/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 1.07/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_5,plain,
% 1.07/1.00      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 1.07/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_147,plain,
% 1.07/1.00      ( v1_funct_1(X0) | k1_xboole_0 != X0 ),
% 1.07/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_5]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_148,plain,
% 1.07/1.00      ( v1_funct_1(k1_xboole_0) ),
% 1.07/1.00      inference(unflattening,[status(thm)],[c_147]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_6,plain,
% 1.07/1.00      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 1.07/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_3,plain,
% 1.07/1.00      ( v4_relat_1(k1_xboole_0,X0) ),
% 1.07/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_2,plain,
% 1.07/1.00      ( v1_relat_1(k6_partfun1(X0)) ),
% 1.07/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_11,plain,
% 1.07/1.00      ( ~ v1_partfun1(X0,k1_xboole_0)
% 1.07/1.00      | ~ v4_relat_1(X0,k1_xboole_0)
% 1.07/1.00      | ~ v1_yellow_1(X0)
% 1.07/1.00      | ~ v1_funct_1(X0)
% 1.07/1.00      | ~ v1_relat_1(X0)
% 1.07/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,X0) ),
% 1.07/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_212,plain,
% 1.07/1.00      ( ~ v1_partfun1(X0,k1_xboole_0)
% 1.07/1.00      | ~ v4_relat_1(X0,k1_xboole_0)
% 1.07/1.00      | ~ v1_yellow_1(X0)
% 1.07/1.00      | ~ v1_funct_1(X0)
% 1.07/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,X0)
% 1.07/1.00      | k6_partfun1(X1) != X0 ),
% 1.07/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_213,plain,
% 1.07/1.00      ( ~ v1_partfun1(k6_partfun1(X0),k1_xboole_0)
% 1.07/1.00      | ~ v4_relat_1(k6_partfun1(X0),k1_xboole_0)
% 1.07/1.00      | ~ v1_yellow_1(k6_partfun1(X0))
% 1.07/1.00      | ~ v1_funct_1(k6_partfun1(X0))
% 1.07/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0)) ),
% 1.07/1.00      inference(unflattening,[status(thm)],[c_212]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_239,plain,
% 1.07/1.00      ( ~ v1_partfun1(k6_partfun1(X0),k1_xboole_0)
% 1.07/1.00      | ~ v1_yellow_1(k6_partfun1(X0))
% 1.07/1.00      | ~ v1_funct_1(k6_partfun1(X0))
% 1.07/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0))
% 1.07/1.00      | k6_partfun1(X0) != k1_xboole_0
% 1.07/1.00      | k1_xboole_0 != X1 ),
% 1.07/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_213]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_240,plain,
% 1.07/1.00      ( ~ v1_partfun1(k6_partfun1(X0),k1_xboole_0)
% 1.07/1.00      | ~ v1_yellow_1(k6_partfun1(X0))
% 1.07/1.00      | ~ v1_funct_1(k6_partfun1(X0))
% 1.07/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0))
% 1.07/1.00      | k6_partfun1(X0) != k1_xboole_0 ),
% 1.07/1.00      inference(unflattening,[status(thm)],[c_239]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_266,plain,
% 1.07/1.00      ( ~ v1_yellow_1(k6_partfun1(X0))
% 1.07/1.00      | ~ v1_funct_1(k6_partfun1(X0))
% 1.07/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0))
% 1.07/1.00      | k6_partfun1(X0) != k6_partfun1(X1)
% 1.07/1.00      | k6_partfun1(X0) != k1_xboole_0
% 1.07/1.00      | k1_xboole_0 != X1 ),
% 1.07/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_240]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_267,plain,
% 1.07/1.00      ( ~ v1_yellow_1(k6_partfun1(X0))
% 1.07/1.00      | ~ v1_funct_1(k6_partfun1(X0))
% 1.07/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0))
% 1.07/1.00      | k6_partfun1(X0) != k6_partfun1(k1_xboole_0)
% 1.07/1.00      | k6_partfun1(X0) != k1_xboole_0 ),
% 1.07/1.00      inference(unflattening,[status(thm)],[c_266]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_293,plain,
% 1.07/1.00      ( ~ v1_yellow_1(k6_partfun1(X0))
% 1.07/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0))
% 1.07/1.00      | k6_partfun1(X0) != k6_partfun1(k1_xboole_0)
% 1.07/1.00      | k6_partfun1(X0) != k1_xboole_0 ),
% 1.07/1.00      inference(resolution_lifted,[status(thm)],[c_148,c_267]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_419,plain,
% 1.07/1.00      ( ~ v1_yellow_1(k6_partfun1(X0_44))
% 1.07/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0_44))
% 1.07/1.00      | k6_partfun1(X0_44) != k6_partfun1(k1_xboole_0)
% 1.07/1.00      | k6_partfun1(X0_44) != k1_xboole_0 ),
% 1.07/1.00      inference(subtyping,[status(esa)],[c_293]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_511,plain,
% 1.07/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0_44))
% 1.07/1.00      | k6_partfun1(X0_44) != k6_partfun1(k1_xboole_0)
% 1.07/1.00      | k6_partfun1(X0_44) != k1_xboole_0
% 1.07/1.00      | v1_yellow_1(k6_partfun1(X0_44)) != iProver_top ),
% 1.07/1.00      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_526,plain,
% 1.07/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0_44))
% 1.07/1.00      | k6_partfun1(X0_44) != k1_xboole_0
% 1.07/1.00      | v1_yellow_1(k6_partfun1(X0_44)) != iProver_top ),
% 1.07/1.00      inference(light_normalisation,[status(thm)],[c_511,c_426]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_683,plain,
% 1.07/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(k1_xboole_0))
% 1.07/1.00      | v1_yellow_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 1.07/1.00      inference(superposition,[status(thm)],[c_426,c_526]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_1,plain,
% 1.07/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.07/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_10,plain,
% 1.07/1.00      ( v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
% 1.07/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_165,plain,
% 1.07/1.00      ( k2_funcop_1(k1_xboole_0,X0) != X1 | k1_xboole_0 = X1 ),
% 1.07/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_10]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_166,plain,
% 1.07/1.00      ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) ),
% 1.07/1.00      inference(unflattening,[status(thm)],[c_165]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_424,plain,
% 1.07/1.00      ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0_46) ),
% 1.07/1.00      inference(subtyping,[status(esa)],[c_166]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_8,plain,
% 1.07/1.00      ( ~ l1_orders_2(X0)
% 1.07/1.00      | k5_yellow_1(X1,k2_funcop_1(X1,X0)) = k6_yellow_1(X1,X0) ),
% 1.07/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_13,negated_conjecture,
% 1.07/1.00      ( l1_orders_2(sK1) ),
% 1.07/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_200,plain,
% 1.07/1.00      ( k5_yellow_1(X0,k2_funcop_1(X0,X1)) = k6_yellow_1(X0,X1)
% 1.07/1.00      | sK1 != X1 ),
% 1.07/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_201,plain,
% 1.07/1.00      ( k5_yellow_1(X0,k2_funcop_1(X0,sK1)) = k6_yellow_1(X0,sK1) ),
% 1.07/1.00      inference(unflattening,[status(thm)],[c_200]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_420,plain,
% 1.07/1.00      ( k5_yellow_1(X0_44,k2_funcop_1(X0_44,sK1)) = k6_yellow_1(X0_44,sK1) ),
% 1.07/1.00      inference(subtyping,[status(esa)],[c_201]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_594,plain,
% 1.07/1.00      ( k5_yellow_1(k1_xboole_0,k1_xboole_0) = k6_yellow_1(k1_xboole_0,sK1) ),
% 1.07/1.00      inference(superposition,[status(thm)],[c_424,c_420]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_684,plain,
% 1.07/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK1)
% 1.07/1.00      | v1_yellow_1(k1_xboole_0) != iProver_top ),
% 1.07/1.00      inference(light_normalisation,[status(thm)],[c_683,c_426,c_594]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_431,plain,
% 1.07/1.00      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 1.07/1.00      theory(equality) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_549,plain,
% 1.07/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != X0_45
% 1.07/1.00      | k6_yellow_1(k1_xboole_0,sK1) != X0_45
% 1.07/1.00      | k6_yellow_1(k1_xboole_0,sK1) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
% 1.07/1.00      inference(instantiation,[status(thm)],[c_431]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_559,plain,
% 1.07/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK1)
% 1.07/1.00      | k6_yellow_1(k1_xboole_0,sK1) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
% 1.07/1.00      | k6_yellow_1(k1_xboole_0,sK1) != k6_yellow_1(k1_xboole_0,sK1) ),
% 1.07/1.00      inference(instantiation,[status(thm)],[c_549]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_436,plain,
% 1.07/1.00      ( ~ v1_yellow_1(X0_44) | v1_yellow_1(X1_44) | X1_44 != X0_44 ),
% 1.07/1.00      theory(equality) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_544,plain,
% 1.07/1.00      ( v1_yellow_1(X0_44)
% 1.07/1.00      | ~ v1_yellow_1(k2_funcop_1(X1_44,sK1))
% 1.07/1.00      | X0_44 != k2_funcop_1(X1_44,sK1) ),
% 1.07/1.00      inference(instantiation,[status(thm)],[c_436]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_545,plain,
% 1.07/1.00      ( X0_44 != k2_funcop_1(X1_44,sK1)
% 1.07/1.00      | v1_yellow_1(X0_44) = iProver_top
% 1.07/1.00      | v1_yellow_1(k2_funcop_1(X1_44,sK1)) != iProver_top ),
% 1.07/1.00      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_547,plain,
% 1.07/1.00      ( k1_xboole_0 != k2_funcop_1(k1_xboole_0,sK1)
% 1.07/1.00      | v1_yellow_1(k2_funcop_1(k1_xboole_0,sK1)) != iProver_top
% 1.07/1.00      | v1_yellow_1(k1_xboole_0) = iProver_top ),
% 1.07/1.00      inference(instantiation,[status(thm)],[c_545]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_449,plain,
% 1.07/1.00      ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,sK1) ),
% 1.07/1.00      inference(instantiation,[status(thm)],[c_424]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_12,negated_conjecture,
% 1.07/1.00      ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
% 1.07/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_425,negated_conjecture,
% 1.07/1.00      ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
% 1.07/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_428,plain,( X0_44 = X0_44 ),theory(equality) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_447,plain,
% 1.07/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 1.07/1.00      inference(instantiation,[status(thm)],[c_428]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_433,plain,
% 1.07/1.00      ( k6_yellow_1(X0_44,X0_46) = k6_yellow_1(X1_44,X0_46)
% 1.07/1.00      | X0_44 != X1_44 ),
% 1.07/1.00      theory(equality) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_440,plain,
% 1.07/1.00      ( k6_yellow_1(k1_xboole_0,sK1) = k6_yellow_1(k1_xboole_0,sK1)
% 1.07/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.07/1.00      inference(instantiation,[status(thm)],[c_433]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_9,plain,
% 1.07/1.00      ( v1_yellow_1(k2_funcop_1(X0,X1)) | ~ l1_orders_2(X1) ),
% 1.07/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_191,plain,
% 1.07/1.00      ( v1_yellow_1(k2_funcop_1(X0,X1)) | sK1 != X1 ),
% 1.07/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_192,plain,
% 1.07/1.00      ( v1_yellow_1(k2_funcop_1(X0,sK1)) ),
% 1.07/1.00      inference(unflattening,[status(thm)],[c_191]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_193,plain,
% 1.07/1.00      ( v1_yellow_1(k2_funcop_1(X0,sK1)) = iProver_top ),
% 1.07/1.00      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(c_195,plain,
% 1.07/1.00      ( v1_yellow_1(k2_funcop_1(k1_xboole_0,sK1)) = iProver_top ),
% 1.07/1.00      inference(instantiation,[status(thm)],[c_193]) ).
% 1.07/1.00  
% 1.07/1.00  cnf(contradiction,plain,
% 1.07/1.00      ( $false ),
% 1.07/1.00      inference(minisat,
% 1.07/1.00                [status(thm)],
% 1.07/1.00                [c_684,c_559,c_547,c_449,c_425,c_447,c_440,c_195]) ).
% 1.07/1.00  
% 1.07/1.00  
% 1.07/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.07/1.00  
% 1.07/1.00  ------                               Statistics
% 1.07/1.00  
% 1.07/1.00  ------ General
% 1.07/1.00  
% 1.07/1.00  abstr_ref_over_cycles:                  0
% 1.07/1.00  abstr_ref_under_cycles:                 0
% 1.07/1.00  gc_basic_clause_elim:                   0
% 1.07/1.00  forced_gc_time:                         0
% 1.07/1.00  parsing_time:                           0.009
% 1.07/1.00  unif_index_cands_time:                  0.
% 1.07/1.00  unif_index_add_time:                    0.
% 1.07/1.00  orderings_time:                         0.
% 1.07/1.00  out_proof_time:                         0.01
% 1.07/1.00  total_time:                             0.059
% 1.07/1.00  num_of_symbols:                         47
% 1.07/1.00  num_of_terms:                           797
% 1.07/1.00  
% 1.07/1.00  ------ Preprocessing
% 1.07/1.00  
% 1.07/1.00  num_of_splits:                          0
% 1.07/1.00  num_of_split_atoms:                     0
% 1.07/1.00  num_of_reused_defs:                     0
% 1.07/1.00  num_eq_ax_congr_red:                    4
% 1.07/1.00  num_of_sem_filtered_clauses:            1
% 1.07/1.00  num_of_subtypes:                        3
% 1.07/1.00  monotx_restored_types:                  0
% 1.07/1.00  sat_num_of_epr_types:                   0
% 1.07/1.00  sat_num_of_non_cyclic_types:            0
% 1.07/1.00  sat_guarded_non_collapsed_types:        0
% 1.07/1.00  num_pure_diseq_elim:                    0
% 1.07/1.00  simp_replaced_by:                       0
% 1.07/1.00  res_preprocessed:                       61
% 1.07/1.00  prep_upred:                             0
% 1.07/1.00  prep_unflattend:                        11
% 1.07/1.00  smt_new_axioms:                         0
% 1.07/1.00  pred_elim_cands:                        1
% 1.07/1.00  pred_elim:                              6
% 1.07/1.00  pred_elim_cl:                           6
% 1.07/1.00  pred_elim_cycles:                       8
% 1.07/1.00  merged_defs:                            0
% 1.07/1.00  merged_defs_ncl:                        0
% 1.07/1.00  bin_hyper_res:                          0
% 1.07/1.00  prep_cycles:                            4
% 1.07/1.00  pred_elim_time:                         0.005
% 1.07/1.00  splitting_time:                         0.
% 1.07/1.00  sem_filter_time:                        0.
% 1.07/1.00  monotx_time:                            0.
% 1.07/1.00  subtype_inf_time:                       0.
% 1.07/1.00  
% 1.07/1.00  ------ Problem properties
% 1.07/1.00  
% 1.07/1.00  clauses:                                8
% 1.07/1.00  conjectures:                            1
% 1.07/1.00  epr:                                    0
% 1.07/1.00  horn:                                   8
% 1.07/1.00  ground:                                 2
% 1.07/1.00  unary:                                  7
% 1.07/1.00  binary:                                 0
% 1.07/1.00  lits:                                   11
% 1.07/1.00  lits_eq:                                8
% 1.07/1.00  fd_pure:                                0
% 1.07/1.00  fd_pseudo:                              0
% 1.07/1.00  fd_cond:                                0
% 1.07/1.00  fd_pseudo_cond:                         0
% 1.07/1.00  ac_symbols:                             0
% 1.07/1.00  
% 1.07/1.00  ------ Propositional Solver
% 1.07/1.00  
% 1.07/1.00  prop_solver_calls:                      27
% 1.07/1.00  prop_fast_solver_calls:                 305
% 1.07/1.00  smt_solver_calls:                       0
% 1.07/1.00  smt_fast_solver_calls:                  0
% 1.07/1.00  prop_num_of_clauses:                    199
% 1.07/1.00  prop_preprocess_simplified:             1344
% 1.07/1.00  prop_fo_subsumed:                       1
% 1.07/1.00  prop_solver_time:                       0.
% 1.07/1.00  smt_solver_time:                        0.
% 1.07/1.00  smt_fast_solver_time:                   0.
% 1.07/1.00  prop_fast_solver_time:                  0.
% 1.07/1.00  prop_unsat_core_time:                   0.
% 1.07/1.00  
% 1.07/1.00  ------ QBF
% 1.07/1.00  
% 1.07/1.00  qbf_q_res:                              0
% 1.07/1.00  qbf_num_tautologies:                    0
% 1.07/1.00  qbf_prep_cycles:                        0
% 1.07/1.00  
% 1.07/1.00  ------ BMC1
% 1.07/1.00  
% 1.07/1.00  bmc1_current_bound:                     -1
% 1.07/1.00  bmc1_last_solved_bound:                 -1
% 1.07/1.00  bmc1_unsat_core_size:                   -1
% 1.07/1.00  bmc1_unsat_core_parents_size:           -1
% 1.07/1.00  bmc1_merge_next_fun:                    0
% 1.07/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.07/1.00  
% 1.07/1.00  ------ Instantiation
% 1.07/1.00  
% 1.07/1.00  inst_num_of_clauses:                    62
% 1.07/1.00  inst_num_in_passive:                    11
% 1.07/1.00  inst_num_in_active:                     44
% 1.07/1.00  inst_num_in_unprocessed:                7
% 1.07/1.00  inst_num_of_loops:                      50
% 1.07/1.00  inst_num_of_learning_restarts:          0
% 1.07/1.00  inst_num_moves_active_passive:          2
% 1.07/1.00  inst_lit_activity:                      0
% 1.07/1.00  inst_lit_activity_moves:                0
% 1.07/1.00  inst_num_tautologies:                   0
% 1.07/1.00  inst_num_prop_implied:                  0
% 1.07/1.00  inst_num_existing_simplified:           0
% 1.07/1.00  inst_num_eq_res_simplified:             0
% 1.07/1.00  inst_num_child_elim:                    0
% 1.07/1.00  inst_num_of_dismatching_blockings:      2
% 1.07/1.00  inst_num_of_non_proper_insts:           38
% 1.07/1.00  inst_num_of_duplicates:                 0
% 1.07/1.00  inst_inst_num_from_inst_to_res:         0
% 1.07/1.00  inst_dismatching_checking_time:         0.
% 1.07/1.00  
% 1.07/1.00  ------ Resolution
% 1.07/1.00  
% 1.07/1.00  res_num_of_clauses:                     0
% 1.07/1.00  res_num_in_passive:                     0
% 1.07/1.00  res_num_in_active:                      0
% 1.07/1.00  res_num_of_loops:                       65
% 1.07/1.00  res_forward_subset_subsumed:            11
% 1.07/1.00  res_backward_subset_subsumed:           0
% 1.07/1.00  res_forward_subsumed:                   1
% 1.07/1.00  res_backward_subsumed:                  0
% 1.07/1.00  res_forward_subsumption_resolution:     0
% 1.07/1.00  res_backward_subsumption_resolution:    0
% 1.07/1.00  res_clause_to_clause_subsumption:       28
% 1.07/1.00  res_orphan_elimination:                 0
% 1.07/1.00  res_tautology_del:                      8
% 1.07/1.00  res_num_eq_res_simplified:              0
% 1.07/1.00  res_num_sel_changes:                    0
% 1.07/1.00  res_moves_from_active_to_pass:          0
% 1.07/1.00  
% 1.07/1.00  ------ Superposition
% 1.07/1.00  
% 1.07/1.00  sup_time_total:                         0.
% 1.07/1.00  sup_time_generating:                    0.
% 1.07/1.00  sup_time_sim_full:                      0.
% 1.07/1.00  sup_time_sim_immed:                     0.
% 1.07/1.00  
% 1.07/1.00  sup_num_of_clauses:                     12
% 1.07/1.00  sup_num_in_active:                      10
% 1.07/1.00  sup_num_in_passive:                     2
% 1.07/1.00  sup_num_of_loops:                       9
% 1.07/1.00  sup_fw_superposition:                   3
% 1.07/1.00  sup_bw_superposition:                   2
% 1.07/1.00  sup_immediate_simplified:               1
% 1.07/1.00  sup_given_eliminated:                   0
% 1.07/1.00  comparisons_done:                       0
% 1.07/1.00  comparisons_avoided:                    0
% 1.07/1.00  
% 1.07/1.00  ------ Simplifications
% 1.07/1.00  
% 1.07/1.00  
% 1.07/1.00  sim_fw_subset_subsumed:                 0
% 1.07/1.00  sim_bw_subset_subsumed:                 0
% 1.07/1.00  sim_fw_subsumed:                        0
% 1.07/1.00  sim_bw_subsumed:                        0
% 1.07/1.00  sim_fw_subsumption_res:                 0
% 1.07/1.00  sim_bw_subsumption_res:                 0
% 1.07/1.00  sim_tautology_del:                      0
% 1.07/1.00  sim_eq_tautology_del:                   0
% 1.07/1.00  sim_eq_res_simp:                        0
% 1.07/1.00  sim_fw_demodulated:                     0
% 1.07/1.00  sim_bw_demodulated:                     0
% 1.07/1.00  sim_light_normalised:                   2
% 1.07/1.00  sim_joinable_taut:                      0
% 1.07/1.00  sim_joinable_simp:                      0
% 1.07/1.00  sim_ac_normalised:                      0
% 1.07/1.00  sim_smt_subsumption:                    0
% 1.07/1.00  
%------------------------------------------------------------------------------
