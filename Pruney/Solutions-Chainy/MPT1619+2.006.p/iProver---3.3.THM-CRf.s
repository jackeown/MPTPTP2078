%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:32 EST 2020

% Result     : Theorem 0.94s
% Output     : CNFRefutation 0.94s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 201 expanded)
%              Number of clauses        :   58 (  63 expanded)
%              Number of leaves         :   27 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  248 ( 346 expanded)
%              Number of equality atoms :  131 ( 215 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f54,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f36,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(rectify,[],[f27])).

fof(f51,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f36])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f61,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f66])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f67])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f68])).

fof(f72,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f61,f69,f69])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f52,f55])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f19,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f20,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(definition_unfolding,[],[f57,f60])).

fof(f22,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k6_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => k6_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f35,plain,(
    ? [X0] :
      ( k6_yellow_1(k1_xboole_0,X0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f39,plain,
    ( ? [X0] :
        ( k6_yellow_1(k1_xboole_0,X0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
        & l1_orders_2(X0) )
   => ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
    & l1_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f39])).

fof(f62,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f63,f69,f69])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => v1_yellow_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_313,plain,
    ( k5_yellow_1(X0_44,X1_44) = k5_yellow_1(X2_44,X3_44)
    | X0_44 != X2_44
    | X1_44 != X3_44 ),
    theory(equality)).

cnf(c_557,plain,
    ( k5_yellow_1(X0_44,X1_44) = k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
    | X1_44 != k2_funcop_1(k1_xboole_0,sK1)
    | X0_44 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_559,plain,
    ( k5_yellow_1(k1_xboole_0,k1_xboole_0) = k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
    | k1_xboole_0 != k2_funcop_1(k1_xboole_0,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_557])).

cnf(c_309,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_434,plain,
    ( X0_45 != X1_45
    | k6_yellow_1(k1_xboole_0,sK1) != X1_45
    | k6_yellow_1(k1_xboole_0,sK1) = X0_45 ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_485,plain,
    ( X0_45 != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
    | k6_yellow_1(k1_xboole_0,sK1) = X0_45
    | k6_yellow_1(k1_xboole_0,sK1) != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1)) ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_556,plain,
    ( k5_yellow_1(X0_44,X1_44) != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
    | k6_yellow_1(k1_xboole_0,sK1) = k5_yellow_1(X0_44,X1_44)
    | k6_yellow_1(k1_xboole_0,sK1) != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1)) ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_558,plain,
    ( k5_yellow_1(k1_xboole_0,k1_xboole_0) != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
    | k6_yellow_1(k1_xboole_0,sK1) != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
    | k6_yellow_1(k1_xboole_0,sK1) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_556])).

cnf(c_441,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != X0_45
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k6_yellow_1(X0_44,sK1)
    | k6_yellow_1(X0_44,sK1) != X0_45 ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_474,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k6_yellow_1(X0_44,sK1)
    | k6_yellow_1(X0_44,sK1) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_475,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK1)
    | k6_yellow_1(k1_xboole_0,sK1) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_456,plain,
    ( X0_45 != k6_yellow_1(k1_xboole_0,sK1)
    | k6_yellow_1(k1_xboole_0,sK1) = X0_45
    | k6_yellow_1(k1_xboole_0,sK1) != k6_yellow_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_465,plain,
    ( k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1)) != k6_yellow_1(k1_xboole_0,sK1)
    | k6_yellow_1(k1_xboole_0,sK1) = k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
    | k6_yellow_1(k1_xboole_0,sK1) != k6_yellow_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_456])).

cnf(c_422,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != X0_45
    | k6_yellow_1(k1_xboole_0,sK1) != X0_45
    | k6_yellow_1(k1_xboole_0,sK1) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_432,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK1)
    | k6_yellow_1(k1_xboole_0,sK1) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | k6_yellow_1(k1_xboole_0,sK1) != k6_yellow_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_422])).

cnf(c_314,plain,
    ( ~ v1_yellow_1(X0_44)
    | v1_yellow_1(X1_44)
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_417,plain,
    ( v1_yellow_1(X0_44)
    | ~ v1_yellow_1(k2_funcop_1(X1_44,sK1))
    | X0_44 != k2_funcop_1(X1_44,sK1) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_419,plain,
    ( ~ v1_yellow_1(k2_funcop_1(k1_xboole_0,sK1))
    | v1_yellow_1(k1_xboole_0)
    | k1_xboole_0 != k2_funcop_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_417])).

cnf(c_6,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3,plain,
    ( v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_11,plain,
    ( ~ v1_partfun1(X0,k1_xboole_0)
    | ~ v4_relat_1(X0,k1_xboole_0)
    | ~ v1_yellow_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_183,plain,
    ( ~ v1_partfun1(X0,k1_xboole_0)
    | ~ v1_yellow_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,X0)
    | k1_xboole_0 != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_184,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_183])).

cnf(c_5,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_32,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_38,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_186,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_184,c_32,c_38,c_0])).

cnf(c_213,plain,
    ( ~ v1_yellow_1(k1_xboole_0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | k6_partfun1(X0) != k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_186])).

cnf(c_214,plain,
    ( ~ v1_yellow_1(k1_xboole_0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | k6_partfun1(k1_xboole_0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_4,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_216,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_214,c_4])).

cnf(c_217,plain,
    ( ~ v1_yellow_1(k1_xboole_0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_216])).

cnf(c_297,plain,
    ( ~ v1_yellow_1(k1_xboole_0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_217])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_10,plain,
    ( v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_206,plain,
    ( k2_funcop_1(k1_xboole_0,X0) != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_207,plain,
    ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) ),
    inference(unflattening,[status(thm)],[c_206])).

cnf(c_298,plain,
    ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0_46) ),
    inference(subtyping,[status(esa)],[c_207])).

cnf(c_331,plain,
    ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_8,plain,
    ( ~ l1_orders_2(X0)
    | k5_yellow_1(X1,k2_funcop_1(X1,X0)) = k6_yellow_1(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_13,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_171,plain,
    ( k5_yellow_1(X0,k2_funcop_1(X0,X1)) = k6_yellow_1(X0,X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_172,plain,
    ( k5_yellow_1(X0,k2_funcop_1(X0,sK1)) = k6_yellow_1(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_171])).

cnf(c_299,plain,
    ( k5_yellow_1(X0_44,k2_funcop_1(X0_44,sK1)) = k6_yellow_1(X0_44,sK1) ),
    inference(subtyping,[status(esa)],[c_172])).

cnf(c_330,plain,
    ( k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1)) = k6_yellow_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_12,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_303,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_306,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_325,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_311,plain,
    ( k6_yellow_1(X0_44,X0_46) = k6_yellow_1(X1_44,X0_46)
    | X0_44 != X1_44 ),
    theory(equality)).

cnf(c_318,plain,
    ( k6_yellow_1(k1_xboole_0,sK1) = k6_yellow_1(k1_xboole_0,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_9,plain,
    ( v1_yellow_1(k2_funcop_1(X0,X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_162,plain,
    ( v1_yellow_1(k2_funcop_1(X0,X1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_163,plain,
    ( v1_yellow_1(k2_funcop_1(X0,sK1)) ),
    inference(unflattening,[status(thm)],[c_162])).

cnf(c_165,plain,
    ( v1_yellow_1(k2_funcop_1(k1_xboole_0,sK1)) ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_559,c_558,c_475,c_465,c_432,c_419,c_297,c_331,c_330,c_303,c_325,c_318,c_165])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.94/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.94/1.00  
% 0.94/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.94/1.00  
% 0.94/1.00  ------  iProver source info
% 0.94/1.00  
% 0.94/1.00  git: date: 2020-06-30 10:37:57 +0100
% 0.94/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.94/1.00  git: non_committed_changes: false
% 0.94/1.00  git: last_make_outside_of_git: false
% 0.94/1.00  
% 0.94/1.00  ------ 
% 0.94/1.00  
% 0.94/1.00  ------ Input Options
% 0.94/1.00  
% 0.94/1.00  --out_options                           all
% 0.94/1.00  --tptp_safe_out                         true
% 0.94/1.00  --problem_path                          ""
% 0.94/1.00  --include_path                          ""
% 0.94/1.00  --clausifier                            res/vclausify_rel
% 0.94/1.00  --clausifier_options                    --mode clausify
% 0.94/1.00  --stdin                                 false
% 0.94/1.00  --stats_out                             all
% 0.94/1.00  
% 0.94/1.00  ------ General Options
% 0.94/1.00  
% 0.94/1.00  --fof                                   false
% 0.94/1.00  --time_out_real                         305.
% 0.94/1.00  --time_out_virtual                      -1.
% 0.94/1.00  --symbol_type_check                     false
% 0.94/1.00  --clausify_out                          false
% 0.94/1.00  --sig_cnt_out                           false
% 0.94/1.00  --trig_cnt_out                          false
% 0.94/1.00  --trig_cnt_out_tolerance                1.
% 0.94/1.00  --trig_cnt_out_sk_spl                   false
% 0.94/1.00  --abstr_cl_out                          false
% 0.94/1.00  
% 0.94/1.00  ------ Global Options
% 0.94/1.00  
% 0.94/1.00  --schedule                              default
% 0.94/1.00  --add_important_lit                     false
% 0.94/1.00  --prop_solver_per_cl                    1000
% 0.94/1.00  --min_unsat_core                        false
% 0.94/1.00  --soft_assumptions                      false
% 0.94/1.00  --soft_lemma_size                       3
% 0.94/1.00  --prop_impl_unit_size                   0
% 0.94/1.00  --prop_impl_unit                        []
% 0.94/1.00  --share_sel_clauses                     true
% 0.94/1.00  --reset_solvers                         false
% 0.94/1.00  --bc_imp_inh                            [conj_cone]
% 0.94/1.00  --conj_cone_tolerance                   3.
% 0.94/1.00  --extra_neg_conj                        none
% 0.94/1.00  --large_theory_mode                     true
% 0.94/1.00  --prolific_symb_bound                   200
% 0.94/1.00  --lt_threshold                          2000
% 0.94/1.00  --clause_weak_htbl                      true
% 0.94/1.00  --gc_record_bc_elim                     false
% 0.94/1.00  
% 0.94/1.00  ------ Preprocessing Options
% 0.94/1.00  
% 0.94/1.00  --preprocessing_flag                    true
% 0.94/1.00  --time_out_prep_mult                    0.1
% 0.94/1.00  --splitting_mode                        input
% 0.94/1.00  --splitting_grd                         true
% 0.94/1.00  --splitting_cvd                         false
% 0.94/1.00  --splitting_cvd_svl                     false
% 0.94/1.00  --splitting_nvd                         32
% 0.94/1.00  --sub_typing                            true
% 0.94/1.00  --prep_gs_sim                           true
% 0.94/1.00  --prep_unflatten                        true
% 0.94/1.00  --prep_res_sim                          true
% 0.94/1.00  --prep_upred                            true
% 0.94/1.00  --prep_sem_filter                       exhaustive
% 0.94/1.00  --prep_sem_filter_out                   false
% 0.94/1.00  --pred_elim                             true
% 0.94/1.00  --res_sim_input                         true
% 0.94/1.00  --eq_ax_congr_red                       true
% 0.94/1.00  --pure_diseq_elim                       true
% 0.94/1.00  --brand_transform                       false
% 0.94/1.00  --non_eq_to_eq                          false
% 0.94/1.00  --prep_def_merge                        true
% 0.94/1.00  --prep_def_merge_prop_impl              false
% 0.94/1.00  --prep_def_merge_mbd                    true
% 0.94/1.00  --prep_def_merge_tr_red                 false
% 0.94/1.00  --prep_def_merge_tr_cl                  false
% 0.94/1.00  --smt_preprocessing                     true
% 0.94/1.00  --smt_ac_axioms                         fast
% 0.94/1.00  --preprocessed_out                      false
% 0.94/1.00  --preprocessed_stats                    false
% 0.94/1.00  
% 0.94/1.00  ------ Abstraction refinement Options
% 0.94/1.00  
% 0.94/1.00  --abstr_ref                             []
% 0.94/1.00  --abstr_ref_prep                        false
% 0.94/1.00  --abstr_ref_until_sat                   false
% 0.94/1.00  --abstr_ref_sig_restrict                funpre
% 0.94/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.94/1.00  --abstr_ref_under                       []
% 0.94/1.00  
% 0.94/1.00  ------ SAT Options
% 0.94/1.00  
% 0.94/1.00  --sat_mode                              false
% 0.94/1.00  --sat_fm_restart_options                ""
% 0.94/1.00  --sat_gr_def                            false
% 0.94/1.00  --sat_epr_types                         true
% 0.94/1.00  --sat_non_cyclic_types                  false
% 0.94/1.00  --sat_finite_models                     false
% 0.94/1.00  --sat_fm_lemmas                         false
% 0.94/1.00  --sat_fm_prep                           false
% 0.94/1.00  --sat_fm_uc_incr                        true
% 0.94/1.00  --sat_out_model                         small
% 0.94/1.00  --sat_out_clauses                       false
% 0.94/1.00  
% 0.94/1.00  ------ QBF Options
% 0.94/1.00  
% 0.94/1.00  --qbf_mode                              false
% 0.94/1.00  --qbf_elim_univ                         false
% 0.94/1.00  --qbf_dom_inst                          none
% 0.94/1.00  --qbf_dom_pre_inst                      false
% 0.94/1.00  --qbf_sk_in                             false
% 0.94/1.00  --qbf_pred_elim                         true
% 0.94/1.00  --qbf_split                             512
% 0.94/1.00  
% 0.94/1.00  ------ BMC1 Options
% 0.94/1.00  
% 0.94/1.00  --bmc1_incremental                      false
% 0.94/1.00  --bmc1_axioms                           reachable_all
% 0.94/1.00  --bmc1_min_bound                        0
% 0.94/1.00  --bmc1_max_bound                        -1
% 0.94/1.00  --bmc1_max_bound_default                -1
% 0.94/1.00  --bmc1_symbol_reachability              true
% 0.94/1.00  --bmc1_property_lemmas                  false
% 0.94/1.00  --bmc1_k_induction                      false
% 0.94/1.00  --bmc1_non_equiv_states                 false
% 0.94/1.00  --bmc1_deadlock                         false
% 0.94/1.00  --bmc1_ucm                              false
% 0.94/1.00  --bmc1_add_unsat_core                   none
% 0.94/1.00  --bmc1_unsat_core_children              false
% 0.94/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.94/1.00  --bmc1_out_stat                         full
% 0.94/1.00  --bmc1_ground_init                      false
% 0.94/1.00  --bmc1_pre_inst_next_state              false
% 0.94/1.00  --bmc1_pre_inst_state                   false
% 0.94/1.00  --bmc1_pre_inst_reach_state             false
% 0.94/1.00  --bmc1_out_unsat_core                   false
% 0.94/1.00  --bmc1_aig_witness_out                  false
% 0.94/1.00  --bmc1_verbose                          false
% 0.94/1.00  --bmc1_dump_clauses_tptp                false
% 0.94/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.94/1.00  --bmc1_dump_file                        -
% 0.94/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.94/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.94/1.00  --bmc1_ucm_extend_mode                  1
% 0.94/1.00  --bmc1_ucm_init_mode                    2
% 0.94/1.00  --bmc1_ucm_cone_mode                    none
% 0.94/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.94/1.00  --bmc1_ucm_relax_model                  4
% 0.94/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.94/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.94/1.00  --bmc1_ucm_layered_model                none
% 0.94/1.00  --bmc1_ucm_max_lemma_size               10
% 0.94/1.00  
% 0.94/1.00  ------ AIG Options
% 0.94/1.00  
% 0.94/1.00  --aig_mode                              false
% 0.94/1.00  
% 0.94/1.00  ------ Instantiation Options
% 0.94/1.00  
% 0.94/1.00  --instantiation_flag                    true
% 0.94/1.00  --inst_sos_flag                         false
% 0.94/1.00  --inst_sos_phase                        true
% 0.94/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.94/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.94/1.00  --inst_lit_sel_side                     num_symb
% 0.94/1.00  --inst_solver_per_active                1400
% 0.94/1.00  --inst_solver_calls_frac                1.
% 0.94/1.00  --inst_passive_queue_type               priority_queues
% 0.94/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.94/1.00  --inst_passive_queues_freq              [25;2]
% 0.94/1.00  --inst_dismatching                      true
% 0.94/1.00  --inst_eager_unprocessed_to_passive     true
% 0.94/1.00  --inst_prop_sim_given                   true
% 0.94/1.00  --inst_prop_sim_new                     false
% 0.94/1.00  --inst_subs_new                         false
% 0.94/1.00  --inst_eq_res_simp                      false
% 0.94/1.00  --inst_subs_given                       false
% 0.94/1.00  --inst_orphan_elimination               true
% 0.94/1.00  --inst_learning_loop_flag               true
% 0.94/1.00  --inst_learning_start                   3000
% 0.94/1.00  --inst_learning_factor                  2
% 0.94/1.00  --inst_start_prop_sim_after_learn       3
% 0.94/1.00  --inst_sel_renew                        solver
% 0.94/1.00  --inst_lit_activity_flag                true
% 0.94/1.00  --inst_restr_to_given                   false
% 0.94/1.00  --inst_activity_threshold               500
% 0.94/1.00  --inst_out_proof                        true
% 0.94/1.00  
% 0.94/1.00  ------ Resolution Options
% 0.94/1.00  
% 0.94/1.00  --resolution_flag                       true
% 0.94/1.00  --res_lit_sel                           adaptive
% 0.94/1.00  --res_lit_sel_side                      none
% 0.94/1.00  --res_ordering                          kbo
% 0.94/1.00  --res_to_prop_solver                    active
% 0.94/1.00  --res_prop_simpl_new                    false
% 0.94/1.00  --res_prop_simpl_given                  true
% 0.94/1.00  --res_passive_queue_type                priority_queues
% 0.94/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.94/1.00  --res_passive_queues_freq               [15;5]
% 0.94/1.00  --res_forward_subs                      full
% 0.94/1.00  --res_backward_subs                     full
% 0.94/1.00  --res_forward_subs_resolution           true
% 0.94/1.00  --res_backward_subs_resolution          true
% 0.94/1.00  --res_orphan_elimination                true
% 0.94/1.00  --res_time_limit                        2.
% 0.94/1.00  --res_out_proof                         true
% 0.94/1.00  
% 0.94/1.00  ------ Superposition Options
% 0.94/1.00  
% 0.94/1.00  --superposition_flag                    true
% 0.94/1.00  --sup_passive_queue_type                priority_queues
% 0.94/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.94/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.94/1.00  --demod_completeness_check              fast
% 0.94/1.00  --demod_use_ground                      true
% 0.94/1.00  --sup_to_prop_solver                    passive
% 0.94/1.00  --sup_prop_simpl_new                    true
% 0.94/1.00  --sup_prop_simpl_given                  true
% 0.94/1.00  --sup_fun_splitting                     false
% 0.94/1.00  --sup_smt_interval                      50000
% 0.94/1.00  
% 0.94/1.00  ------ Superposition Simplification Setup
% 0.94/1.00  
% 0.94/1.00  --sup_indices_passive                   []
% 0.94/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.94/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.00  --sup_full_bw                           [BwDemod]
% 0.94/1.00  --sup_immed_triv                        [TrivRules]
% 0.94/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.94/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.00  --sup_immed_bw_main                     []
% 0.94/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.94/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.94/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.94/1.00  
% 0.94/1.00  ------ Combination Options
% 0.94/1.00  
% 0.94/1.00  --comb_res_mult                         3
% 0.94/1.00  --comb_sup_mult                         2
% 0.94/1.00  --comb_inst_mult                        10
% 0.94/1.00  
% 0.94/1.00  ------ Debug Options
% 0.94/1.00  
% 0.94/1.00  --dbg_backtrace                         false
% 0.94/1.00  --dbg_dump_prop_clauses                 false
% 0.94/1.00  --dbg_dump_prop_clauses_file            -
% 0.94/1.00  --dbg_out_stat                          false
% 0.94/1.00  ------ Parsing...
% 0.94/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.94/1.00  
% 0.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 0.94/1.00  
% 0.94/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.94/1.00  
% 0.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.94/1.00  ------ Proving...
% 0.94/1.00  ------ Problem Properties 
% 0.94/1.00  
% 0.94/1.00  
% 0.94/1.00  clauses                                 8
% 0.94/1.00  conjectures                             1
% 0.94/1.00  EPR                                     0
% 0.94/1.00  Horn                                    8
% 0.94/1.00  unary                                   7
% 0.94/1.00  binary                                  1
% 0.94/1.00  lits                                    9
% 0.94/1.00  lits eq                                 6
% 0.94/1.00  fd_pure                                 0
% 0.94/1.00  fd_pseudo                               0
% 0.94/1.00  fd_cond                                 0
% 0.94/1.00  fd_pseudo_cond                          0
% 0.94/1.00  AC symbols                              0
% 0.94/1.00  
% 0.94/1.00  ------ Schedule dynamic 5 is on 
% 0.94/1.00  
% 0.94/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.94/1.00  
% 0.94/1.00  
% 0.94/1.00  ------ 
% 0.94/1.00  Current options:
% 0.94/1.00  ------ 
% 0.94/1.00  
% 0.94/1.00  ------ Input Options
% 0.94/1.00  
% 0.94/1.00  --out_options                           all
% 0.94/1.00  --tptp_safe_out                         true
% 0.94/1.00  --problem_path                          ""
% 0.94/1.00  --include_path                          ""
% 0.94/1.00  --clausifier                            res/vclausify_rel
% 0.94/1.00  --clausifier_options                    --mode clausify
% 0.94/1.00  --stdin                                 false
% 0.94/1.00  --stats_out                             all
% 0.94/1.00  
% 0.94/1.00  ------ General Options
% 0.94/1.00  
% 0.94/1.00  --fof                                   false
% 0.94/1.00  --time_out_real                         305.
% 0.94/1.00  --time_out_virtual                      -1.
% 0.94/1.00  --symbol_type_check                     false
% 0.94/1.00  --clausify_out                          false
% 0.94/1.00  --sig_cnt_out                           false
% 0.94/1.00  --trig_cnt_out                          false
% 0.94/1.00  --trig_cnt_out_tolerance                1.
% 0.94/1.00  --trig_cnt_out_sk_spl                   false
% 0.94/1.00  --abstr_cl_out                          false
% 0.94/1.00  
% 0.94/1.00  ------ Global Options
% 0.94/1.00  
% 0.94/1.00  --schedule                              default
% 0.94/1.00  --add_important_lit                     false
% 0.94/1.00  --prop_solver_per_cl                    1000
% 0.94/1.00  --min_unsat_core                        false
% 0.94/1.00  --soft_assumptions                      false
% 0.94/1.00  --soft_lemma_size                       3
% 0.94/1.00  --prop_impl_unit_size                   0
% 0.94/1.00  --prop_impl_unit                        []
% 0.94/1.00  --share_sel_clauses                     true
% 0.94/1.00  --reset_solvers                         false
% 0.94/1.00  --bc_imp_inh                            [conj_cone]
% 0.94/1.00  --conj_cone_tolerance                   3.
% 0.94/1.00  --extra_neg_conj                        none
% 0.94/1.00  --large_theory_mode                     true
% 0.94/1.00  --prolific_symb_bound                   200
% 0.94/1.00  --lt_threshold                          2000
% 0.94/1.00  --clause_weak_htbl                      true
% 0.94/1.00  --gc_record_bc_elim                     false
% 0.94/1.00  
% 0.94/1.00  ------ Preprocessing Options
% 0.94/1.00  
% 0.94/1.00  --preprocessing_flag                    true
% 0.94/1.00  --time_out_prep_mult                    0.1
% 0.94/1.00  --splitting_mode                        input
% 0.94/1.00  --splitting_grd                         true
% 0.94/1.00  --splitting_cvd                         false
% 0.94/1.00  --splitting_cvd_svl                     false
% 0.94/1.00  --splitting_nvd                         32
% 0.94/1.00  --sub_typing                            true
% 0.94/1.00  --prep_gs_sim                           true
% 0.94/1.00  --prep_unflatten                        true
% 0.94/1.00  --prep_res_sim                          true
% 0.94/1.00  --prep_upred                            true
% 0.94/1.00  --prep_sem_filter                       exhaustive
% 0.94/1.00  --prep_sem_filter_out                   false
% 0.94/1.00  --pred_elim                             true
% 0.94/1.00  --res_sim_input                         true
% 0.94/1.00  --eq_ax_congr_red                       true
% 0.94/1.00  --pure_diseq_elim                       true
% 0.94/1.00  --brand_transform                       false
% 0.94/1.00  --non_eq_to_eq                          false
% 0.94/1.00  --prep_def_merge                        true
% 0.94/1.00  --prep_def_merge_prop_impl              false
% 0.94/1.00  --prep_def_merge_mbd                    true
% 0.94/1.00  --prep_def_merge_tr_red                 false
% 0.94/1.00  --prep_def_merge_tr_cl                  false
% 0.94/1.00  --smt_preprocessing                     true
% 0.94/1.00  --smt_ac_axioms                         fast
% 0.94/1.00  --preprocessed_out                      false
% 0.94/1.00  --preprocessed_stats                    false
% 0.94/1.00  
% 0.94/1.00  ------ Abstraction refinement Options
% 0.94/1.00  
% 0.94/1.00  --abstr_ref                             []
% 0.94/1.00  --abstr_ref_prep                        false
% 0.94/1.00  --abstr_ref_until_sat                   false
% 0.94/1.00  --abstr_ref_sig_restrict                funpre
% 0.94/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.94/1.00  --abstr_ref_under                       []
% 0.94/1.00  
% 0.94/1.00  ------ SAT Options
% 0.94/1.00  
% 0.94/1.00  --sat_mode                              false
% 0.94/1.00  --sat_fm_restart_options                ""
% 0.94/1.00  --sat_gr_def                            false
% 0.94/1.00  --sat_epr_types                         true
% 0.94/1.00  --sat_non_cyclic_types                  false
% 0.94/1.00  --sat_finite_models                     false
% 0.94/1.00  --sat_fm_lemmas                         false
% 0.94/1.00  --sat_fm_prep                           false
% 0.94/1.00  --sat_fm_uc_incr                        true
% 0.94/1.00  --sat_out_model                         small
% 0.94/1.00  --sat_out_clauses                       false
% 0.94/1.00  
% 0.94/1.00  ------ QBF Options
% 0.94/1.00  
% 0.94/1.00  --qbf_mode                              false
% 0.94/1.00  --qbf_elim_univ                         false
% 0.94/1.00  --qbf_dom_inst                          none
% 0.94/1.00  --qbf_dom_pre_inst                      false
% 0.94/1.00  --qbf_sk_in                             false
% 0.94/1.00  --qbf_pred_elim                         true
% 0.94/1.00  --qbf_split                             512
% 0.94/1.00  
% 0.94/1.00  ------ BMC1 Options
% 0.94/1.00  
% 0.94/1.00  --bmc1_incremental                      false
% 0.94/1.00  --bmc1_axioms                           reachable_all
% 0.94/1.00  --bmc1_min_bound                        0
% 0.94/1.00  --bmc1_max_bound                        -1
% 0.94/1.00  --bmc1_max_bound_default                -1
% 0.94/1.00  --bmc1_symbol_reachability              true
% 0.94/1.00  --bmc1_property_lemmas                  false
% 0.94/1.00  --bmc1_k_induction                      false
% 0.94/1.00  --bmc1_non_equiv_states                 false
% 0.94/1.00  --bmc1_deadlock                         false
% 0.94/1.00  --bmc1_ucm                              false
% 0.94/1.00  --bmc1_add_unsat_core                   none
% 0.94/1.00  --bmc1_unsat_core_children              false
% 0.94/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.94/1.00  --bmc1_out_stat                         full
% 0.94/1.00  --bmc1_ground_init                      false
% 0.94/1.00  --bmc1_pre_inst_next_state              false
% 0.94/1.00  --bmc1_pre_inst_state                   false
% 0.94/1.00  --bmc1_pre_inst_reach_state             false
% 0.94/1.00  --bmc1_out_unsat_core                   false
% 0.94/1.00  --bmc1_aig_witness_out                  false
% 0.94/1.00  --bmc1_verbose                          false
% 0.94/1.00  --bmc1_dump_clauses_tptp                false
% 0.94/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.94/1.00  --bmc1_dump_file                        -
% 0.94/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.94/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.94/1.00  --bmc1_ucm_extend_mode                  1
% 0.94/1.00  --bmc1_ucm_init_mode                    2
% 0.94/1.00  --bmc1_ucm_cone_mode                    none
% 0.94/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.94/1.00  --bmc1_ucm_relax_model                  4
% 0.94/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.94/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.94/1.00  --bmc1_ucm_layered_model                none
% 0.94/1.00  --bmc1_ucm_max_lemma_size               10
% 0.94/1.00  
% 0.94/1.00  ------ AIG Options
% 0.94/1.00  
% 0.94/1.00  --aig_mode                              false
% 0.94/1.00  
% 0.94/1.00  ------ Instantiation Options
% 0.94/1.00  
% 0.94/1.00  --instantiation_flag                    true
% 0.94/1.00  --inst_sos_flag                         false
% 0.94/1.00  --inst_sos_phase                        true
% 0.94/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.94/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.94/1.00  --inst_lit_sel_side                     none
% 0.94/1.00  --inst_solver_per_active                1400
% 0.94/1.00  --inst_solver_calls_frac                1.
% 0.94/1.00  --inst_passive_queue_type               priority_queues
% 0.94/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.94/1.00  --inst_passive_queues_freq              [25;2]
% 0.94/1.00  --inst_dismatching                      true
% 0.94/1.00  --inst_eager_unprocessed_to_passive     true
% 0.94/1.00  --inst_prop_sim_given                   true
% 0.94/1.00  --inst_prop_sim_new                     false
% 0.94/1.00  --inst_subs_new                         false
% 0.94/1.00  --inst_eq_res_simp                      false
% 0.94/1.00  --inst_subs_given                       false
% 0.94/1.00  --inst_orphan_elimination               true
% 0.94/1.00  --inst_learning_loop_flag               true
% 0.94/1.00  --inst_learning_start                   3000
% 0.94/1.00  --inst_learning_factor                  2
% 0.94/1.00  --inst_start_prop_sim_after_learn       3
% 0.94/1.00  --inst_sel_renew                        solver
% 0.94/1.00  --inst_lit_activity_flag                true
% 0.94/1.00  --inst_restr_to_given                   false
% 0.94/1.00  --inst_activity_threshold               500
% 0.94/1.00  --inst_out_proof                        true
% 0.94/1.00  
% 0.94/1.00  ------ Resolution Options
% 0.94/1.00  
% 0.94/1.00  --resolution_flag                       false
% 0.94/1.00  --res_lit_sel                           adaptive
% 0.94/1.00  --res_lit_sel_side                      none
% 0.94/1.00  --res_ordering                          kbo
% 0.94/1.00  --res_to_prop_solver                    active
% 0.94/1.00  --res_prop_simpl_new                    false
% 0.94/1.00  --res_prop_simpl_given                  true
% 0.94/1.00  --res_passive_queue_type                priority_queues
% 0.94/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.94/1.00  --res_passive_queues_freq               [15;5]
% 0.94/1.00  --res_forward_subs                      full
% 0.94/1.00  --res_backward_subs                     full
% 0.94/1.00  --res_forward_subs_resolution           true
% 0.94/1.00  --res_backward_subs_resolution          true
% 0.94/1.00  --res_orphan_elimination                true
% 0.94/1.00  --res_time_limit                        2.
% 0.94/1.00  --res_out_proof                         true
% 0.94/1.00  
% 0.94/1.00  ------ Superposition Options
% 0.94/1.00  
% 0.94/1.00  --superposition_flag                    true
% 0.94/1.00  --sup_passive_queue_type                priority_queues
% 0.94/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.94/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.94/1.00  --demod_completeness_check              fast
% 0.94/1.00  --demod_use_ground                      true
% 0.94/1.00  --sup_to_prop_solver                    passive
% 0.94/1.00  --sup_prop_simpl_new                    true
% 0.94/1.00  --sup_prop_simpl_given                  true
% 0.94/1.00  --sup_fun_splitting                     false
% 0.94/1.00  --sup_smt_interval                      50000
% 0.94/1.00  
% 0.94/1.00  ------ Superposition Simplification Setup
% 0.94/1.00  
% 0.94/1.00  --sup_indices_passive                   []
% 0.94/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.94/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.00  --sup_full_bw                           [BwDemod]
% 0.94/1.00  --sup_immed_triv                        [TrivRules]
% 0.94/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.94/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.00  --sup_immed_bw_main                     []
% 0.94/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.94/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.94/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.94/1.00  
% 0.94/1.00  ------ Combination Options
% 0.94/1.00  
% 0.94/1.00  --comb_res_mult                         3
% 0.94/1.00  --comb_sup_mult                         2
% 0.94/1.00  --comb_inst_mult                        10
% 0.94/1.00  
% 0.94/1.00  ------ Debug Options
% 0.94/1.00  
% 0.94/1.00  --dbg_backtrace                         false
% 0.94/1.00  --dbg_dump_prop_clauses                 false
% 0.94/1.00  --dbg_dump_prop_clauses_file            -
% 0.94/1.00  --dbg_out_stat                          false
% 0.94/1.00  
% 0.94/1.00  
% 0.94/1.00  
% 0.94/1.00  
% 0.94/1.00  ------ Proving...
% 0.94/1.00  
% 0.94/1.00  
% 0.94/1.00  % SZS status Theorem for theBenchmark.p
% 0.94/1.00  
% 0.94/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 0.94/1.00  
% 0.94/1.00  fof(f14,axiom,(
% 0.94/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f26,plain,(
% 0.94/1.00    ! [X0] : v1_partfun1(k6_partfun1(X0),X0)),
% 0.94/1.00    inference(pure_predicate_removal,[],[f14])).
% 0.94/1.00  
% 0.94/1.00  fof(f54,plain,(
% 0.94/1.00    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f26])).
% 0.94/1.00  
% 0.94/1.00  fof(f11,axiom,(
% 0.94/1.00    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f27,plain,(
% 0.94/1.00    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0)),
% 0.94/1.00    inference(pure_predicate_removal,[],[f11])).
% 0.94/1.00  
% 0.94/1.00  fof(f36,plain,(
% 0.94/1.00    ! [X0] : v4_relat_1(k1_xboole_0,X0)),
% 0.94/1.00    inference(rectify,[],[f27])).
% 0.94/1.00  
% 0.94/1.00  fof(f51,plain,(
% 0.94/1.00    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f36])).
% 0.94/1.00  
% 0.94/1.00  fof(f21,axiom,(
% 0.94/1.00    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f33,plain,(
% 0.94/1.00    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.94/1.00    inference(ennf_transformation,[],[f21])).
% 0.94/1.00  
% 0.94/1.00  fof(f34,plain,(
% 0.94/1.00    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.94/1.00    inference(flattening,[],[f33])).
% 0.94/1.00  
% 0.94/1.00  fof(f61,plain,(
% 0.94/1.00    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f34])).
% 0.94/1.00  
% 0.94/1.00  fof(f3,axiom,(
% 0.94/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f43,plain,(
% 0.94/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f3])).
% 0.94/1.00  
% 0.94/1.00  fof(f4,axiom,(
% 0.94/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f44,plain,(
% 0.94/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f4])).
% 0.94/1.00  
% 0.94/1.00  fof(f5,axiom,(
% 0.94/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f45,plain,(
% 0.94/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f5])).
% 0.94/1.00  
% 0.94/1.00  fof(f6,axiom,(
% 0.94/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f46,plain,(
% 0.94/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f6])).
% 0.94/1.00  
% 0.94/1.00  fof(f7,axiom,(
% 0.94/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f47,plain,(
% 0.94/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f7])).
% 0.94/1.00  
% 0.94/1.00  fof(f8,axiom,(
% 0.94/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f48,plain,(
% 0.94/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f8])).
% 0.94/1.00  
% 0.94/1.00  fof(f9,axiom,(
% 0.94/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f49,plain,(
% 0.94/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f9])).
% 0.94/1.00  
% 0.94/1.00  fof(f64,plain,(
% 0.94/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.94/1.00    inference(definition_unfolding,[],[f48,f49])).
% 0.94/1.00  
% 0.94/1.00  fof(f65,plain,(
% 0.94/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.94/1.00    inference(definition_unfolding,[],[f47,f64])).
% 0.94/1.00  
% 0.94/1.00  fof(f66,plain,(
% 0.94/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.94/1.00    inference(definition_unfolding,[],[f46,f65])).
% 0.94/1.00  
% 0.94/1.00  fof(f67,plain,(
% 0.94/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.94/1.00    inference(definition_unfolding,[],[f45,f66])).
% 0.94/1.00  
% 0.94/1.00  fof(f68,plain,(
% 0.94/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.94/1.00    inference(definition_unfolding,[],[f44,f67])).
% 0.94/1.00  
% 0.94/1.00  fof(f69,plain,(
% 0.94/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.94/1.00    inference(definition_unfolding,[],[f43,f68])).
% 0.94/1.00  
% 0.94/1.00  fof(f72,plain,(
% 0.94/1.00    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.94/1.00    inference(definition_unfolding,[],[f61,f69,f69])).
% 0.94/1.00  
% 0.94/1.00  fof(f13,axiom,(
% 0.94/1.00    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f30,plain,(
% 0.94/1.00    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.94/1.00    inference(ennf_transformation,[],[f13])).
% 0.94/1.00  
% 0.94/1.00  fof(f53,plain,(
% 0.94/1.00    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f30])).
% 0.94/1.00  
% 0.94/1.00  fof(f10,axiom,(
% 0.94/1.00    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f29,plain,(
% 0.94/1.00    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.94/1.00    inference(ennf_transformation,[],[f10])).
% 0.94/1.00  
% 0.94/1.00  fof(f50,plain,(
% 0.94/1.00    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f29])).
% 0.94/1.00  
% 0.94/1.00  fof(f1,axiom,(
% 0.94/1.00    v1_xboole_0(k1_xboole_0)),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f41,plain,(
% 0.94/1.00    v1_xboole_0(k1_xboole_0)),
% 0.94/1.00    inference(cnf_transformation,[],[f1])).
% 0.94/1.00  
% 0.94/1.00  fof(f12,axiom,(
% 0.94/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f52,plain,(
% 0.94/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.94/1.00    inference(cnf_transformation,[],[f12])).
% 0.94/1.00  
% 0.94/1.00  fof(f15,axiom,(
% 0.94/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f55,plain,(
% 0.94/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f15])).
% 0.94/1.00  
% 0.94/1.00  fof(f70,plain,(
% 0.94/1.00    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.94/1.00    inference(definition_unfolding,[],[f52,f55])).
% 0.94/1.00  
% 0.94/1.00  fof(f2,axiom,(
% 0.94/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f28,plain,(
% 0.94/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.94/1.00    inference(ennf_transformation,[],[f2])).
% 0.94/1.00  
% 0.94/1.00  fof(f42,plain,(
% 0.94/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f28])).
% 0.94/1.00  
% 0.94/1.00  fof(f19,axiom,(
% 0.94/1.00    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f59,plain,(
% 0.94/1.00    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 0.94/1.00    inference(cnf_transformation,[],[f19])).
% 0.94/1.00  
% 0.94/1.00  fof(f17,axiom,(
% 0.94/1.00    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f31,plain,(
% 0.94/1.00    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.94/1.00    inference(ennf_transformation,[],[f17])).
% 0.94/1.00  
% 0.94/1.00  fof(f57,plain,(
% 0.94/1.00    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f31])).
% 0.94/1.00  
% 0.94/1.00  fof(f20,axiom,(
% 0.94/1.00    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f60,plain,(
% 0.94/1.00    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f20])).
% 0.94/1.00  
% 0.94/1.00  fof(f71,plain,(
% 0.94/1.00    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.94/1.00    inference(definition_unfolding,[],[f57,f60])).
% 0.94/1.00  
% 0.94/1.00  fof(f22,conjecture,(
% 0.94/1.00    ! [X0] : (l1_orders_2(X0) => k6_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f23,negated_conjecture,(
% 0.94/1.00    ~! [X0] : (l1_orders_2(X0) => k6_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.94/1.00    inference(negated_conjecture,[],[f22])).
% 0.94/1.00  
% 0.94/1.00  fof(f35,plain,(
% 0.94/1.00    ? [X0] : (k6_yellow_1(k1_xboole_0,X0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) & l1_orders_2(X0))),
% 0.94/1.00    inference(ennf_transformation,[],[f23])).
% 0.94/1.00  
% 0.94/1.00  fof(f39,plain,(
% 0.94/1.00    ? [X0] : (k6_yellow_1(k1_xboole_0,X0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) & l1_orders_2(X0)) => (k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) & l1_orders_2(sK1))),
% 0.94/1.00    introduced(choice_axiom,[])).
% 0.94/1.00  
% 0.94/1.00  fof(f40,plain,(
% 0.94/1.00    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) & l1_orders_2(sK1)),
% 0.94/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f39])).
% 0.94/1.00  
% 0.94/1.00  fof(f62,plain,(
% 0.94/1.00    l1_orders_2(sK1)),
% 0.94/1.00    inference(cnf_transformation,[],[f40])).
% 0.94/1.00  
% 0.94/1.00  fof(f63,plain,(
% 0.94/1.00    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))),
% 0.94/1.00    inference(cnf_transformation,[],[f40])).
% 0.94/1.00  
% 0.94/1.00  fof(f73,plain,(
% 0.94/1.00    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 0.94/1.00    inference(definition_unfolding,[],[f63,f69,f69])).
% 0.94/1.00  
% 0.94/1.00  fof(f18,axiom,(
% 0.94/1.00    ! [X0,X1] : (l1_orders_2(X1) => v1_yellow_1(k2_funcop_1(X0,X1)))),
% 0.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.00  
% 0.94/1.00  fof(f32,plain,(
% 0.94/1.00    ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.94/1.00    inference(ennf_transformation,[],[f18])).
% 0.94/1.00  
% 0.94/1.00  fof(f58,plain,(
% 0.94/1.00    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.94/1.00    inference(cnf_transformation,[],[f32])).
% 0.94/1.00  
% 0.94/1.00  cnf(c_313,plain,
% 0.94/1.00      ( k5_yellow_1(X0_44,X1_44) = k5_yellow_1(X2_44,X3_44)
% 0.94/1.00      | X0_44 != X2_44
% 0.94/1.00      | X1_44 != X3_44 ),
% 0.94/1.00      theory(equality) ).
% 0.94/1.00  
% 0.94/1.00  cnf(c_557,plain,
% 0.94/1.00      ( k5_yellow_1(X0_44,X1_44) = k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
% 0.94/1.00      | X1_44 != k2_funcop_1(k1_xboole_0,sK1)
% 0.94/1.00      | X0_44 != k1_xboole_0 ),
% 0.94/1.00      inference(instantiation,[status(thm)],[c_313]) ).
% 0.94/1.00  
% 0.94/1.00  cnf(c_559,plain,
% 0.94/1.00      ( k5_yellow_1(k1_xboole_0,k1_xboole_0) = k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
% 0.94/1.00      | k1_xboole_0 != k2_funcop_1(k1_xboole_0,sK1)
% 0.94/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 0.94/1.00      inference(instantiation,[status(thm)],[c_557]) ).
% 0.94/1.00  
% 0.94/1.00  cnf(c_309,plain,
% 0.94/1.00      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 0.94/1.00      theory(equality) ).
% 0.94/1.00  
% 0.94/1.00  cnf(c_434,plain,
% 0.94/1.00      ( X0_45 != X1_45
% 0.94/1.00      | k6_yellow_1(k1_xboole_0,sK1) != X1_45
% 0.94/1.00      | k6_yellow_1(k1_xboole_0,sK1) = X0_45 ),
% 0.94/1.00      inference(instantiation,[status(thm)],[c_309]) ).
% 0.94/1.00  
% 0.94/1.00  cnf(c_485,plain,
% 0.94/1.00      ( X0_45 != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
% 0.94/1.00      | k6_yellow_1(k1_xboole_0,sK1) = X0_45
% 0.94/1.00      | k6_yellow_1(k1_xboole_0,sK1) != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1)) ),
% 0.94/1.00      inference(instantiation,[status(thm)],[c_434]) ).
% 0.94/1.00  
% 0.94/1.00  cnf(c_556,plain,
% 0.94/1.00      ( k5_yellow_1(X0_44,X1_44) != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
% 0.94/1.00      | k6_yellow_1(k1_xboole_0,sK1) = k5_yellow_1(X0_44,X1_44)
% 0.94/1.00      | k6_yellow_1(k1_xboole_0,sK1) != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1)) ),
% 0.94/1.00      inference(instantiation,[status(thm)],[c_485]) ).
% 0.94/1.00  
% 0.94/1.00  cnf(c_558,plain,
% 0.94/1.00      ( k5_yellow_1(k1_xboole_0,k1_xboole_0) != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
% 0.94/1.00      | k6_yellow_1(k1_xboole_0,sK1) != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
% 0.94/1.00      | k6_yellow_1(k1_xboole_0,sK1) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
% 0.94/1.00      inference(instantiation,[status(thm)],[c_556]) ).
% 0.94/1.00  
% 0.94/1.00  cnf(c_441,plain,
% 0.94/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != X0_45
% 0.94/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k6_yellow_1(X0_44,sK1)
% 0.94/1.00      | k6_yellow_1(X0_44,sK1) != X0_45 ),
% 0.94/1.00      inference(instantiation,[status(thm)],[c_309]) ).
% 0.94/1.00  
% 0.94/1.00  cnf(c_474,plain,
% 0.94/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0)
% 0.94/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k6_yellow_1(X0_44,sK1)
% 0.94/1.00      | k6_yellow_1(X0_44,sK1) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
% 0.94/1.00      inference(instantiation,[status(thm)],[c_441]) ).
% 0.94/1.00  
% 0.94/1.00  cnf(c_475,plain,
% 0.94/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0)
% 0.94/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK1)
% 0.94/1.00      | k6_yellow_1(k1_xboole_0,sK1) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
% 0.94/1.00      inference(instantiation,[status(thm)],[c_474]) ).
% 0.94/1.00  
% 0.94/1.00  cnf(c_456,plain,
% 0.94/1.00      ( X0_45 != k6_yellow_1(k1_xboole_0,sK1)
% 0.94/1.00      | k6_yellow_1(k1_xboole_0,sK1) = X0_45
% 0.94/1.00      | k6_yellow_1(k1_xboole_0,sK1) != k6_yellow_1(k1_xboole_0,sK1) ),
% 0.94/1.00      inference(instantiation,[status(thm)],[c_434]) ).
% 0.94/1.00  
% 0.94/1.00  cnf(c_465,plain,
% 0.94/1.00      ( k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1)) != k6_yellow_1(k1_xboole_0,sK1)
% 0.94/1.00      | k6_yellow_1(k1_xboole_0,sK1) = k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
% 0.94/1.00      | k6_yellow_1(k1_xboole_0,sK1) != k6_yellow_1(k1_xboole_0,sK1) ),
% 0.94/1.00      inference(instantiation,[status(thm)],[c_456]) ).
% 0.94/1.00  
% 0.94/1.00  cnf(c_422,plain,
% 0.94/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != X0_45
% 0.94/1.00      | k6_yellow_1(k1_xboole_0,sK1) != X0_45
% 0.94/1.00      | k6_yellow_1(k1_xboole_0,sK1) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
% 0.94/1.00      inference(instantiation,[status(thm)],[c_309]) ).
% 0.94/1.00  
% 0.94/1.00  cnf(c_432,plain,
% 0.94/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK1)
% 0.94/1.00      | k6_yellow_1(k1_xboole_0,sK1) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
% 0.94/1.01      | k6_yellow_1(k1_xboole_0,sK1) != k6_yellow_1(k1_xboole_0,sK1) ),
% 0.94/1.01      inference(instantiation,[status(thm)],[c_422]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_314,plain,
% 0.94/1.01      ( ~ v1_yellow_1(X0_44) | v1_yellow_1(X1_44) | X1_44 != X0_44 ),
% 0.94/1.01      theory(equality) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_417,plain,
% 0.94/1.01      ( v1_yellow_1(X0_44)
% 0.94/1.01      | ~ v1_yellow_1(k2_funcop_1(X1_44,sK1))
% 0.94/1.01      | X0_44 != k2_funcop_1(X1_44,sK1) ),
% 0.94/1.01      inference(instantiation,[status(thm)],[c_314]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_419,plain,
% 0.94/1.01      ( ~ v1_yellow_1(k2_funcop_1(k1_xboole_0,sK1))
% 0.94/1.01      | v1_yellow_1(k1_xboole_0)
% 0.94/1.01      | k1_xboole_0 != k2_funcop_1(k1_xboole_0,sK1) ),
% 0.94/1.01      inference(instantiation,[status(thm)],[c_417]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_6,plain,
% 0.94/1.01      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 0.94/1.01      inference(cnf_transformation,[],[f54]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_3,plain,
% 0.94/1.01      ( v4_relat_1(k1_xboole_0,X0) ),
% 0.94/1.01      inference(cnf_transformation,[],[f51]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_11,plain,
% 0.94/1.01      ( ~ v1_partfun1(X0,k1_xboole_0)
% 0.94/1.01      | ~ v4_relat_1(X0,k1_xboole_0)
% 0.94/1.01      | ~ v1_yellow_1(X0)
% 0.94/1.01      | ~ v1_funct_1(X0)
% 0.94/1.01      | ~ v1_relat_1(X0)
% 0.94/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,X0) ),
% 0.94/1.01      inference(cnf_transformation,[],[f72]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_183,plain,
% 0.94/1.01      ( ~ v1_partfun1(X0,k1_xboole_0)
% 0.94/1.01      | ~ v1_yellow_1(X0)
% 0.94/1.01      | ~ v1_funct_1(X0)
% 0.94/1.01      | ~ v1_relat_1(X0)
% 0.94/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,X0)
% 0.94/1.01      | k1_xboole_0 != X1
% 0.94/1.01      | k1_xboole_0 != X0 ),
% 0.94/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_11]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_184,plain,
% 0.94/1.01      ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
% 0.94/1.01      | ~ v1_yellow_1(k1_xboole_0)
% 0.94/1.01      | ~ v1_funct_1(k1_xboole_0)
% 0.94/1.01      | ~ v1_relat_1(k1_xboole_0)
% 0.94/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
% 0.94/1.01      inference(unflattening,[status(thm)],[c_183]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_5,plain,
% 0.94/1.01      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 0.94/1.01      inference(cnf_transformation,[],[f53]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_32,plain,
% 0.94/1.01      ( v1_funct_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 0.94/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_2,plain,
% 0.94/1.01      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 0.94/1.01      inference(cnf_transformation,[],[f50]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_38,plain,
% 0.94/1.01      ( v1_relat_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 0.94/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_0,plain,
% 0.94/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 0.94/1.01      inference(cnf_transformation,[],[f41]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_186,plain,
% 0.94/1.01      ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
% 0.94/1.01      | ~ v1_yellow_1(k1_xboole_0)
% 0.94/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
% 0.94/1.01      inference(global_propositional_subsumption,
% 0.94/1.01                [status(thm)],
% 0.94/1.01                [c_184,c_32,c_38,c_0]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_213,plain,
% 0.94/1.01      ( ~ v1_yellow_1(k1_xboole_0)
% 0.94/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
% 0.94/1.01      | k6_partfun1(X0) != k1_xboole_0
% 0.94/1.01      | k1_xboole_0 != X0 ),
% 0.94/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_186]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_214,plain,
% 0.94/1.01      ( ~ v1_yellow_1(k1_xboole_0)
% 0.94/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
% 0.94/1.01      | k6_partfun1(k1_xboole_0) != k1_xboole_0 ),
% 0.94/1.01      inference(unflattening,[status(thm)],[c_213]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_4,plain,
% 0.94/1.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 0.94/1.01      inference(cnf_transformation,[],[f70]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_216,plain,
% 0.94/1.01      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
% 0.94/1.01      | ~ v1_yellow_1(k1_xboole_0) ),
% 0.94/1.01      inference(global_propositional_subsumption,
% 0.94/1.01                [status(thm)],
% 0.94/1.01                [c_214,c_4]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_217,plain,
% 0.94/1.01      ( ~ v1_yellow_1(k1_xboole_0)
% 0.94/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
% 0.94/1.01      inference(renaming,[status(thm)],[c_216]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_297,plain,
% 0.94/1.01      ( ~ v1_yellow_1(k1_xboole_0)
% 0.94/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
% 0.94/1.01      inference(subtyping,[status(esa)],[c_217]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_1,plain,
% 0.94/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 0.94/1.01      inference(cnf_transformation,[],[f42]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_10,plain,
% 0.94/1.01      ( v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
% 0.94/1.01      inference(cnf_transformation,[],[f59]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_206,plain,
% 0.94/1.01      ( k2_funcop_1(k1_xboole_0,X0) != X1 | k1_xboole_0 = X1 ),
% 0.94/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_10]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_207,plain,
% 0.94/1.01      ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) ),
% 0.94/1.01      inference(unflattening,[status(thm)],[c_206]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_298,plain,
% 0.94/1.01      ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0_46) ),
% 0.94/1.01      inference(subtyping,[status(esa)],[c_207]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_331,plain,
% 0.94/1.01      ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,sK1) ),
% 0.94/1.01      inference(instantiation,[status(thm)],[c_298]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_8,plain,
% 0.94/1.01      ( ~ l1_orders_2(X0)
% 0.94/1.01      | k5_yellow_1(X1,k2_funcop_1(X1,X0)) = k6_yellow_1(X1,X0) ),
% 0.94/1.01      inference(cnf_transformation,[],[f71]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_13,negated_conjecture,
% 0.94/1.01      ( l1_orders_2(sK1) ),
% 0.94/1.01      inference(cnf_transformation,[],[f62]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_171,plain,
% 0.94/1.01      ( k5_yellow_1(X0,k2_funcop_1(X0,X1)) = k6_yellow_1(X0,X1)
% 0.94/1.01      | sK1 != X1 ),
% 0.94/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_172,plain,
% 0.94/1.01      ( k5_yellow_1(X0,k2_funcop_1(X0,sK1)) = k6_yellow_1(X0,sK1) ),
% 0.94/1.01      inference(unflattening,[status(thm)],[c_171]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_299,plain,
% 0.94/1.01      ( k5_yellow_1(X0_44,k2_funcop_1(X0_44,sK1)) = k6_yellow_1(X0_44,sK1) ),
% 0.94/1.01      inference(subtyping,[status(esa)],[c_172]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_330,plain,
% 0.94/1.01      ( k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1)) = k6_yellow_1(k1_xboole_0,sK1) ),
% 0.94/1.01      inference(instantiation,[status(thm)],[c_299]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_12,negated_conjecture,
% 0.94/1.01      ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
% 0.94/1.01      inference(cnf_transformation,[],[f73]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_303,negated_conjecture,
% 0.94/1.01      ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
% 0.94/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_306,plain,( X0_44 = X0_44 ),theory(equality) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_325,plain,
% 0.94/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 0.94/1.01      inference(instantiation,[status(thm)],[c_306]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_311,plain,
% 0.94/1.01      ( k6_yellow_1(X0_44,X0_46) = k6_yellow_1(X1_44,X0_46)
% 0.94/1.01      | X0_44 != X1_44 ),
% 0.94/1.01      theory(equality) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_318,plain,
% 0.94/1.01      ( k6_yellow_1(k1_xboole_0,sK1) = k6_yellow_1(k1_xboole_0,sK1)
% 0.94/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 0.94/1.01      inference(instantiation,[status(thm)],[c_311]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_9,plain,
% 0.94/1.01      ( v1_yellow_1(k2_funcop_1(X0,X1)) | ~ l1_orders_2(X1) ),
% 0.94/1.01      inference(cnf_transformation,[],[f58]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_162,plain,
% 0.94/1.01      ( v1_yellow_1(k2_funcop_1(X0,X1)) | sK1 != X1 ),
% 0.94/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_163,plain,
% 0.94/1.01      ( v1_yellow_1(k2_funcop_1(X0,sK1)) ),
% 0.94/1.01      inference(unflattening,[status(thm)],[c_162]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(c_165,plain,
% 0.94/1.01      ( v1_yellow_1(k2_funcop_1(k1_xboole_0,sK1)) ),
% 0.94/1.01      inference(instantiation,[status(thm)],[c_163]) ).
% 0.94/1.01  
% 0.94/1.01  cnf(contradiction,plain,
% 0.94/1.01      ( $false ),
% 0.94/1.01      inference(minisat,
% 0.94/1.01                [status(thm)],
% 0.94/1.01                [c_559,c_558,c_475,c_465,c_432,c_419,c_297,c_331,c_330,
% 0.94/1.01                 c_303,c_325,c_318,c_165]) ).
% 0.94/1.01  
% 0.94/1.01  
% 0.94/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 0.94/1.01  
% 0.94/1.01  ------                               Statistics
% 0.94/1.01  
% 0.94/1.01  ------ General
% 0.94/1.01  
% 0.94/1.01  abstr_ref_over_cycles:                  0
% 0.94/1.01  abstr_ref_under_cycles:                 0
% 0.94/1.01  gc_basic_clause_elim:                   0
% 0.94/1.01  forced_gc_time:                         0
% 0.94/1.01  parsing_time:                           0.008
% 0.94/1.01  unif_index_cands_time:                  0.
% 0.94/1.01  unif_index_add_time:                    0.
% 0.94/1.01  orderings_time:                         0.
% 0.94/1.01  out_proof_time:                         0.008
% 0.94/1.01  total_time:                             0.052
% 0.94/1.01  num_of_symbols:                         47
% 0.94/1.01  num_of_terms:                           692
% 0.94/1.01  
% 0.94/1.01  ------ Preprocessing
% 0.94/1.01  
% 0.94/1.01  num_of_splits:                          0
% 0.94/1.01  num_of_split_atoms:                     0
% 0.94/1.01  num_of_reused_defs:                     0
% 0.94/1.01  num_eq_ax_congr_red:                    5
% 0.94/1.01  num_of_sem_filtered_clauses:            1
% 0.94/1.01  num_of_subtypes:                        3
% 0.94/1.01  monotx_restored_types:                  0
% 0.94/1.01  sat_num_of_epr_types:                   0
% 0.94/1.01  sat_num_of_non_cyclic_types:            0
% 0.94/1.01  sat_guarded_non_collapsed_types:        0
% 0.94/1.01  num_pure_diseq_elim:                    0
% 0.94/1.01  simp_replaced_by:                       0
% 0.94/1.01  res_preprocessed:                       61
% 0.94/1.01  prep_upred:                             0
% 0.94/1.01  prep_unflattend:                        9
% 0.94/1.01  smt_new_axioms:                         0
% 0.94/1.01  pred_elim_cands:                        1
% 0.94/1.01  pred_elim:                              6
% 0.94/1.01  pred_elim_cl:                           6
% 0.94/1.01  pred_elim_cycles:                       8
% 0.94/1.01  merged_defs:                            0
% 0.94/1.01  merged_defs_ncl:                        0
% 0.94/1.01  bin_hyper_res:                          0
% 0.94/1.01  prep_cycles:                            4
% 0.94/1.01  pred_elim_time:                         0.003
% 0.94/1.01  splitting_time:                         0.
% 0.94/1.01  sem_filter_time:                        0.
% 0.94/1.01  monotx_time:                            0.
% 0.94/1.01  subtype_inf_time:                       0.
% 0.94/1.01  
% 0.94/1.01  ------ Problem properties
% 0.94/1.01  
% 0.94/1.01  clauses:                                8
% 0.94/1.01  conjectures:                            1
% 0.94/1.01  epr:                                    0
% 0.94/1.01  horn:                                   8
% 0.94/1.01  ground:                                 3
% 0.94/1.01  unary:                                  7
% 0.94/1.01  binary:                                 1
% 0.94/1.01  lits:                                   9
% 0.94/1.01  lits_eq:                                6
% 0.94/1.01  fd_pure:                                0
% 0.94/1.01  fd_pseudo:                              0
% 0.94/1.01  fd_cond:                                0
% 0.94/1.01  fd_pseudo_cond:                         0
% 0.94/1.01  ac_symbols:                             0
% 0.94/1.01  
% 0.94/1.01  ------ Propositional Solver
% 0.94/1.01  
% 0.94/1.01  prop_solver_calls:                      27
% 0.94/1.01  prop_fast_solver_calls:                 268
% 0.94/1.01  smt_solver_calls:                       0
% 0.94/1.01  smt_fast_solver_calls:                  0
% 0.94/1.01  prop_num_of_clauses:                    180
% 0.94/1.01  prop_preprocess_simplified:             1287
% 0.94/1.01  prop_fo_subsumed:                       3
% 0.94/1.01  prop_solver_time:                       0.
% 0.94/1.01  smt_solver_time:                        0.
% 0.94/1.01  smt_fast_solver_time:                   0.
% 0.94/1.01  prop_fast_solver_time:                  0.
% 0.94/1.01  prop_unsat_core_time:                   0.
% 0.94/1.01  
% 0.94/1.01  ------ QBF
% 0.94/1.01  
% 0.94/1.01  qbf_q_res:                              0
% 0.94/1.01  qbf_num_tautologies:                    0
% 0.94/1.01  qbf_prep_cycles:                        0
% 0.94/1.01  
% 0.94/1.01  ------ BMC1
% 0.94/1.01  
% 0.94/1.01  bmc1_current_bound:                     -1
% 0.94/1.01  bmc1_last_solved_bound:                 -1
% 0.94/1.01  bmc1_unsat_core_size:                   -1
% 0.94/1.01  bmc1_unsat_core_parents_size:           -1
% 0.94/1.01  bmc1_merge_next_fun:                    0
% 0.94/1.01  bmc1_unsat_core_clauses_time:           0.
% 0.94/1.01  
% 0.94/1.01  ------ Instantiation
% 0.94/1.01  
% 0.94/1.01  inst_num_of_clauses:                    67
% 0.94/1.01  inst_num_in_passive:                    14
% 0.94/1.01  inst_num_in_active:                     46
% 0.94/1.01  inst_num_in_unprocessed:                6
% 0.94/1.01  inst_num_of_loops:                      53
% 0.94/1.01  inst_num_of_learning_restarts:          0
% 0.94/1.01  inst_num_moves_active_passive:          2
% 0.94/1.01  inst_lit_activity:                      0
% 0.94/1.01  inst_lit_activity_moves:                0
% 0.94/1.01  inst_num_tautologies:                   0
% 0.94/1.01  inst_num_prop_implied:                  0
% 0.94/1.01  inst_num_existing_simplified:           0
% 0.94/1.01  inst_num_eq_res_simplified:             0
% 0.94/1.01  inst_num_child_elim:                    0
% 0.94/1.01  inst_num_of_dismatching_blockings:      3
% 0.94/1.01  inst_num_of_non_proper_insts:           44
% 0.94/1.01  inst_num_of_duplicates:                 0
% 0.94/1.01  inst_inst_num_from_inst_to_res:         0
% 0.94/1.01  inst_dismatching_checking_time:         0.
% 0.94/1.01  
% 0.94/1.01  ------ Resolution
% 0.94/1.01  
% 0.94/1.01  res_num_of_clauses:                     0
% 0.94/1.01  res_num_in_passive:                     0
% 0.94/1.01  res_num_in_active:                      0
% 0.94/1.01  res_num_of_loops:                       65
% 0.94/1.01  res_forward_subset_subsumed:            9
% 0.94/1.01  res_backward_subset_subsumed:           0
% 0.94/1.01  res_forward_subsumed:                   0
% 0.94/1.01  res_backward_subsumed:                  0
% 0.94/1.01  res_forward_subsumption_resolution:     0
% 0.94/1.01  res_backward_subsumption_resolution:    0
% 0.94/1.01  res_clause_to_clause_subsumption:       14
% 0.94/1.01  res_orphan_elimination:                 0
% 0.94/1.01  res_tautology_del:                      8
% 0.94/1.01  res_num_eq_res_simplified:              0
% 0.94/1.01  res_num_sel_changes:                    0
% 0.94/1.01  res_moves_from_active_to_pass:          0
% 0.94/1.01  
% 0.94/1.01  ------ Superposition
% 0.94/1.01  
% 0.94/1.01  sup_time_total:                         0.
% 0.94/1.01  sup_time_generating:                    0.
% 0.94/1.01  sup_time_sim_full:                      0.
% 0.94/1.01  sup_time_sim_immed:                     0.
% 0.94/1.01  
% 0.94/1.01  sup_num_of_clauses:                     11
% 0.94/1.01  sup_num_in_active:                      9
% 0.94/1.01  sup_num_in_passive:                     2
% 0.94/1.01  sup_num_of_loops:                       10
% 0.94/1.01  sup_fw_superposition:                   2
% 0.94/1.01  sup_bw_superposition:                   2
% 0.94/1.01  sup_immediate_simplified:               0
% 0.94/1.01  sup_given_eliminated:                   0
% 0.94/1.01  comparisons_done:                       0
% 0.94/1.01  comparisons_avoided:                    0
% 0.94/1.01  
% 0.94/1.01  ------ Simplifications
% 0.94/1.01  
% 0.94/1.01  
% 0.94/1.01  sim_fw_subset_subsumed:                 0
% 0.94/1.01  sim_bw_subset_subsumed:                 0
% 0.94/1.01  sim_fw_subsumed:                        0
% 0.94/1.01  sim_bw_subsumed:                        0
% 0.94/1.01  sim_fw_subsumption_res:                 0
% 0.94/1.01  sim_bw_subsumption_res:                 0
% 0.94/1.01  sim_tautology_del:                      0
% 0.94/1.01  sim_eq_tautology_del:                   0
% 0.94/1.01  sim_eq_res_simp:                        0
% 0.94/1.01  sim_fw_demodulated:                     0
% 0.94/1.01  sim_bw_demodulated:                     1
% 0.94/1.01  sim_light_normalised:                   0
% 0.94/1.01  sim_joinable_taut:                      0
% 0.94/1.01  sim_joinable_simp:                      0
% 0.94/1.01  sim_ac_normalised:                      0
% 0.94/1.01  sim_smt_subsumption:                    0
% 0.94/1.01  
%------------------------------------------------------------------------------
