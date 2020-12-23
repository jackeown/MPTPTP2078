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
% DateTime   : Thu Dec  3 12:20:32 EST 2020

% Result     : Theorem 1.02s
% Output     : CNFRefutation 1.02s
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

fof(f28,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f56,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f38,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(rectify,[],[f29])).

fof(f53,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f38])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f63,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f66])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f70])).

fof(f74,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f63,f71,f71])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f19,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f20,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(definition_unfolding,[],[f59,f62])).

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

fof(f37,plain,(
    ? [X0] :
      ( k6_yellow_1(k1_xboole_0,X0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f41,plain,
    ( ? [X0] :
        ( k6_yellow_1(k1_xboole_0,X0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
        & l1_orders_2(X0) )
   => ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
    & l1_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f41])).

fof(f64,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f65,f71,f71])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => v1_yellow_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f34])).

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
    inference(cnf_transformation,[],[f56])).

cnf(c_3,plain,
    ( v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_11,plain,
    ( ~ v1_partfun1(X0,k1_xboole_0)
    | ~ v4_relat_1(X0,k1_xboole_0)
    | ~ v1_yellow_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f74])).

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
    inference(cnf_transformation,[],[f55])).

cnf(c_32,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_38,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

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
    inference(cnf_transformation,[],[f72])).

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
    inference(cnf_transformation,[],[f44])).

cnf(c_10,plain,
    ( v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f61])).

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
    inference(cnf_transformation,[],[f73])).

cnf(c_13,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f64])).

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
    inference(cnf_transformation,[],[f75])).

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
    inference(cnf_transformation,[],[f60])).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:56:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.02/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.02/1.00  
% 1.02/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.02/1.00  
% 1.02/1.00  ------  iProver source info
% 1.02/1.00  
% 1.02/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.02/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.02/1.00  git: non_committed_changes: false
% 1.02/1.00  git: last_make_outside_of_git: false
% 1.02/1.00  
% 1.02/1.00  ------ 
% 1.02/1.00  
% 1.02/1.00  ------ Input Options
% 1.02/1.00  
% 1.02/1.00  --out_options                           all
% 1.02/1.00  --tptp_safe_out                         true
% 1.02/1.00  --problem_path                          ""
% 1.02/1.00  --include_path                          ""
% 1.02/1.00  --clausifier                            res/vclausify_rel
% 1.02/1.00  --clausifier_options                    --mode clausify
% 1.02/1.00  --stdin                                 false
% 1.02/1.00  --stats_out                             all
% 1.02/1.00  
% 1.02/1.00  ------ General Options
% 1.02/1.00  
% 1.02/1.00  --fof                                   false
% 1.02/1.00  --time_out_real                         305.
% 1.02/1.00  --time_out_virtual                      -1.
% 1.02/1.00  --symbol_type_check                     false
% 1.02/1.00  --clausify_out                          false
% 1.02/1.00  --sig_cnt_out                           false
% 1.02/1.00  --trig_cnt_out                          false
% 1.02/1.00  --trig_cnt_out_tolerance                1.
% 1.02/1.00  --trig_cnt_out_sk_spl                   false
% 1.02/1.00  --abstr_cl_out                          false
% 1.02/1.00  
% 1.02/1.00  ------ Global Options
% 1.02/1.00  
% 1.02/1.00  --schedule                              default
% 1.02/1.00  --add_important_lit                     false
% 1.02/1.00  --prop_solver_per_cl                    1000
% 1.02/1.00  --min_unsat_core                        false
% 1.02/1.00  --soft_assumptions                      false
% 1.02/1.00  --soft_lemma_size                       3
% 1.02/1.00  --prop_impl_unit_size                   0
% 1.02/1.00  --prop_impl_unit                        []
% 1.02/1.00  --share_sel_clauses                     true
% 1.02/1.00  --reset_solvers                         false
% 1.02/1.00  --bc_imp_inh                            [conj_cone]
% 1.02/1.00  --conj_cone_tolerance                   3.
% 1.02/1.00  --extra_neg_conj                        none
% 1.02/1.00  --large_theory_mode                     true
% 1.02/1.00  --prolific_symb_bound                   200
% 1.02/1.00  --lt_threshold                          2000
% 1.02/1.00  --clause_weak_htbl                      true
% 1.02/1.00  --gc_record_bc_elim                     false
% 1.02/1.00  
% 1.02/1.00  ------ Preprocessing Options
% 1.02/1.00  
% 1.02/1.00  --preprocessing_flag                    true
% 1.02/1.00  --time_out_prep_mult                    0.1
% 1.02/1.00  --splitting_mode                        input
% 1.02/1.00  --splitting_grd                         true
% 1.02/1.00  --splitting_cvd                         false
% 1.02/1.00  --splitting_cvd_svl                     false
% 1.02/1.00  --splitting_nvd                         32
% 1.02/1.00  --sub_typing                            true
% 1.02/1.00  --prep_gs_sim                           true
% 1.02/1.00  --prep_unflatten                        true
% 1.02/1.00  --prep_res_sim                          true
% 1.02/1.00  --prep_upred                            true
% 1.02/1.00  --prep_sem_filter                       exhaustive
% 1.02/1.00  --prep_sem_filter_out                   false
% 1.02/1.00  --pred_elim                             true
% 1.02/1.00  --res_sim_input                         true
% 1.02/1.00  --eq_ax_congr_red                       true
% 1.02/1.00  --pure_diseq_elim                       true
% 1.02/1.00  --brand_transform                       false
% 1.02/1.00  --non_eq_to_eq                          false
% 1.02/1.00  --prep_def_merge                        true
% 1.02/1.00  --prep_def_merge_prop_impl              false
% 1.02/1.00  --prep_def_merge_mbd                    true
% 1.02/1.00  --prep_def_merge_tr_red                 false
% 1.02/1.00  --prep_def_merge_tr_cl                  false
% 1.02/1.00  --smt_preprocessing                     true
% 1.02/1.00  --smt_ac_axioms                         fast
% 1.02/1.00  --preprocessed_out                      false
% 1.02/1.00  --preprocessed_stats                    false
% 1.02/1.00  
% 1.02/1.00  ------ Abstraction refinement Options
% 1.02/1.00  
% 1.02/1.00  --abstr_ref                             []
% 1.02/1.00  --abstr_ref_prep                        false
% 1.02/1.00  --abstr_ref_until_sat                   false
% 1.02/1.00  --abstr_ref_sig_restrict                funpre
% 1.02/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.02/1.00  --abstr_ref_under                       []
% 1.02/1.00  
% 1.02/1.00  ------ SAT Options
% 1.02/1.00  
% 1.02/1.00  --sat_mode                              false
% 1.02/1.00  --sat_fm_restart_options                ""
% 1.02/1.00  --sat_gr_def                            false
% 1.02/1.00  --sat_epr_types                         true
% 1.02/1.00  --sat_non_cyclic_types                  false
% 1.02/1.00  --sat_finite_models                     false
% 1.02/1.00  --sat_fm_lemmas                         false
% 1.02/1.00  --sat_fm_prep                           false
% 1.02/1.01  --sat_fm_uc_incr                        true
% 1.02/1.01  --sat_out_model                         small
% 1.02/1.01  --sat_out_clauses                       false
% 1.02/1.01  
% 1.02/1.01  ------ QBF Options
% 1.02/1.01  
% 1.02/1.01  --qbf_mode                              false
% 1.02/1.01  --qbf_elim_univ                         false
% 1.02/1.01  --qbf_dom_inst                          none
% 1.02/1.01  --qbf_dom_pre_inst                      false
% 1.02/1.01  --qbf_sk_in                             false
% 1.02/1.01  --qbf_pred_elim                         true
% 1.02/1.01  --qbf_split                             512
% 1.02/1.01  
% 1.02/1.01  ------ BMC1 Options
% 1.02/1.01  
% 1.02/1.01  --bmc1_incremental                      false
% 1.02/1.01  --bmc1_axioms                           reachable_all
% 1.02/1.01  --bmc1_min_bound                        0
% 1.02/1.01  --bmc1_max_bound                        -1
% 1.02/1.01  --bmc1_max_bound_default                -1
% 1.02/1.01  --bmc1_symbol_reachability              true
% 1.02/1.01  --bmc1_property_lemmas                  false
% 1.02/1.01  --bmc1_k_induction                      false
% 1.02/1.01  --bmc1_non_equiv_states                 false
% 1.02/1.01  --bmc1_deadlock                         false
% 1.02/1.01  --bmc1_ucm                              false
% 1.02/1.01  --bmc1_add_unsat_core                   none
% 1.02/1.01  --bmc1_unsat_core_children              false
% 1.02/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.02/1.01  --bmc1_out_stat                         full
% 1.02/1.01  --bmc1_ground_init                      false
% 1.02/1.01  --bmc1_pre_inst_next_state              false
% 1.02/1.01  --bmc1_pre_inst_state                   false
% 1.02/1.01  --bmc1_pre_inst_reach_state             false
% 1.02/1.01  --bmc1_out_unsat_core                   false
% 1.02/1.01  --bmc1_aig_witness_out                  false
% 1.02/1.01  --bmc1_verbose                          false
% 1.02/1.01  --bmc1_dump_clauses_tptp                false
% 1.02/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.02/1.01  --bmc1_dump_file                        -
% 1.02/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.02/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.02/1.01  --bmc1_ucm_extend_mode                  1
% 1.02/1.01  --bmc1_ucm_init_mode                    2
% 1.02/1.01  --bmc1_ucm_cone_mode                    none
% 1.02/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.02/1.01  --bmc1_ucm_relax_model                  4
% 1.02/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.02/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.02/1.01  --bmc1_ucm_layered_model                none
% 1.02/1.01  --bmc1_ucm_max_lemma_size               10
% 1.02/1.01  
% 1.02/1.01  ------ AIG Options
% 1.02/1.01  
% 1.02/1.01  --aig_mode                              false
% 1.02/1.01  
% 1.02/1.01  ------ Instantiation Options
% 1.02/1.01  
% 1.02/1.01  --instantiation_flag                    true
% 1.02/1.01  --inst_sos_flag                         false
% 1.02/1.01  --inst_sos_phase                        true
% 1.02/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.02/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.02/1.01  --inst_lit_sel_side                     num_symb
% 1.02/1.01  --inst_solver_per_active                1400
% 1.02/1.01  --inst_solver_calls_frac                1.
% 1.02/1.01  --inst_passive_queue_type               priority_queues
% 1.02/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.02/1.01  --inst_passive_queues_freq              [25;2]
% 1.02/1.01  --inst_dismatching                      true
% 1.02/1.01  --inst_eager_unprocessed_to_passive     true
% 1.02/1.01  --inst_prop_sim_given                   true
% 1.02/1.01  --inst_prop_sim_new                     false
% 1.02/1.01  --inst_subs_new                         false
% 1.02/1.01  --inst_eq_res_simp                      false
% 1.02/1.01  --inst_subs_given                       false
% 1.02/1.01  --inst_orphan_elimination               true
% 1.02/1.01  --inst_learning_loop_flag               true
% 1.02/1.01  --inst_learning_start                   3000
% 1.02/1.01  --inst_learning_factor                  2
% 1.02/1.01  --inst_start_prop_sim_after_learn       3
% 1.02/1.01  --inst_sel_renew                        solver
% 1.02/1.01  --inst_lit_activity_flag                true
% 1.02/1.01  --inst_restr_to_given                   false
% 1.02/1.01  --inst_activity_threshold               500
% 1.02/1.01  --inst_out_proof                        true
% 1.02/1.01  
% 1.02/1.01  ------ Resolution Options
% 1.02/1.01  
% 1.02/1.01  --resolution_flag                       true
% 1.02/1.01  --res_lit_sel                           adaptive
% 1.02/1.01  --res_lit_sel_side                      none
% 1.02/1.01  --res_ordering                          kbo
% 1.02/1.01  --res_to_prop_solver                    active
% 1.02/1.01  --res_prop_simpl_new                    false
% 1.02/1.01  --res_prop_simpl_given                  true
% 1.02/1.01  --res_passive_queue_type                priority_queues
% 1.02/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.02/1.01  --res_passive_queues_freq               [15;5]
% 1.02/1.01  --res_forward_subs                      full
% 1.02/1.01  --res_backward_subs                     full
% 1.02/1.01  --res_forward_subs_resolution           true
% 1.02/1.01  --res_backward_subs_resolution          true
% 1.02/1.01  --res_orphan_elimination                true
% 1.02/1.01  --res_time_limit                        2.
% 1.02/1.01  --res_out_proof                         true
% 1.02/1.01  
% 1.02/1.01  ------ Superposition Options
% 1.02/1.01  
% 1.02/1.01  --superposition_flag                    true
% 1.02/1.01  --sup_passive_queue_type                priority_queues
% 1.02/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.02/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.02/1.01  --demod_completeness_check              fast
% 1.02/1.01  --demod_use_ground                      true
% 1.02/1.01  --sup_to_prop_solver                    passive
% 1.02/1.01  --sup_prop_simpl_new                    true
% 1.02/1.01  --sup_prop_simpl_given                  true
% 1.02/1.01  --sup_fun_splitting                     false
% 1.02/1.01  --sup_smt_interval                      50000
% 1.02/1.01  
% 1.02/1.01  ------ Superposition Simplification Setup
% 1.02/1.01  
% 1.02/1.01  --sup_indices_passive                   []
% 1.02/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.02/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.02/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.02/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.02/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.02/1.01  --sup_full_bw                           [BwDemod]
% 1.02/1.01  --sup_immed_triv                        [TrivRules]
% 1.02/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.02/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.02/1.01  --sup_immed_bw_main                     []
% 1.02/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.02/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.02/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.02/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.02/1.01  
% 1.02/1.01  ------ Combination Options
% 1.02/1.01  
% 1.02/1.01  --comb_res_mult                         3
% 1.02/1.01  --comb_sup_mult                         2
% 1.02/1.01  --comb_inst_mult                        10
% 1.02/1.01  
% 1.02/1.01  ------ Debug Options
% 1.02/1.01  
% 1.02/1.01  --dbg_backtrace                         false
% 1.02/1.01  --dbg_dump_prop_clauses                 false
% 1.02/1.01  --dbg_dump_prop_clauses_file            -
% 1.02/1.01  --dbg_out_stat                          false
% 1.02/1.01  ------ Parsing...
% 1.02/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.02/1.01  
% 1.02/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.02/1.01  
% 1.02/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.02/1.01  
% 1.02/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.02/1.01  ------ Proving...
% 1.02/1.01  ------ Problem Properties 
% 1.02/1.01  
% 1.02/1.01  
% 1.02/1.01  clauses                                 8
% 1.02/1.01  conjectures                             1
% 1.02/1.01  EPR                                     0
% 1.02/1.01  Horn                                    8
% 1.02/1.01  unary                                   7
% 1.02/1.01  binary                                  1
% 1.02/1.01  lits                                    9
% 1.02/1.01  lits eq                                 6
% 1.02/1.01  fd_pure                                 0
% 1.02/1.01  fd_pseudo                               0
% 1.02/1.01  fd_cond                                 0
% 1.02/1.01  fd_pseudo_cond                          0
% 1.02/1.01  AC symbols                              0
% 1.02/1.01  
% 1.02/1.01  ------ Schedule dynamic 5 is on 
% 1.02/1.01  
% 1.02/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.02/1.01  
% 1.02/1.01  
% 1.02/1.01  ------ 
% 1.02/1.01  Current options:
% 1.02/1.01  ------ 
% 1.02/1.01  
% 1.02/1.01  ------ Input Options
% 1.02/1.01  
% 1.02/1.01  --out_options                           all
% 1.02/1.01  --tptp_safe_out                         true
% 1.02/1.01  --problem_path                          ""
% 1.02/1.01  --include_path                          ""
% 1.02/1.01  --clausifier                            res/vclausify_rel
% 1.02/1.01  --clausifier_options                    --mode clausify
% 1.02/1.01  --stdin                                 false
% 1.02/1.01  --stats_out                             all
% 1.02/1.01  
% 1.02/1.01  ------ General Options
% 1.02/1.01  
% 1.02/1.01  --fof                                   false
% 1.02/1.01  --time_out_real                         305.
% 1.02/1.01  --time_out_virtual                      -1.
% 1.02/1.01  --symbol_type_check                     false
% 1.02/1.01  --clausify_out                          false
% 1.02/1.01  --sig_cnt_out                           false
% 1.02/1.01  --trig_cnt_out                          false
% 1.02/1.01  --trig_cnt_out_tolerance                1.
% 1.02/1.01  --trig_cnt_out_sk_spl                   false
% 1.02/1.01  --abstr_cl_out                          false
% 1.02/1.01  
% 1.02/1.01  ------ Global Options
% 1.02/1.01  
% 1.02/1.01  --schedule                              default
% 1.02/1.01  --add_important_lit                     false
% 1.02/1.01  --prop_solver_per_cl                    1000
% 1.02/1.01  --min_unsat_core                        false
% 1.02/1.01  --soft_assumptions                      false
% 1.02/1.01  --soft_lemma_size                       3
% 1.02/1.01  --prop_impl_unit_size                   0
% 1.02/1.01  --prop_impl_unit                        []
% 1.02/1.01  --share_sel_clauses                     true
% 1.02/1.01  --reset_solvers                         false
% 1.02/1.01  --bc_imp_inh                            [conj_cone]
% 1.02/1.01  --conj_cone_tolerance                   3.
% 1.02/1.01  --extra_neg_conj                        none
% 1.02/1.01  --large_theory_mode                     true
% 1.02/1.01  --prolific_symb_bound                   200
% 1.02/1.01  --lt_threshold                          2000
% 1.02/1.01  --clause_weak_htbl                      true
% 1.02/1.01  --gc_record_bc_elim                     false
% 1.02/1.01  
% 1.02/1.01  ------ Preprocessing Options
% 1.02/1.01  
% 1.02/1.01  --preprocessing_flag                    true
% 1.02/1.01  --time_out_prep_mult                    0.1
% 1.02/1.01  --splitting_mode                        input
% 1.02/1.01  --splitting_grd                         true
% 1.02/1.01  --splitting_cvd                         false
% 1.02/1.01  --splitting_cvd_svl                     false
% 1.02/1.01  --splitting_nvd                         32
% 1.02/1.01  --sub_typing                            true
% 1.02/1.01  --prep_gs_sim                           true
% 1.02/1.01  --prep_unflatten                        true
% 1.02/1.01  --prep_res_sim                          true
% 1.02/1.01  --prep_upred                            true
% 1.02/1.01  --prep_sem_filter                       exhaustive
% 1.02/1.01  --prep_sem_filter_out                   false
% 1.02/1.01  --pred_elim                             true
% 1.02/1.01  --res_sim_input                         true
% 1.02/1.01  --eq_ax_congr_red                       true
% 1.02/1.01  --pure_diseq_elim                       true
% 1.02/1.01  --brand_transform                       false
% 1.02/1.01  --non_eq_to_eq                          false
% 1.02/1.01  --prep_def_merge                        true
% 1.02/1.01  --prep_def_merge_prop_impl              false
% 1.02/1.01  --prep_def_merge_mbd                    true
% 1.02/1.01  --prep_def_merge_tr_red                 false
% 1.02/1.01  --prep_def_merge_tr_cl                  false
% 1.02/1.01  --smt_preprocessing                     true
% 1.02/1.01  --smt_ac_axioms                         fast
% 1.02/1.01  --preprocessed_out                      false
% 1.02/1.01  --preprocessed_stats                    false
% 1.02/1.01  
% 1.02/1.01  ------ Abstraction refinement Options
% 1.02/1.01  
% 1.02/1.01  --abstr_ref                             []
% 1.02/1.01  --abstr_ref_prep                        false
% 1.02/1.01  --abstr_ref_until_sat                   false
% 1.02/1.01  --abstr_ref_sig_restrict                funpre
% 1.02/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.02/1.01  --abstr_ref_under                       []
% 1.02/1.01  
% 1.02/1.01  ------ SAT Options
% 1.02/1.01  
% 1.02/1.01  --sat_mode                              false
% 1.02/1.01  --sat_fm_restart_options                ""
% 1.02/1.01  --sat_gr_def                            false
% 1.02/1.01  --sat_epr_types                         true
% 1.02/1.01  --sat_non_cyclic_types                  false
% 1.02/1.01  --sat_finite_models                     false
% 1.02/1.01  --sat_fm_lemmas                         false
% 1.02/1.01  --sat_fm_prep                           false
% 1.02/1.01  --sat_fm_uc_incr                        true
% 1.02/1.01  --sat_out_model                         small
% 1.02/1.01  --sat_out_clauses                       false
% 1.02/1.01  
% 1.02/1.01  ------ QBF Options
% 1.02/1.01  
% 1.02/1.01  --qbf_mode                              false
% 1.02/1.01  --qbf_elim_univ                         false
% 1.02/1.01  --qbf_dom_inst                          none
% 1.02/1.01  --qbf_dom_pre_inst                      false
% 1.02/1.01  --qbf_sk_in                             false
% 1.02/1.01  --qbf_pred_elim                         true
% 1.02/1.01  --qbf_split                             512
% 1.02/1.01  
% 1.02/1.01  ------ BMC1 Options
% 1.02/1.01  
% 1.02/1.01  --bmc1_incremental                      false
% 1.02/1.01  --bmc1_axioms                           reachable_all
% 1.02/1.01  --bmc1_min_bound                        0
% 1.02/1.01  --bmc1_max_bound                        -1
% 1.02/1.01  --bmc1_max_bound_default                -1
% 1.02/1.01  --bmc1_symbol_reachability              true
% 1.02/1.01  --bmc1_property_lemmas                  false
% 1.02/1.01  --bmc1_k_induction                      false
% 1.02/1.01  --bmc1_non_equiv_states                 false
% 1.02/1.01  --bmc1_deadlock                         false
% 1.02/1.01  --bmc1_ucm                              false
% 1.02/1.01  --bmc1_add_unsat_core                   none
% 1.02/1.01  --bmc1_unsat_core_children              false
% 1.02/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.02/1.01  --bmc1_out_stat                         full
% 1.02/1.01  --bmc1_ground_init                      false
% 1.02/1.01  --bmc1_pre_inst_next_state              false
% 1.02/1.01  --bmc1_pre_inst_state                   false
% 1.02/1.01  --bmc1_pre_inst_reach_state             false
% 1.02/1.01  --bmc1_out_unsat_core                   false
% 1.02/1.01  --bmc1_aig_witness_out                  false
% 1.02/1.01  --bmc1_verbose                          false
% 1.02/1.01  --bmc1_dump_clauses_tptp                false
% 1.02/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.02/1.01  --bmc1_dump_file                        -
% 1.02/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.02/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.02/1.01  --bmc1_ucm_extend_mode                  1
% 1.02/1.01  --bmc1_ucm_init_mode                    2
% 1.02/1.01  --bmc1_ucm_cone_mode                    none
% 1.02/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.02/1.01  --bmc1_ucm_relax_model                  4
% 1.02/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.02/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.02/1.01  --bmc1_ucm_layered_model                none
% 1.02/1.01  --bmc1_ucm_max_lemma_size               10
% 1.02/1.01  
% 1.02/1.01  ------ AIG Options
% 1.02/1.01  
% 1.02/1.01  --aig_mode                              false
% 1.02/1.01  
% 1.02/1.01  ------ Instantiation Options
% 1.02/1.01  
% 1.02/1.01  --instantiation_flag                    true
% 1.02/1.01  --inst_sos_flag                         false
% 1.02/1.01  --inst_sos_phase                        true
% 1.02/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.02/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.02/1.01  --inst_lit_sel_side                     none
% 1.02/1.01  --inst_solver_per_active                1400
% 1.02/1.01  --inst_solver_calls_frac                1.
% 1.02/1.01  --inst_passive_queue_type               priority_queues
% 1.02/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.02/1.01  --inst_passive_queues_freq              [25;2]
% 1.02/1.01  --inst_dismatching                      true
% 1.02/1.01  --inst_eager_unprocessed_to_passive     true
% 1.02/1.01  --inst_prop_sim_given                   true
% 1.02/1.01  --inst_prop_sim_new                     false
% 1.02/1.01  --inst_subs_new                         false
% 1.02/1.01  --inst_eq_res_simp                      false
% 1.02/1.01  --inst_subs_given                       false
% 1.02/1.01  --inst_orphan_elimination               true
% 1.02/1.01  --inst_learning_loop_flag               true
% 1.02/1.01  --inst_learning_start                   3000
% 1.02/1.01  --inst_learning_factor                  2
% 1.02/1.01  --inst_start_prop_sim_after_learn       3
% 1.02/1.01  --inst_sel_renew                        solver
% 1.02/1.01  --inst_lit_activity_flag                true
% 1.02/1.01  --inst_restr_to_given                   false
% 1.02/1.01  --inst_activity_threshold               500
% 1.02/1.01  --inst_out_proof                        true
% 1.02/1.01  
% 1.02/1.01  ------ Resolution Options
% 1.02/1.01  
% 1.02/1.01  --resolution_flag                       false
% 1.02/1.01  --res_lit_sel                           adaptive
% 1.02/1.01  --res_lit_sel_side                      none
% 1.02/1.01  --res_ordering                          kbo
% 1.02/1.01  --res_to_prop_solver                    active
% 1.02/1.01  --res_prop_simpl_new                    false
% 1.02/1.01  --res_prop_simpl_given                  true
% 1.02/1.01  --res_passive_queue_type                priority_queues
% 1.02/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.02/1.01  --res_passive_queues_freq               [15;5]
% 1.02/1.01  --res_forward_subs                      full
% 1.02/1.01  --res_backward_subs                     full
% 1.02/1.01  --res_forward_subs_resolution           true
% 1.02/1.01  --res_backward_subs_resolution          true
% 1.02/1.01  --res_orphan_elimination                true
% 1.02/1.01  --res_time_limit                        2.
% 1.02/1.01  --res_out_proof                         true
% 1.02/1.01  
% 1.02/1.01  ------ Superposition Options
% 1.02/1.01  
% 1.02/1.01  --superposition_flag                    true
% 1.02/1.01  --sup_passive_queue_type                priority_queues
% 1.02/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.02/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.02/1.01  --demod_completeness_check              fast
% 1.02/1.01  --demod_use_ground                      true
% 1.02/1.01  --sup_to_prop_solver                    passive
% 1.02/1.01  --sup_prop_simpl_new                    true
% 1.02/1.01  --sup_prop_simpl_given                  true
% 1.02/1.01  --sup_fun_splitting                     false
% 1.02/1.01  --sup_smt_interval                      50000
% 1.02/1.01  
% 1.02/1.01  ------ Superposition Simplification Setup
% 1.02/1.01  
% 1.02/1.01  --sup_indices_passive                   []
% 1.02/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.02/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.02/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.02/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.02/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.02/1.01  --sup_full_bw                           [BwDemod]
% 1.02/1.01  --sup_immed_triv                        [TrivRules]
% 1.02/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.02/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.02/1.01  --sup_immed_bw_main                     []
% 1.02/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.02/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.02/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.02/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.02/1.01  
% 1.02/1.01  ------ Combination Options
% 1.02/1.01  
% 1.02/1.01  --comb_res_mult                         3
% 1.02/1.01  --comb_sup_mult                         2
% 1.02/1.01  --comb_inst_mult                        10
% 1.02/1.01  
% 1.02/1.01  ------ Debug Options
% 1.02/1.01  
% 1.02/1.01  --dbg_backtrace                         false
% 1.02/1.01  --dbg_dump_prop_clauses                 false
% 1.02/1.01  --dbg_dump_prop_clauses_file            -
% 1.02/1.01  --dbg_out_stat                          false
% 1.02/1.01  
% 1.02/1.01  
% 1.02/1.01  
% 1.02/1.01  
% 1.02/1.01  ------ Proving...
% 1.02/1.01  
% 1.02/1.01  
% 1.02/1.01  % SZS status Theorem for theBenchmark.p
% 1.02/1.01  
% 1.02/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.02/1.01  
% 1.02/1.01  fof(f14,axiom,(
% 1.02/1.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f28,plain,(
% 1.02/1.01    ! [X0] : v1_partfun1(k6_partfun1(X0),X0)),
% 1.02/1.01    inference(pure_predicate_removal,[],[f14])).
% 1.02/1.01  
% 1.02/1.01  fof(f56,plain,(
% 1.02/1.01    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f28])).
% 1.02/1.01  
% 1.02/1.01  fof(f11,axiom,(
% 1.02/1.01    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f29,plain,(
% 1.02/1.01    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0)),
% 1.02/1.01    inference(pure_predicate_removal,[],[f11])).
% 1.02/1.01  
% 1.02/1.01  fof(f38,plain,(
% 1.02/1.01    ! [X0] : v4_relat_1(k1_xboole_0,X0)),
% 1.02/1.01    inference(rectify,[],[f29])).
% 1.02/1.01  
% 1.02/1.01  fof(f53,plain,(
% 1.02/1.01    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f38])).
% 1.02/1.01  
% 1.02/1.01  fof(f21,axiom,(
% 1.02/1.01    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f35,plain,(
% 1.02/1.01    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 1.02/1.01    inference(ennf_transformation,[],[f21])).
% 1.02/1.01  
% 1.02/1.01  fof(f36,plain,(
% 1.02/1.01    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.02/1.01    inference(flattening,[],[f35])).
% 1.02/1.01  
% 1.02/1.01  fof(f63,plain,(
% 1.02/1.01    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f36])).
% 1.02/1.01  
% 1.02/1.01  fof(f3,axiom,(
% 1.02/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f45,plain,(
% 1.02/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f3])).
% 1.02/1.01  
% 1.02/1.01  fof(f4,axiom,(
% 1.02/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f46,plain,(
% 1.02/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f4])).
% 1.02/1.01  
% 1.02/1.01  fof(f5,axiom,(
% 1.02/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f47,plain,(
% 1.02/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f5])).
% 1.02/1.01  
% 1.02/1.01  fof(f6,axiom,(
% 1.02/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f48,plain,(
% 1.02/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f6])).
% 1.02/1.01  
% 1.02/1.01  fof(f7,axiom,(
% 1.02/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f49,plain,(
% 1.02/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f7])).
% 1.02/1.01  
% 1.02/1.01  fof(f8,axiom,(
% 1.02/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f50,plain,(
% 1.02/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f8])).
% 1.02/1.01  
% 1.02/1.01  fof(f9,axiom,(
% 1.02/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f51,plain,(
% 1.02/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f9])).
% 1.02/1.01  
% 1.02/1.01  fof(f66,plain,(
% 1.02/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.02/1.01    inference(definition_unfolding,[],[f50,f51])).
% 1.02/1.01  
% 1.02/1.01  fof(f67,plain,(
% 1.02/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.02/1.01    inference(definition_unfolding,[],[f49,f66])).
% 1.02/1.01  
% 1.02/1.01  fof(f68,plain,(
% 1.02/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.02/1.01    inference(definition_unfolding,[],[f48,f67])).
% 1.02/1.01  
% 1.02/1.01  fof(f69,plain,(
% 1.02/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.02/1.01    inference(definition_unfolding,[],[f47,f68])).
% 1.02/1.01  
% 1.02/1.01  fof(f70,plain,(
% 1.02/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.02/1.01    inference(definition_unfolding,[],[f46,f69])).
% 1.02/1.01  
% 1.02/1.01  fof(f71,plain,(
% 1.02/1.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.02/1.01    inference(definition_unfolding,[],[f45,f70])).
% 1.02/1.01  
% 1.02/1.01  fof(f74,plain,(
% 1.02/1.01    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.02/1.01    inference(definition_unfolding,[],[f63,f71,f71])).
% 1.02/1.01  
% 1.02/1.01  fof(f13,axiom,(
% 1.02/1.01    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f32,plain,(
% 1.02/1.01    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 1.02/1.01    inference(ennf_transformation,[],[f13])).
% 1.02/1.01  
% 1.02/1.01  fof(f55,plain,(
% 1.02/1.01    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f32])).
% 1.02/1.01  
% 1.02/1.01  fof(f10,axiom,(
% 1.02/1.01    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f31,plain,(
% 1.02/1.01    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.02/1.01    inference(ennf_transformation,[],[f10])).
% 1.02/1.01  
% 1.02/1.01  fof(f52,plain,(
% 1.02/1.01    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f31])).
% 1.02/1.01  
% 1.02/1.01  fof(f1,axiom,(
% 1.02/1.01    v1_xboole_0(k1_xboole_0)),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f43,plain,(
% 1.02/1.01    v1_xboole_0(k1_xboole_0)),
% 1.02/1.01    inference(cnf_transformation,[],[f1])).
% 1.02/1.01  
% 1.02/1.01  fof(f12,axiom,(
% 1.02/1.01    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f54,plain,(
% 1.02/1.01    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.02/1.01    inference(cnf_transformation,[],[f12])).
% 1.02/1.01  
% 1.02/1.01  fof(f15,axiom,(
% 1.02/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f57,plain,(
% 1.02/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f15])).
% 1.02/1.01  
% 1.02/1.01  fof(f72,plain,(
% 1.02/1.01    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.02/1.01    inference(definition_unfolding,[],[f54,f57])).
% 1.02/1.01  
% 1.02/1.01  fof(f2,axiom,(
% 1.02/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f30,plain,(
% 1.02/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.02/1.01    inference(ennf_transformation,[],[f2])).
% 1.02/1.01  
% 1.02/1.01  fof(f44,plain,(
% 1.02/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f30])).
% 1.02/1.01  
% 1.02/1.01  fof(f19,axiom,(
% 1.02/1.01    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f61,plain,(
% 1.02/1.01    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 1.02/1.01    inference(cnf_transformation,[],[f19])).
% 1.02/1.01  
% 1.02/1.01  fof(f17,axiom,(
% 1.02/1.01    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f33,plain,(
% 1.02/1.01    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 1.02/1.01    inference(ennf_transformation,[],[f17])).
% 1.02/1.01  
% 1.02/1.01  fof(f59,plain,(
% 1.02/1.01    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f33])).
% 1.02/1.01  
% 1.02/1.01  fof(f20,axiom,(
% 1.02/1.01    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f62,plain,(
% 1.02/1.01    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f20])).
% 1.02/1.01  
% 1.02/1.01  fof(f73,plain,(
% 1.02/1.01    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 1.02/1.01    inference(definition_unfolding,[],[f59,f62])).
% 1.02/1.01  
% 1.02/1.01  fof(f22,conjecture,(
% 1.02/1.01    ! [X0] : (l1_orders_2(X0) => k6_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f23,negated_conjecture,(
% 1.02/1.01    ~! [X0] : (l1_orders_2(X0) => k6_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 1.02/1.01    inference(negated_conjecture,[],[f22])).
% 1.02/1.01  
% 1.02/1.01  fof(f37,plain,(
% 1.02/1.01    ? [X0] : (k6_yellow_1(k1_xboole_0,X0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) & l1_orders_2(X0))),
% 1.02/1.01    inference(ennf_transformation,[],[f23])).
% 1.02/1.01  
% 1.02/1.01  fof(f41,plain,(
% 1.02/1.01    ? [X0] : (k6_yellow_1(k1_xboole_0,X0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) & l1_orders_2(X0)) => (k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) & l1_orders_2(sK1))),
% 1.02/1.01    introduced(choice_axiom,[])).
% 1.02/1.01  
% 1.02/1.01  fof(f42,plain,(
% 1.02/1.01    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) & l1_orders_2(sK1)),
% 1.02/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f41])).
% 1.02/1.01  
% 1.02/1.01  fof(f64,plain,(
% 1.02/1.01    l1_orders_2(sK1)),
% 1.02/1.01    inference(cnf_transformation,[],[f42])).
% 1.02/1.01  
% 1.02/1.01  fof(f65,plain,(
% 1.02/1.01    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))),
% 1.02/1.01    inference(cnf_transformation,[],[f42])).
% 1.02/1.01  
% 1.02/1.01  fof(f75,plain,(
% 1.02/1.01    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 1.02/1.01    inference(definition_unfolding,[],[f65,f71,f71])).
% 1.02/1.01  
% 1.02/1.01  fof(f18,axiom,(
% 1.02/1.01    ! [X0,X1] : (l1_orders_2(X1) => v1_yellow_1(k2_funcop_1(X0,X1)))),
% 1.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.02/1.01  
% 1.02/1.01  fof(f34,plain,(
% 1.02/1.01    ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 1.02/1.01    inference(ennf_transformation,[],[f18])).
% 1.02/1.01  
% 1.02/1.01  fof(f60,plain,(
% 1.02/1.01    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 1.02/1.01    inference(cnf_transformation,[],[f34])).
% 1.02/1.01  
% 1.02/1.01  cnf(c_313,plain,
% 1.02/1.01      ( k5_yellow_1(X0_44,X1_44) = k5_yellow_1(X2_44,X3_44)
% 1.02/1.01      | X0_44 != X2_44
% 1.02/1.01      | X1_44 != X3_44 ),
% 1.02/1.01      theory(equality) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_557,plain,
% 1.02/1.01      ( k5_yellow_1(X0_44,X1_44) = k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
% 1.02/1.01      | X1_44 != k2_funcop_1(k1_xboole_0,sK1)
% 1.02/1.01      | X0_44 != k1_xboole_0 ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_313]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_559,plain,
% 1.02/1.01      ( k5_yellow_1(k1_xboole_0,k1_xboole_0) = k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
% 1.02/1.01      | k1_xboole_0 != k2_funcop_1(k1_xboole_0,sK1)
% 1.02/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_557]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_309,plain,
% 1.02/1.01      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 1.02/1.01      theory(equality) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_434,plain,
% 1.02/1.01      ( X0_45 != X1_45
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) != X1_45
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) = X0_45 ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_309]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_485,plain,
% 1.02/1.01      ( X0_45 != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) = X0_45
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1)) ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_434]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_556,plain,
% 1.02/1.01      ( k5_yellow_1(X0_44,X1_44) != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) = k5_yellow_1(X0_44,X1_44)
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1)) ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_485]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_558,plain,
% 1.02/1.01      ( k5_yellow_1(k1_xboole_0,k1_xboole_0) != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) != k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_556]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_441,plain,
% 1.02/1.01      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != X0_45
% 1.02/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k6_yellow_1(X0_44,sK1)
% 1.02/1.01      | k6_yellow_1(X0_44,sK1) != X0_45 ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_309]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_474,plain,
% 1.02/1.01      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0)
% 1.02/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k6_yellow_1(X0_44,sK1)
% 1.02/1.01      | k6_yellow_1(X0_44,sK1) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_441]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_475,plain,
% 1.02/1.01      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != k5_yellow_1(k1_xboole_0,k1_xboole_0)
% 1.02/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK1)
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) != k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_474]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_456,plain,
% 1.02/1.01      ( X0_45 != k6_yellow_1(k1_xboole_0,sK1)
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) = X0_45
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) != k6_yellow_1(k1_xboole_0,sK1) ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_434]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_465,plain,
% 1.02/1.01      ( k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1)) != k6_yellow_1(k1_xboole_0,sK1)
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) = k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1))
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) != k6_yellow_1(k1_xboole_0,sK1) ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_456]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_422,plain,
% 1.02/1.01      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != X0_45
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) != X0_45
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_309]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_432,plain,
% 1.02/1.01      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK1)
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
% 1.02/1.01      | k6_yellow_1(k1_xboole_0,sK1) != k6_yellow_1(k1_xboole_0,sK1) ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_422]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_314,plain,
% 1.02/1.01      ( ~ v1_yellow_1(X0_44) | v1_yellow_1(X1_44) | X1_44 != X0_44 ),
% 1.02/1.01      theory(equality) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_417,plain,
% 1.02/1.01      ( v1_yellow_1(X0_44)
% 1.02/1.01      | ~ v1_yellow_1(k2_funcop_1(X1_44,sK1))
% 1.02/1.01      | X0_44 != k2_funcop_1(X1_44,sK1) ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_314]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_419,plain,
% 1.02/1.01      ( ~ v1_yellow_1(k2_funcop_1(k1_xboole_0,sK1))
% 1.02/1.01      | v1_yellow_1(k1_xboole_0)
% 1.02/1.01      | k1_xboole_0 != k2_funcop_1(k1_xboole_0,sK1) ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_417]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_6,plain,
% 1.02/1.01      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 1.02/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_3,plain,
% 1.02/1.01      ( v4_relat_1(k1_xboole_0,X0) ),
% 1.02/1.01      inference(cnf_transformation,[],[f53]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_11,plain,
% 1.02/1.01      ( ~ v1_partfun1(X0,k1_xboole_0)
% 1.02/1.01      | ~ v4_relat_1(X0,k1_xboole_0)
% 1.02/1.01      | ~ v1_yellow_1(X0)
% 1.02/1.01      | ~ v1_funct_1(X0)
% 1.02/1.01      | ~ v1_relat_1(X0)
% 1.02/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,X0) ),
% 1.02/1.01      inference(cnf_transformation,[],[f74]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_183,plain,
% 1.02/1.01      ( ~ v1_partfun1(X0,k1_xboole_0)
% 1.02/1.01      | ~ v1_yellow_1(X0)
% 1.02/1.01      | ~ v1_funct_1(X0)
% 1.02/1.01      | ~ v1_relat_1(X0)
% 1.02/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,X0)
% 1.02/1.01      | k1_xboole_0 != X1
% 1.02/1.01      | k1_xboole_0 != X0 ),
% 1.02/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_11]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_184,plain,
% 1.02/1.01      ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
% 1.02/1.01      | ~ v1_yellow_1(k1_xboole_0)
% 1.02/1.01      | ~ v1_funct_1(k1_xboole_0)
% 1.02/1.01      | ~ v1_relat_1(k1_xboole_0)
% 1.02/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
% 1.02/1.01      inference(unflattening,[status(thm)],[c_183]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_5,plain,
% 1.02/1.01      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 1.02/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_32,plain,
% 1.02/1.01      ( v1_funct_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_2,plain,
% 1.02/1.01      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 1.02/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_38,plain,
% 1.02/1.01      ( v1_relat_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_0,plain,
% 1.02/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 1.02/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_186,plain,
% 1.02/1.01      ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
% 1.02/1.01      | ~ v1_yellow_1(k1_xboole_0)
% 1.02/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
% 1.02/1.01      inference(global_propositional_subsumption,
% 1.02/1.01                [status(thm)],
% 1.02/1.01                [c_184,c_32,c_38,c_0]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_213,plain,
% 1.02/1.01      ( ~ v1_yellow_1(k1_xboole_0)
% 1.02/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
% 1.02/1.01      | k6_partfun1(X0) != k1_xboole_0
% 1.02/1.01      | k1_xboole_0 != X0 ),
% 1.02/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_186]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_214,plain,
% 1.02/1.01      ( ~ v1_yellow_1(k1_xboole_0)
% 1.02/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
% 1.02/1.01      | k6_partfun1(k1_xboole_0) != k1_xboole_0 ),
% 1.02/1.01      inference(unflattening,[status(thm)],[c_213]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_4,plain,
% 1.02/1.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 1.02/1.01      inference(cnf_transformation,[],[f72]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_216,plain,
% 1.02/1.01      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
% 1.02/1.01      | ~ v1_yellow_1(k1_xboole_0) ),
% 1.02/1.01      inference(global_propositional_subsumption,
% 1.02/1.01                [status(thm)],
% 1.02/1.01                [c_214,c_4]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_217,plain,
% 1.02/1.01      ( ~ v1_yellow_1(k1_xboole_0)
% 1.02/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
% 1.02/1.01      inference(renaming,[status(thm)],[c_216]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_297,plain,
% 1.02/1.01      ( ~ v1_yellow_1(k1_xboole_0)
% 1.02/1.01      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
% 1.02/1.01      inference(subtyping,[status(esa)],[c_217]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_1,plain,
% 1.02/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.02/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_10,plain,
% 1.02/1.01      ( v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
% 1.02/1.01      inference(cnf_transformation,[],[f61]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_206,plain,
% 1.02/1.01      ( k2_funcop_1(k1_xboole_0,X0) != X1 | k1_xboole_0 = X1 ),
% 1.02/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_10]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_207,plain,
% 1.02/1.01      ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) ),
% 1.02/1.01      inference(unflattening,[status(thm)],[c_206]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_298,plain,
% 1.02/1.01      ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0_46) ),
% 1.02/1.01      inference(subtyping,[status(esa)],[c_207]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_331,plain,
% 1.02/1.01      ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,sK1) ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_298]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_8,plain,
% 1.02/1.01      ( ~ l1_orders_2(X0)
% 1.02/1.01      | k5_yellow_1(X1,k2_funcop_1(X1,X0)) = k6_yellow_1(X1,X0) ),
% 1.02/1.01      inference(cnf_transformation,[],[f73]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_13,negated_conjecture,
% 1.02/1.01      ( l1_orders_2(sK1) ),
% 1.02/1.01      inference(cnf_transformation,[],[f64]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_171,plain,
% 1.02/1.01      ( k5_yellow_1(X0,k2_funcop_1(X0,X1)) = k6_yellow_1(X0,X1)
% 1.02/1.01      | sK1 != X1 ),
% 1.02/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_172,plain,
% 1.02/1.01      ( k5_yellow_1(X0,k2_funcop_1(X0,sK1)) = k6_yellow_1(X0,sK1) ),
% 1.02/1.01      inference(unflattening,[status(thm)],[c_171]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_299,plain,
% 1.02/1.01      ( k5_yellow_1(X0_44,k2_funcop_1(X0_44,sK1)) = k6_yellow_1(X0_44,sK1) ),
% 1.02/1.01      inference(subtyping,[status(esa)],[c_172]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_330,plain,
% 1.02/1.01      ( k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,sK1)) = k6_yellow_1(k1_xboole_0,sK1) ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_299]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_12,negated_conjecture,
% 1.02/1.01      ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
% 1.02/1.01      inference(cnf_transformation,[],[f75]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_303,negated_conjecture,
% 1.02/1.01      ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
% 1.02/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_306,plain,( X0_44 = X0_44 ),theory(equality) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_325,plain,
% 1.02/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_306]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_311,plain,
% 1.02/1.01      ( k6_yellow_1(X0_44,X0_46) = k6_yellow_1(X1_44,X0_46)
% 1.02/1.01      | X0_44 != X1_44 ),
% 1.02/1.01      theory(equality) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_318,plain,
% 1.02/1.01      ( k6_yellow_1(k1_xboole_0,sK1) = k6_yellow_1(k1_xboole_0,sK1)
% 1.02/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_311]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_9,plain,
% 1.02/1.01      ( v1_yellow_1(k2_funcop_1(X0,X1)) | ~ l1_orders_2(X1) ),
% 1.02/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_162,plain,
% 1.02/1.01      ( v1_yellow_1(k2_funcop_1(X0,X1)) | sK1 != X1 ),
% 1.02/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_163,plain,
% 1.02/1.01      ( v1_yellow_1(k2_funcop_1(X0,sK1)) ),
% 1.02/1.01      inference(unflattening,[status(thm)],[c_162]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(c_165,plain,
% 1.02/1.01      ( v1_yellow_1(k2_funcop_1(k1_xboole_0,sK1)) ),
% 1.02/1.01      inference(instantiation,[status(thm)],[c_163]) ).
% 1.02/1.01  
% 1.02/1.01  cnf(contradiction,plain,
% 1.02/1.01      ( $false ),
% 1.02/1.01      inference(minisat,
% 1.02/1.01                [status(thm)],
% 1.02/1.01                [c_559,c_558,c_475,c_465,c_432,c_419,c_297,c_331,c_330,
% 1.02/1.01                 c_303,c_325,c_318,c_165]) ).
% 1.02/1.01  
% 1.02/1.01  
% 1.02/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.02/1.01  
% 1.02/1.01  ------                               Statistics
% 1.02/1.01  
% 1.02/1.01  ------ General
% 1.02/1.01  
% 1.02/1.01  abstr_ref_over_cycles:                  0
% 1.02/1.01  abstr_ref_under_cycles:                 0
% 1.02/1.01  gc_basic_clause_elim:                   0
% 1.02/1.01  forced_gc_time:                         0
% 1.02/1.01  parsing_time:                           0.01
% 1.02/1.01  unif_index_cands_time:                  0.
% 1.02/1.01  unif_index_add_time:                    0.
% 1.02/1.01  orderings_time:                         0.
% 1.02/1.01  out_proof_time:                         0.011
% 1.02/1.01  total_time:                             0.058
% 1.02/1.01  num_of_symbols:                         47
% 1.02/1.01  num_of_terms:                           692
% 1.02/1.01  
% 1.02/1.01  ------ Preprocessing
% 1.02/1.01  
% 1.02/1.01  num_of_splits:                          0
% 1.02/1.01  num_of_split_atoms:                     0
% 1.02/1.01  num_of_reused_defs:                     0
% 1.02/1.01  num_eq_ax_congr_red:                    5
% 1.02/1.01  num_of_sem_filtered_clauses:            1
% 1.02/1.01  num_of_subtypes:                        3
% 1.02/1.01  monotx_restored_types:                  0
% 1.02/1.01  sat_num_of_epr_types:                   0
% 1.02/1.01  sat_num_of_non_cyclic_types:            0
% 1.02/1.01  sat_guarded_non_collapsed_types:        0
% 1.02/1.01  num_pure_diseq_elim:                    0
% 1.02/1.01  simp_replaced_by:                       0
% 1.02/1.01  res_preprocessed:                       61
% 1.02/1.01  prep_upred:                             0
% 1.02/1.01  prep_unflattend:                        9
% 1.02/1.01  smt_new_axioms:                         0
% 1.02/1.01  pred_elim_cands:                        1
% 1.02/1.01  pred_elim:                              6
% 1.02/1.01  pred_elim_cl:                           6
% 1.02/1.01  pred_elim_cycles:                       8
% 1.02/1.01  merged_defs:                            0
% 1.02/1.01  merged_defs_ncl:                        0
% 1.02/1.01  bin_hyper_res:                          0
% 1.02/1.01  prep_cycles:                            4
% 1.02/1.01  pred_elim_time:                         0.002
% 1.02/1.01  splitting_time:                         0.
% 1.02/1.01  sem_filter_time:                        0.
% 1.02/1.01  monotx_time:                            0.
% 1.02/1.01  subtype_inf_time:                       0.
% 1.02/1.01  
% 1.02/1.01  ------ Problem properties
% 1.02/1.01  
% 1.02/1.01  clauses:                                8
% 1.02/1.01  conjectures:                            1
% 1.02/1.01  epr:                                    0
% 1.02/1.01  horn:                                   8
% 1.02/1.01  ground:                                 3
% 1.02/1.01  unary:                                  7
% 1.02/1.01  binary:                                 1
% 1.02/1.01  lits:                                   9
% 1.02/1.01  lits_eq:                                6
% 1.02/1.01  fd_pure:                                0
% 1.02/1.01  fd_pseudo:                              0
% 1.02/1.01  fd_cond:                                0
% 1.02/1.01  fd_pseudo_cond:                         0
% 1.02/1.01  ac_symbols:                             0
% 1.02/1.01  
% 1.02/1.01  ------ Propositional Solver
% 1.02/1.01  
% 1.02/1.01  prop_solver_calls:                      27
% 1.02/1.01  prop_fast_solver_calls:                 268
% 1.02/1.01  smt_solver_calls:                       0
% 1.02/1.01  smt_fast_solver_calls:                  0
% 1.02/1.01  prop_num_of_clauses:                    180
% 1.02/1.01  prop_preprocess_simplified:             1287
% 1.02/1.01  prop_fo_subsumed:                       3
% 1.02/1.01  prop_solver_time:                       0.
% 1.02/1.01  smt_solver_time:                        0.
% 1.02/1.01  smt_fast_solver_time:                   0.
% 1.02/1.01  prop_fast_solver_time:                  0.
% 1.02/1.01  prop_unsat_core_time:                   0.
% 1.02/1.01  
% 1.02/1.01  ------ QBF
% 1.02/1.01  
% 1.02/1.01  qbf_q_res:                              0
% 1.02/1.01  qbf_num_tautologies:                    0
% 1.02/1.01  qbf_prep_cycles:                        0
% 1.02/1.01  
% 1.02/1.01  ------ BMC1
% 1.02/1.01  
% 1.02/1.01  bmc1_current_bound:                     -1
% 1.02/1.01  bmc1_last_solved_bound:                 -1
% 1.02/1.01  bmc1_unsat_core_size:                   -1
% 1.02/1.01  bmc1_unsat_core_parents_size:           -1
% 1.02/1.01  bmc1_merge_next_fun:                    0
% 1.02/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.02/1.01  
% 1.02/1.01  ------ Instantiation
% 1.02/1.01  
% 1.02/1.01  inst_num_of_clauses:                    67
% 1.02/1.01  inst_num_in_passive:                    14
% 1.02/1.01  inst_num_in_active:                     46
% 1.02/1.01  inst_num_in_unprocessed:                6
% 1.02/1.01  inst_num_of_loops:                      53
% 1.02/1.01  inst_num_of_learning_restarts:          0
% 1.02/1.01  inst_num_moves_active_passive:          2
% 1.02/1.01  inst_lit_activity:                      0
% 1.02/1.01  inst_lit_activity_moves:                0
% 1.02/1.01  inst_num_tautologies:                   0
% 1.02/1.01  inst_num_prop_implied:                  0
% 1.02/1.01  inst_num_existing_simplified:           0
% 1.02/1.01  inst_num_eq_res_simplified:             0
% 1.02/1.01  inst_num_child_elim:                    0
% 1.02/1.01  inst_num_of_dismatching_blockings:      3
% 1.02/1.01  inst_num_of_non_proper_insts:           44
% 1.02/1.01  inst_num_of_duplicates:                 0
% 1.02/1.01  inst_inst_num_from_inst_to_res:         0
% 1.02/1.01  inst_dismatching_checking_time:         0.
% 1.02/1.01  
% 1.02/1.01  ------ Resolution
% 1.02/1.01  
% 1.02/1.01  res_num_of_clauses:                     0
% 1.02/1.01  res_num_in_passive:                     0
% 1.02/1.01  res_num_in_active:                      0
% 1.02/1.01  res_num_of_loops:                       65
% 1.02/1.01  res_forward_subset_subsumed:            9
% 1.02/1.01  res_backward_subset_subsumed:           0
% 1.02/1.01  res_forward_subsumed:                   0
% 1.02/1.01  res_backward_subsumed:                  0
% 1.02/1.01  res_forward_subsumption_resolution:     0
% 1.02/1.01  res_backward_subsumption_resolution:    0
% 1.02/1.01  res_clause_to_clause_subsumption:       14
% 1.02/1.01  res_orphan_elimination:                 0
% 1.02/1.01  res_tautology_del:                      8
% 1.02/1.01  res_num_eq_res_simplified:              0
% 1.02/1.01  res_num_sel_changes:                    0
% 1.02/1.01  res_moves_from_active_to_pass:          0
% 1.02/1.01  
% 1.02/1.01  ------ Superposition
% 1.02/1.01  
% 1.02/1.01  sup_time_total:                         0.
% 1.02/1.01  sup_time_generating:                    0.
% 1.02/1.01  sup_time_sim_full:                      0.
% 1.02/1.01  sup_time_sim_immed:                     0.
% 1.02/1.01  
% 1.02/1.01  sup_num_of_clauses:                     11
% 1.02/1.01  sup_num_in_active:                      9
% 1.02/1.01  sup_num_in_passive:                     2
% 1.02/1.01  sup_num_of_loops:                       10
% 1.02/1.01  sup_fw_superposition:                   2
% 1.02/1.01  sup_bw_superposition:                   2
% 1.02/1.01  sup_immediate_simplified:               0
% 1.02/1.01  sup_given_eliminated:                   0
% 1.02/1.01  comparisons_done:                       0
% 1.02/1.01  comparisons_avoided:                    0
% 1.02/1.01  
% 1.02/1.01  ------ Simplifications
% 1.02/1.01  
% 1.02/1.01  
% 1.02/1.01  sim_fw_subset_subsumed:                 0
% 1.02/1.01  sim_bw_subset_subsumed:                 0
% 1.02/1.01  sim_fw_subsumed:                        0
% 1.02/1.01  sim_bw_subsumed:                        0
% 1.02/1.01  sim_fw_subsumption_res:                 0
% 1.02/1.01  sim_bw_subsumption_res:                 0
% 1.02/1.01  sim_tautology_del:                      0
% 1.02/1.01  sim_eq_tautology_del:                   0
% 1.02/1.01  sim_eq_res_simp:                        0
% 1.02/1.01  sim_fw_demodulated:                     0
% 1.02/1.01  sim_bw_demodulated:                     1
% 1.02/1.01  sim_light_normalised:                   0
% 1.02/1.01  sim_joinable_taut:                      0
% 1.02/1.01  sim_joinable_simp:                      0
% 1.02/1.01  sim_ac_normalised:                      0
% 1.02/1.01  sim_smt_subsumption:                    0
% 1.02/1.01  
%------------------------------------------------------------------------------
