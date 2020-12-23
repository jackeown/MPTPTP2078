%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:34 EST 2020

% Result     : Theorem 1.09s
% Output     : CNFRefutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 255 expanded)
%              Number of clauses        :   71 (  86 expanded)
%              Number of leaves         :   29 (  69 expanded)
%              Depth                    :   22
%              Number of atoms          :  294 ( 435 expanded)
%              Number of equality atoms :  157 ( 270 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f54,f58])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f57,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f56,f58])).

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

fof(f64,plain,(
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

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f67])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f68])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f69])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f70])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f71])).

fof(f77,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f64,f72,f72])).

fof(f55,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f55,f58])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f19,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
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

fof(f60,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f20,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(definition_unfolding,[],[f60,f63])).

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

fof(f65,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f66,f72,f72])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

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

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_488,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_903,plain,
    ( X0_47 != X1_47
    | X0_47 = k6_partfun1(X2_47)
    | k6_partfun1(X2_47) != X1_47 ),
    inference(instantiation,[status(thm)],[c_488])).

cnf(c_904,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_903])).

cnf(c_490,plain,
    ( ~ v4_relat_1(X0_47,X1_47)
    | v4_relat_1(X2_47,X3_47)
    | X2_47 != X0_47
    | X3_47 != X1_47 ),
    theory(equality)).

cnf(c_799,plain,
    ( v4_relat_1(X0_47,X1_47)
    | ~ v4_relat_1(k6_partfun1(X2_47),X3_47)
    | X1_47 != X3_47
    | X0_47 != k6_partfun1(X2_47) ),
    inference(instantiation,[status(thm)],[c_490])).

cnf(c_801,plain,
    ( ~ v4_relat_1(k6_partfun1(k1_xboole_0),k1_xboole_0)
    | v4_relat_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_6,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_482,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_9,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7,plain,
    ( v1_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_14,plain,
    ( ~ v1_partfun1(X0,k1_xboole_0)
    | ~ v4_relat_1(X0,k1_xboole_0)
    | ~ v1_yellow_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_208,plain,
    ( ~ v1_partfun1(X0,k1_xboole_0)
    | ~ v4_relat_1(X0,k1_xboole_0)
    | ~ v1_yellow_1(X0)
    | ~ v1_relat_1(X0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,X0)
    | k6_partfun1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_209,plain,
    ( ~ v1_partfun1(k6_partfun1(X0),k1_xboole_0)
    | ~ v4_relat_1(k6_partfun1(X0),k1_xboole_0)
    | ~ v1_yellow_1(k6_partfun1(X0))
    | ~ v1_relat_1(k6_partfun1(X0))
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0)) ),
    inference(unflattening,[status(thm)],[c_208])).

cnf(c_8,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_213,plain,
    ( ~ v1_yellow_1(k6_partfun1(X0))
    | ~ v4_relat_1(k6_partfun1(X0),k1_xboole_0)
    | ~ v1_partfun1(k6_partfun1(X0),k1_xboole_0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_209,c_8])).

cnf(c_214,plain,
    ( ~ v1_partfun1(k6_partfun1(X0),k1_xboole_0)
    | ~ v4_relat_1(k6_partfun1(X0),k1_xboole_0)
    | ~ v1_yellow_1(k6_partfun1(X0))
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0)) ),
    inference(renaming,[status(thm)],[c_213])).

cnf(c_237,plain,
    ( ~ v4_relat_1(k6_partfun1(X0),k1_xboole_0)
    | ~ v1_yellow_1(k6_partfun1(X0))
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0))
    | k6_partfun1(X0) != k6_partfun1(X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_214])).

cnf(c_238,plain,
    ( ~ v4_relat_1(k6_partfun1(X0),k1_xboole_0)
    | ~ v1_yellow_1(k6_partfun1(X0))
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0))
    | k6_partfun1(X0) != k6_partfun1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_475,plain,
    ( ~ v4_relat_1(k6_partfun1(X0_47),k1_xboole_0)
    | ~ v1_yellow_1(k6_partfun1(X0_47))
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0_47))
    | k6_partfun1(X0_47) != k6_partfun1(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_238])).

cnf(c_606,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0_47))
    | k6_partfun1(X0_47) != k6_partfun1(k1_xboole_0)
    | v4_relat_1(k6_partfun1(X0_47),k1_xboole_0) != iProver_top
    | v1_yellow_1(k6_partfun1(X0_47)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_475])).

cnf(c_630,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0_47))
    | k6_partfun1(X0_47) != k1_xboole_0
    | v4_relat_1(k6_partfun1(X0_47),k1_xboole_0) != iProver_top
    | v1_yellow_1(k6_partfun1(X0_47)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_606,c_482])).

cnf(c_761,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(k1_xboole_0))
    | v4_relat_1(k6_partfun1(k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_yellow_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_482,c_630])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_13,plain,
    ( v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_165,plain,
    ( k2_funcop_1(k1_xboole_0,X0) != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_166,plain,
    ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) ),
    inference(unflattening,[status(thm)],[c_165])).

cnf(c_480,plain,
    ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0_49) ),
    inference(subtyping,[status(esa)],[c_166])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | k5_yellow_1(X1,k2_funcop_1(X1,X0)) = k6_yellow_1(X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_16,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_196,plain,
    ( k5_yellow_1(X0,k2_funcop_1(X0,X1)) = k6_yellow_1(X0,X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_197,plain,
    ( k5_yellow_1(X0,k2_funcop_1(X0,sK1)) = k6_yellow_1(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_196])).

cnf(c_476,plain,
    ( k5_yellow_1(X0_47,k2_funcop_1(X0_47,sK1)) = k6_yellow_1(X0_47,sK1) ),
    inference(subtyping,[status(esa)],[c_197])).

cnf(c_716,plain,
    ( k5_yellow_1(k1_xboole_0,k1_xboole_0) = k6_yellow_1(k1_xboole_0,sK1) ),
    inference(superposition,[status(thm)],[c_480,c_476])).

cnf(c_762,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK1)
    | v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_yellow_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_761,c_482,c_716])).

cnf(c_763,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_762])).

cnf(c_725,plain,
    ( k1_relat_1(X0_47) != X1_47
    | k1_xboole_0 != X1_47
    | k1_xboole_0 = k1_relat_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_488])).

cnf(c_726,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_725])).

cnf(c_491,plain,
    ( X0_47 != X1_47
    | k1_relat_1(X0_47) = k1_relat_1(X1_47) ),
    theory(equality)).

cnf(c_690,plain,
    ( k6_partfun1(X0_47) != X1_47
    | k1_relat_1(k6_partfun1(X0_47)) = k1_relat_1(X1_47) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_692,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k6_partfun1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_690])).

cnf(c_658,plain,
    ( k1_relat_1(k6_partfun1(X0_47)) != X1_47
    | k1_relat_1(k6_partfun1(X0_47)) = k1_xboole_0
    | k1_xboole_0 != X1_47 ),
    inference(instantiation,[status(thm)],[c_488])).

cnf(c_689,plain,
    ( k1_relat_1(k6_partfun1(X0_47)) != k1_relat_1(X1_47)
    | k1_relat_1(k6_partfun1(X0_47)) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X1_47) ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_691,plain,
    ( k1_relat_1(k6_partfun1(k1_xboole_0)) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(k6_partfun1(k1_xboole_0)) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_489,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_659,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != X0_48
    | k6_yellow_1(k1_xboole_0,sK1) != X0_48
    | k6_yellow_1(k1_xboole_0,sK1) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_489])).

cnf(c_669,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK1)
    | k6_yellow_1(k1_xboole_0,sK1) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | k6_yellow_1(k1_xboole_0,sK1) != k6_yellow_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(c_497,plain,
    ( ~ v1_yellow_1(X0_47)
    | v1_yellow_1(X1_47)
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_653,plain,
    ( v1_yellow_1(X0_47)
    | ~ v1_yellow_1(k2_funcop_1(X1_47,sK1))
    | X0_47 != k2_funcop_1(X1_47,sK1) ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_655,plain,
    ( ~ v1_yellow_1(k2_funcop_1(k1_xboole_0,sK1))
    | v1_yellow_1(k1_xboole_0)
    | k1_xboole_0 != k2_funcop_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_272,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | k6_partfun1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_273,plain,
    ( v4_relat_1(k6_partfun1(X0),X1)
    | ~ r1_tarski(k1_relat_1(k6_partfun1(X0)),X1) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_291,plain,
    ( v4_relat_1(k6_partfun1(X0),X1)
    | X1 != X2
    | k1_relat_1(k6_partfun1(X0)) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_273])).

cnf(c_292,plain,
    ( v4_relat_1(k6_partfun1(X0),X1)
    | k1_relat_1(k6_partfun1(X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_474,plain,
    ( v4_relat_1(k6_partfun1(X0_47),X1_47)
    | k1_relat_1(k6_partfun1(X0_47)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_292])).

cnf(c_522,plain,
    ( v4_relat_1(k6_partfun1(k1_xboole_0),k1_xboole_0)
    | k1_relat_1(k6_partfun1(k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_513,plain,
    ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_15,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_481,negated_conjecture,
    ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_5,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_483,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_486,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_511,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_494,plain,
    ( k6_yellow_1(X0_47,X0_49) = k6_yellow_1(X1_47,X0_49)
    | X0_47 != X1_47 ),
    theory(equality)).

cnf(c_504,plain,
    ( k6_yellow_1(k1_xboole_0,sK1) = k6_yellow_1(k1_xboole_0,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_12,plain,
    ( v1_yellow_1(k2_funcop_1(X0,X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_187,plain,
    ( v1_yellow_1(k2_funcop_1(X0,X1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_188,plain,
    ( v1_yellow_1(k2_funcop_1(X0,sK1)) ),
    inference(unflattening,[status(thm)],[c_187])).

cnf(c_190,plain,
    ( v1_yellow_1(k2_funcop_1(k1_xboole_0,sK1)) ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_904,c_801,c_763,c_726,c_692,c_691,c_669,c_655,c_522,c_513,c_481,c_482,c_483,c_511,c_504,c_190])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.09/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.09/0.99  
% 1.09/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.09/0.99  
% 1.09/0.99  ------  iProver source info
% 1.09/0.99  
% 1.09/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.09/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.09/0.99  git: non_committed_changes: false
% 1.09/0.99  git: last_make_outside_of_git: false
% 1.09/0.99  
% 1.09/0.99  ------ 
% 1.09/0.99  
% 1.09/0.99  ------ Input Options
% 1.09/0.99  
% 1.09/0.99  --out_options                           all
% 1.09/0.99  --tptp_safe_out                         true
% 1.09/0.99  --problem_path                          ""
% 1.09/0.99  --include_path                          ""
% 1.09/0.99  --clausifier                            res/vclausify_rel
% 1.09/0.99  --clausifier_options                    --mode clausify
% 1.09/0.99  --stdin                                 false
% 1.09/0.99  --stats_out                             all
% 1.09/0.99  
% 1.09/0.99  ------ General Options
% 1.09/0.99  
% 1.09/0.99  --fof                                   false
% 1.09/0.99  --time_out_real                         305.
% 1.09/0.99  --time_out_virtual                      -1.
% 1.09/0.99  --symbol_type_check                     false
% 1.09/0.99  --clausify_out                          false
% 1.09/0.99  --sig_cnt_out                           false
% 1.09/0.99  --trig_cnt_out                          false
% 1.09/0.99  --trig_cnt_out_tolerance                1.
% 1.09/0.99  --trig_cnt_out_sk_spl                   false
% 1.09/0.99  --abstr_cl_out                          false
% 1.09/0.99  
% 1.09/0.99  ------ Global Options
% 1.09/0.99  
% 1.09/0.99  --schedule                              default
% 1.09/0.99  --add_important_lit                     false
% 1.09/0.99  --prop_solver_per_cl                    1000
% 1.09/0.99  --min_unsat_core                        false
% 1.09/0.99  --soft_assumptions                      false
% 1.09/0.99  --soft_lemma_size                       3
% 1.09/0.99  --prop_impl_unit_size                   0
% 1.09/0.99  --prop_impl_unit                        []
% 1.09/0.99  --share_sel_clauses                     true
% 1.09/0.99  --reset_solvers                         false
% 1.09/0.99  --bc_imp_inh                            [conj_cone]
% 1.09/0.99  --conj_cone_tolerance                   3.
% 1.09/0.99  --extra_neg_conj                        none
% 1.09/0.99  --large_theory_mode                     true
% 1.09/0.99  --prolific_symb_bound                   200
% 1.09/0.99  --lt_threshold                          2000
% 1.09/0.99  --clause_weak_htbl                      true
% 1.09/0.99  --gc_record_bc_elim                     false
% 1.09/0.99  
% 1.09/0.99  ------ Preprocessing Options
% 1.09/0.99  
% 1.09/0.99  --preprocessing_flag                    true
% 1.09/0.99  --time_out_prep_mult                    0.1
% 1.09/0.99  --splitting_mode                        input
% 1.09/0.99  --splitting_grd                         true
% 1.09/0.99  --splitting_cvd                         false
% 1.09/0.99  --splitting_cvd_svl                     false
% 1.09/0.99  --splitting_nvd                         32
% 1.09/0.99  --sub_typing                            true
% 1.09/0.99  --prep_gs_sim                           true
% 1.09/0.99  --prep_unflatten                        true
% 1.09/0.99  --prep_res_sim                          true
% 1.09/0.99  --prep_upred                            true
% 1.09/0.99  --prep_sem_filter                       exhaustive
% 1.09/0.99  --prep_sem_filter_out                   false
% 1.09/0.99  --pred_elim                             true
% 1.09/0.99  --res_sim_input                         true
% 1.09/0.99  --eq_ax_congr_red                       true
% 1.09/0.99  --pure_diseq_elim                       true
% 1.09/0.99  --brand_transform                       false
% 1.09/0.99  --non_eq_to_eq                          false
% 1.09/0.99  --prep_def_merge                        true
% 1.09/0.99  --prep_def_merge_prop_impl              false
% 1.09/0.99  --prep_def_merge_mbd                    true
% 1.09/0.99  --prep_def_merge_tr_red                 false
% 1.09/0.99  --prep_def_merge_tr_cl                  false
% 1.09/0.99  --smt_preprocessing                     true
% 1.09/0.99  --smt_ac_axioms                         fast
% 1.09/0.99  --preprocessed_out                      false
% 1.09/0.99  --preprocessed_stats                    false
% 1.09/0.99  
% 1.09/0.99  ------ Abstraction refinement Options
% 1.09/0.99  
% 1.09/0.99  --abstr_ref                             []
% 1.09/0.99  --abstr_ref_prep                        false
% 1.09/0.99  --abstr_ref_until_sat                   false
% 1.09/0.99  --abstr_ref_sig_restrict                funpre
% 1.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.09/0.99  --abstr_ref_under                       []
% 1.09/0.99  
% 1.09/0.99  ------ SAT Options
% 1.09/0.99  
% 1.09/0.99  --sat_mode                              false
% 1.09/0.99  --sat_fm_restart_options                ""
% 1.09/0.99  --sat_gr_def                            false
% 1.09/0.99  --sat_epr_types                         true
% 1.09/0.99  --sat_non_cyclic_types                  false
% 1.09/0.99  --sat_finite_models                     false
% 1.09/0.99  --sat_fm_lemmas                         false
% 1.09/0.99  --sat_fm_prep                           false
% 1.09/0.99  --sat_fm_uc_incr                        true
% 1.09/0.99  --sat_out_model                         small
% 1.09/0.99  --sat_out_clauses                       false
% 1.09/0.99  
% 1.09/0.99  ------ QBF Options
% 1.09/0.99  
% 1.09/0.99  --qbf_mode                              false
% 1.09/0.99  --qbf_elim_univ                         false
% 1.09/0.99  --qbf_dom_inst                          none
% 1.09/0.99  --qbf_dom_pre_inst                      false
% 1.09/0.99  --qbf_sk_in                             false
% 1.09/0.99  --qbf_pred_elim                         true
% 1.09/0.99  --qbf_split                             512
% 1.09/0.99  
% 1.09/0.99  ------ BMC1 Options
% 1.09/0.99  
% 1.09/0.99  --bmc1_incremental                      false
% 1.09/0.99  --bmc1_axioms                           reachable_all
% 1.09/0.99  --bmc1_min_bound                        0
% 1.09/0.99  --bmc1_max_bound                        -1
% 1.09/0.99  --bmc1_max_bound_default                -1
% 1.09/0.99  --bmc1_symbol_reachability              true
% 1.09/0.99  --bmc1_property_lemmas                  false
% 1.09/0.99  --bmc1_k_induction                      false
% 1.09/0.99  --bmc1_non_equiv_states                 false
% 1.09/0.99  --bmc1_deadlock                         false
% 1.09/0.99  --bmc1_ucm                              false
% 1.09/0.99  --bmc1_add_unsat_core                   none
% 1.09/0.99  --bmc1_unsat_core_children              false
% 1.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.09/0.99  --bmc1_out_stat                         full
% 1.09/0.99  --bmc1_ground_init                      false
% 1.09/0.99  --bmc1_pre_inst_next_state              false
% 1.09/0.99  --bmc1_pre_inst_state                   false
% 1.09/0.99  --bmc1_pre_inst_reach_state             false
% 1.09/0.99  --bmc1_out_unsat_core                   false
% 1.09/0.99  --bmc1_aig_witness_out                  false
% 1.09/0.99  --bmc1_verbose                          false
% 1.09/0.99  --bmc1_dump_clauses_tptp                false
% 1.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.09/0.99  --bmc1_dump_file                        -
% 1.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.09/0.99  --bmc1_ucm_extend_mode                  1
% 1.09/0.99  --bmc1_ucm_init_mode                    2
% 1.09/0.99  --bmc1_ucm_cone_mode                    none
% 1.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.09/0.99  --bmc1_ucm_relax_model                  4
% 1.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.09/0.99  --bmc1_ucm_layered_model                none
% 1.09/0.99  --bmc1_ucm_max_lemma_size               10
% 1.09/0.99  
% 1.09/0.99  ------ AIG Options
% 1.09/0.99  
% 1.09/0.99  --aig_mode                              false
% 1.09/0.99  
% 1.09/0.99  ------ Instantiation Options
% 1.09/0.99  
% 1.09/0.99  --instantiation_flag                    true
% 1.09/0.99  --inst_sos_flag                         false
% 1.09/0.99  --inst_sos_phase                        true
% 1.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.09/0.99  --inst_lit_sel_side                     num_symb
% 1.09/0.99  --inst_solver_per_active                1400
% 1.09/0.99  --inst_solver_calls_frac                1.
% 1.09/0.99  --inst_passive_queue_type               priority_queues
% 1.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.09/0.99  --inst_passive_queues_freq              [25;2]
% 1.09/0.99  --inst_dismatching                      true
% 1.09/0.99  --inst_eager_unprocessed_to_passive     true
% 1.09/0.99  --inst_prop_sim_given                   true
% 1.09/0.99  --inst_prop_sim_new                     false
% 1.09/0.99  --inst_subs_new                         false
% 1.09/0.99  --inst_eq_res_simp                      false
% 1.09/0.99  --inst_subs_given                       false
% 1.09/0.99  --inst_orphan_elimination               true
% 1.09/0.99  --inst_learning_loop_flag               true
% 1.09/0.99  --inst_learning_start                   3000
% 1.09/0.99  --inst_learning_factor                  2
% 1.09/0.99  --inst_start_prop_sim_after_learn       3
% 1.09/0.99  --inst_sel_renew                        solver
% 1.09/0.99  --inst_lit_activity_flag                true
% 1.09/0.99  --inst_restr_to_given                   false
% 1.09/0.99  --inst_activity_threshold               500
% 1.09/0.99  --inst_out_proof                        true
% 1.09/0.99  
% 1.09/0.99  ------ Resolution Options
% 1.09/0.99  
% 1.09/0.99  --resolution_flag                       true
% 1.09/0.99  --res_lit_sel                           adaptive
% 1.09/0.99  --res_lit_sel_side                      none
% 1.09/0.99  --res_ordering                          kbo
% 1.09/0.99  --res_to_prop_solver                    active
% 1.09/0.99  --res_prop_simpl_new                    false
% 1.09/0.99  --res_prop_simpl_given                  true
% 1.09/0.99  --res_passive_queue_type                priority_queues
% 1.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.09/0.99  --res_passive_queues_freq               [15;5]
% 1.09/0.99  --res_forward_subs                      full
% 1.09/0.99  --res_backward_subs                     full
% 1.09/0.99  --res_forward_subs_resolution           true
% 1.09/0.99  --res_backward_subs_resolution          true
% 1.09/0.99  --res_orphan_elimination                true
% 1.09/0.99  --res_time_limit                        2.
% 1.09/0.99  --res_out_proof                         true
% 1.09/0.99  
% 1.09/0.99  ------ Superposition Options
% 1.09/0.99  
% 1.09/0.99  --superposition_flag                    true
% 1.09/0.99  --sup_passive_queue_type                priority_queues
% 1.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.09/0.99  --demod_completeness_check              fast
% 1.09/0.99  --demod_use_ground                      true
% 1.09/0.99  --sup_to_prop_solver                    passive
% 1.09/0.99  --sup_prop_simpl_new                    true
% 1.09/0.99  --sup_prop_simpl_given                  true
% 1.09/0.99  --sup_fun_splitting                     false
% 1.09/0.99  --sup_smt_interval                      50000
% 1.09/0.99  
% 1.09/0.99  ------ Superposition Simplification Setup
% 1.09/0.99  
% 1.09/0.99  --sup_indices_passive                   []
% 1.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/0.99  --sup_full_bw                           [BwDemod]
% 1.09/0.99  --sup_immed_triv                        [TrivRules]
% 1.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/0.99  --sup_immed_bw_main                     []
% 1.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.09/0.99  
% 1.09/0.99  ------ Combination Options
% 1.09/0.99  
% 1.09/0.99  --comb_res_mult                         3
% 1.09/0.99  --comb_sup_mult                         2
% 1.09/0.99  --comb_inst_mult                        10
% 1.09/0.99  
% 1.09/0.99  ------ Debug Options
% 1.09/0.99  
% 1.09/0.99  --dbg_backtrace                         false
% 1.09/0.99  --dbg_dump_prop_clauses                 false
% 1.09/0.99  --dbg_dump_prop_clauses_file            -
% 1.09/0.99  --dbg_out_stat                          false
% 1.09/0.99  ------ Parsing...
% 1.09/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.09/0.99  
% 1.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.09/0.99  
% 1.09/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.09/0.99  
% 1.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.09/0.99  ------ Proving...
% 1.09/0.99  ------ Problem Properties 
% 1.09/0.99  
% 1.09/0.99  
% 1.09/0.99  clauses                                 11
% 1.09/0.99  conjectures                             1
% 1.09/0.99  EPR                                     0
% 1.09/0.99  Horn                                    11
% 1.09/0.99  unary                                   9
% 1.09/0.99  binary                                  1
% 1.09/0.99  lits                                    15
% 1.09/0.99  lits eq                                 10
% 1.09/0.99  fd_pure                                 0
% 1.09/0.99  fd_pseudo                               0
% 1.09/0.99  fd_cond                                 0
% 1.09/0.99  fd_pseudo_cond                          0
% 1.09/0.99  AC symbols                              0
% 1.09/0.99  
% 1.09/0.99  ------ Schedule dynamic 5 is on 
% 1.09/0.99  
% 1.09/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.09/0.99  
% 1.09/0.99  
% 1.09/0.99  ------ 
% 1.09/0.99  Current options:
% 1.09/0.99  ------ 
% 1.09/0.99  
% 1.09/0.99  ------ Input Options
% 1.09/0.99  
% 1.09/0.99  --out_options                           all
% 1.09/0.99  --tptp_safe_out                         true
% 1.09/0.99  --problem_path                          ""
% 1.09/0.99  --include_path                          ""
% 1.09/0.99  --clausifier                            res/vclausify_rel
% 1.09/0.99  --clausifier_options                    --mode clausify
% 1.09/0.99  --stdin                                 false
% 1.09/0.99  --stats_out                             all
% 1.09/0.99  
% 1.09/0.99  ------ General Options
% 1.09/0.99  
% 1.09/0.99  --fof                                   false
% 1.09/0.99  --time_out_real                         305.
% 1.09/0.99  --time_out_virtual                      -1.
% 1.09/0.99  --symbol_type_check                     false
% 1.09/0.99  --clausify_out                          false
% 1.09/0.99  --sig_cnt_out                           false
% 1.09/0.99  --trig_cnt_out                          false
% 1.09/0.99  --trig_cnt_out_tolerance                1.
% 1.09/0.99  --trig_cnt_out_sk_spl                   false
% 1.09/0.99  --abstr_cl_out                          false
% 1.09/0.99  
% 1.09/0.99  ------ Global Options
% 1.09/0.99  
% 1.09/0.99  --schedule                              default
% 1.09/0.99  --add_important_lit                     false
% 1.09/0.99  --prop_solver_per_cl                    1000
% 1.09/0.99  --min_unsat_core                        false
% 1.09/0.99  --soft_assumptions                      false
% 1.09/0.99  --soft_lemma_size                       3
% 1.09/0.99  --prop_impl_unit_size                   0
% 1.09/0.99  --prop_impl_unit                        []
% 1.09/0.99  --share_sel_clauses                     true
% 1.09/0.99  --reset_solvers                         false
% 1.09/0.99  --bc_imp_inh                            [conj_cone]
% 1.09/0.99  --conj_cone_tolerance                   3.
% 1.09/0.99  --extra_neg_conj                        none
% 1.09/0.99  --large_theory_mode                     true
% 1.09/0.99  --prolific_symb_bound                   200
% 1.09/0.99  --lt_threshold                          2000
% 1.09/0.99  --clause_weak_htbl                      true
% 1.09/0.99  --gc_record_bc_elim                     false
% 1.09/0.99  
% 1.09/0.99  ------ Preprocessing Options
% 1.09/0.99  
% 1.09/0.99  --preprocessing_flag                    true
% 1.09/0.99  --time_out_prep_mult                    0.1
% 1.09/0.99  --splitting_mode                        input
% 1.09/0.99  --splitting_grd                         true
% 1.09/0.99  --splitting_cvd                         false
% 1.09/0.99  --splitting_cvd_svl                     false
% 1.09/0.99  --splitting_nvd                         32
% 1.09/0.99  --sub_typing                            true
% 1.09/0.99  --prep_gs_sim                           true
% 1.09/0.99  --prep_unflatten                        true
% 1.09/0.99  --prep_res_sim                          true
% 1.09/0.99  --prep_upred                            true
% 1.09/0.99  --prep_sem_filter                       exhaustive
% 1.09/0.99  --prep_sem_filter_out                   false
% 1.09/0.99  --pred_elim                             true
% 1.09/0.99  --res_sim_input                         true
% 1.09/0.99  --eq_ax_congr_red                       true
% 1.09/0.99  --pure_diseq_elim                       true
% 1.09/0.99  --brand_transform                       false
% 1.09/0.99  --non_eq_to_eq                          false
% 1.09/0.99  --prep_def_merge                        true
% 1.09/0.99  --prep_def_merge_prop_impl              false
% 1.09/0.99  --prep_def_merge_mbd                    true
% 1.09/0.99  --prep_def_merge_tr_red                 false
% 1.09/0.99  --prep_def_merge_tr_cl                  false
% 1.09/0.99  --smt_preprocessing                     true
% 1.09/0.99  --smt_ac_axioms                         fast
% 1.09/0.99  --preprocessed_out                      false
% 1.09/0.99  --preprocessed_stats                    false
% 1.09/0.99  
% 1.09/0.99  ------ Abstraction refinement Options
% 1.09/0.99  
% 1.09/0.99  --abstr_ref                             []
% 1.09/0.99  --abstr_ref_prep                        false
% 1.09/0.99  --abstr_ref_until_sat                   false
% 1.09/0.99  --abstr_ref_sig_restrict                funpre
% 1.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.09/0.99  --abstr_ref_under                       []
% 1.09/0.99  
% 1.09/0.99  ------ SAT Options
% 1.09/0.99  
% 1.09/0.99  --sat_mode                              false
% 1.09/0.99  --sat_fm_restart_options                ""
% 1.09/0.99  --sat_gr_def                            false
% 1.09/0.99  --sat_epr_types                         true
% 1.09/0.99  --sat_non_cyclic_types                  false
% 1.09/0.99  --sat_finite_models                     false
% 1.09/0.99  --sat_fm_lemmas                         false
% 1.09/0.99  --sat_fm_prep                           false
% 1.09/0.99  --sat_fm_uc_incr                        true
% 1.09/0.99  --sat_out_model                         small
% 1.09/0.99  --sat_out_clauses                       false
% 1.09/0.99  
% 1.09/0.99  ------ QBF Options
% 1.09/0.99  
% 1.09/0.99  --qbf_mode                              false
% 1.09/0.99  --qbf_elim_univ                         false
% 1.09/0.99  --qbf_dom_inst                          none
% 1.09/0.99  --qbf_dom_pre_inst                      false
% 1.09/0.99  --qbf_sk_in                             false
% 1.09/0.99  --qbf_pred_elim                         true
% 1.09/0.99  --qbf_split                             512
% 1.09/0.99  
% 1.09/0.99  ------ BMC1 Options
% 1.09/0.99  
% 1.09/0.99  --bmc1_incremental                      false
% 1.09/0.99  --bmc1_axioms                           reachable_all
% 1.09/0.99  --bmc1_min_bound                        0
% 1.09/0.99  --bmc1_max_bound                        -1
% 1.09/0.99  --bmc1_max_bound_default                -1
% 1.09/1.00  --bmc1_symbol_reachability              true
% 1.09/1.00  --bmc1_property_lemmas                  false
% 1.09/1.00  --bmc1_k_induction                      false
% 1.09/1.00  --bmc1_non_equiv_states                 false
% 1.09/1.00  --bmc1_deadlock                         false
% 1.09/1.00  --bmc1_ucm                              false
% 1.09/1.00  --bmc1_add_unsat_core                   none
% 1.09/1.00  --bmc1_unsat_core_children              false
% 1.09/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.09/1.00  --bmc1_out_stat                         full
% 1.09/1.00  --bmc1_ground_init                      false
% 1.09/1.00  --bmc1_pre_inst_next_state              false
% 1.09/1.00  --bmc1_pre_inst_state                   false
% 1.09/1.00  --bmc1_pre_inst_reach_state             false
% 1.09/1.00  --bmc1_out_unsat_core                   false
% 1.09/1.00  --bmc1_aig_witness_out                  false
% 1.09/1.00  --bmc1_verbose                          false
% 1.09/1.00  --bmc1_dump_clauses_tptp                false
% 1.09/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.09/1.00  --bmc1_dump_file                        -
% 1.09/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.09/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.09/1.00  --bmc1_ucm_extend_mode                  1
% 1.09/1.00  --bmc1_ucm_init_mode                    2
% 1.09/1.00  --bmc1_ucm_cone_mode                    none
% 1.09/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.09/1.00  --bmc1_ucm_relax_model                  4
% 1.09/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.09/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.09/1.00  --bmc1_ucm_layered_model                none
% 1.09/1.00  --bmc1_ucm_max_lemma_size               10
% 1.09/1.00  
% 1.09/1.00  ------ AIG Options
% 1.09/1.00  
% 1.09/1.00  --aig_mode                              false
% 1.09/1.00  
% 1.09/1.00  ------ Instantiation Options
% 1.09/1.00  
% 1.09/1.00  --instantiation_flag                    true
% 1.09/1.00  --inst_sos_flag                         false
% 1.09/1.00  --inst_sos_phase                        true
% 1.09/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.09/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.09/1.00  --inst_lit_sel_side                     none
% 1.09/1.00  --inst_solver_per_active                1400
% 1.09/1.00  --inst_solver_calls_frac                1.
% 1.09/1.00  --inst_passive_queue_type               priority_queues
% 1.09/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.09/1.00  --inst_passive_queues_freq              [25;2]
% 1.09/1.00  --inst_dismatching                      true
% 1.09/1.00  --inst_eager_unprocessed_to_passive     true
% 1.09/1.00  --inst_prop_sim_given                   true
% 1.09/1.00  --inst_prop_sim_new                     false
% 1.09/1.00  --inst_subs_new                         false
% 1.09/1.00  --inst_eq_res_simp                      false
% 1.09/1.00  --inst_subs_given                       false
% 1.09/1.00  --inst_orphan_elimination               true
% 1.09/1.00  --inst_learning_loop_flag               true
% 1.09/1.00  --inst_learning_start                   3000
% 1.09/1.00  --inst_learning_factor                  2
% 1.09/1.00  --inst_start_prop_sim_after_learn       3
% 1.09/1.00  --inst_sel_renew                        solver
% 1.09/1.00  --inst_lit_activity_flag                true
% 1.09/1.00  --inst_restr_to_given                   false
% 1.09/1.00  --inst_activity_threshold               500
% 1.09/1.00  --inst_out_proof                        true
% 1.09/1.00  
% 1.09/1.00  ------ Resolution Options
% 1.09/1.00  
% 1.09/1.00  --resolution_flag                       false
% 1.09/1.00  --res_lit_sel                           adaptive
% 1.09/1.00  --res_lit_sel_side                      none
% 1.09/1.00  --res_ordering                          kbo
% 1.09/1.00  --res_to_prop_solver                    active
% 1.09/1.00  --res_prop_simpl_new                    false
% 1.09/1.00  --res_prop_simpl_given                  true
% 1.09/1.00  --res_passive_queue_type                priority_queues
% 1.09/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.09/1.00  --res_passive_queues_freq               [15;5]
% 1.09/1.00  --res_forward_subs                      full
% 1.09/1.00  --res_backward_subs                     full
% 1.09/1.00  --res_forward_subs_resolution           true
% 1.09/1.00  --res_backward_subs_resolution          true
% 1.09/1.00  --res_orphan_elimination                true
% 1.09/1.00  --res_time_limit                        2.
% 1.09/1.00  --res_out_proof                         true
% 1.09/1.00  
% 1.09/1.00  ------ Superposition Options
% 1.09/1.00  
% 1.09/1.00  --superposition_flag                    true
% 1.09/1.00  --sup_passive_queue_type                priority_queues
% 1.09/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.09/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.09/1.00  --demod_completeness_check              fast
% 1.09/1.00  --demod_use_ground                      true
% 1.09/1.00  --sup_to_prop_solver                    passive
% 1.09/1.00  --sup_prop_simpl_new                    true
% 1.09/1.00  --sup_prop_simpl_given                  true
% 1.09/1.00  --sup_fun_splitting                     false
% 1.09/1.00  --sup_smt_interval                      50000
% 1.09/1.00  
% 1.09/1.00  ------ Superposition Simplification Setup
% 1.09/1.00  
% 1.09/1.00  --sup_indices_passive                   []
% 1.09/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.09/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.09/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/1.00  --sup_full_bw                           [BwDemod]
% 1.09/1.00  --sup_immed_triv                        [TrivRules]
% 1.09/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.09/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/1.00  --sup_immed_bw_main                     []
% 1.09/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.09/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.09/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.09/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.09/1.00  
% 1.09/1.00  ------ Combination Options
% 1.09/1.00  
% 1.09/1.00  --comb_res_mult                         3
% 1.09/1.00  --comb_sup_mult                         2
% 1.09/1.00  --comb_inst_mult                        10
% 1.09/1.00  
% 1.09/1.00  ------ Debug Options
% 1.09/1.00  
% 1.09/1.00  --dbg_backtrace                         false
% 1.09/1.00  --dbg_dump_prop_clauses                 false
% 1.09/1.00  --dbg_dump_prop_clauses_file            -
% 1.09/1.00  --dbg_out_stat                          false
% 1.09/1.00  
% 1.09/1.00  
% 1.09/1.00  
% 1.09/1.00  
% 1.09/1.00  ------ Proving...
% 1.09/1.00  
% 1.09/1.00  
% 1.09/1.00  % SZS status Theorem for theBenchmark.p
% 1.09/1.00  
% 1.09/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.09/1.00  
% 1.09/1.00  fof(f12,axiom,(
% 1.09/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f54,plain,(
% 1.09/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.09/1.00    inference(cnf_transformation,[],[f12])).
% 1.09/1.00  
% 1.09/1.00  fof(f15,axiom,(
% 1.09/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f58,plain,(
% 1.09/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.09/1.00    inference(cnf_transformation,[],[f15])).
% 1.09/1.00  
% 1.09/1.00  fof(f73,plain,(
% 1.09/1.00    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.09/1.00    inference(definition_unfolding,[],[f54,f58])).
% 1.09/1.00  
% 1.09/1.00  fof(f14,axiom,(
% 1.09/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f28,plain,(
% 1.09/1.00    ! [X0] : v1_partfun1(k6_partfun1(X0),X0)),
% 1.09/1.00    inference(pure_predicate_removal,[],[f14])).
% 1.09/1.00  
% 1.09/1.00  fof(f57,plain,(
% 1.09/1.00    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 1.09/1.00    inference(cnf_transformation,[],[f28])).
% 1.09/1.00  
% 1.09/1.00  fof(f13,axiom,(
% 1.09/1.00    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f56,plain,(
% 1.09/1.00    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.09/1.00    inference(cnf_transformation,[],[f13])).
% 1.09/1.00  
% 1.09/1.00  fof(f74,plain,(
% 1.09/1.00    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 1.09/1.00    inference(definition_unfolding,[],[f56,f58])).
% 1.09/1.00  
% 1.09/1.00  fof(f21,axiom,(
% 1.09/1.00    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f33,plain,(
% 1.09/1.00    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 1.09/1.00    inference(ennf_transformation,[],[f21])).
% 1.09/1.00  
% 1.09/1.00  fof(f34,plain,(
% 1.09/1.00    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.09/1.00    inference(flattening,[],[f33])).
% 1.09/1.00  
% 1.09/1.00  fof(f64,plain,(
% 1.09/1.00    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.09/1.00    inference(cnf_transformation,[],[f34])).
% 1.09/1.00  
% 1.09/1.00  fof(f3,axiom,(
% 1.09/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f43,plain,(
% 1.09/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.09/1.00    inference(cnf_transformation,[],[f3])).
% 1.09/1.00  
% 1.09/1.00  fof(f4,axiom,(
% 1.09/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f44,plain,(
% 1.09/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.09/1.00    inference(cnf_transformation,[],[f4])).
% 1.09/1.00  
% 1.09/1.00  fof(f5,axiom,(
% 1.09/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f45,plain,(
% 1.09/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.09/1.00    inference(cnf_transformation,[],[f5])).
% 1.09/1.00  
% 1.09/1.00  fof(f6,axiom,(
% 1.09/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f46,plain,(
% 1.09/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.09/1.00    inference(cnf_transformation,[],[f6])).
% 1.09/1.00  
% 1.09/1.00  fof(f7,axiom,(
% 1.09/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f47,plain,(
% 1.09/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.09/1.00    inference(cnf_transformation,[],[f7])).
% 1.09/1.00  
% 1.09/1.00  fof(f8,axiom,(
% 1.09/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f48,plain,(
% 1.09/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.09/1.00    inference(cnf_transformation,[],[f8])).
% 1.09/1.00  
% 1.09/1.00  fof(f9,axiom,(
% 1.09/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f49,plain,(
% 1.09/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.09/1.00    inference(cnf_transformation,[],[f9])).
% 1.09/1.00  
% 1.09/1.00  fof(f67,plain,(
% 1.09/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.09/1.00    inference(definition_unfolding,[],[f48,f49])).
% 1.09/1.00  
% 1.09/1.00  fof(f68,plain,(
% 1.09/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.09/1.00    inference(definition_unfolding,[],[f47,f67])).
% 1.09/1.00  
% 1.09/1.00  fof(f69,plain,(
% 1.09/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.09/1.00    inference(definition_unfolding,[],[f46,f68])).
% 1.09/1.00  
% 1.09/1.00  fof(f70,plain,(
% 1.09/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.09/1.00    inference(definition_unfolding,[],[f45,f69])).
% 1.09/1.00  
% 1.09/1.00  fof(f71,plain,(
% 1.09/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.09/1.00    inference(definition_unfolding,[],[f44,f70])).
% 1.09/1.00  
% 1.09/1.00  fof(f72,plain,(
% 1.09/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.09/1.00    inference(definition_unfolding,[],[f43,f71])).
% 1.09/1.00  
% 1.09/1.00  fof(f77,plain,(
% 1.09/1.00    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.09/1.00    inference(definition_unfolding,[],[f64,f72,f72])).
% 1.09/1.00  
% 1.09/1.00  fof(f55,plain,(
% 1.09/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.09/1.00    inference(cnf_transformation,[],[f13])).
% 1.09/1.00  
% 1.09/1.00  fof(f75,plain,(
% 1.09/1.00    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 1.09/1.00    inference(definition_unfolding,[],[f55,f58])).
% 1.09/1.00  
% 1.09/1.00  fof(f1,axiom,(
% 1.09/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f29,plain,(
% 1.09/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.09/1.00    inference(ennf_transformation,[],[f1])).
% 1.09/1.00  
% 1.09/1.00  fof(f41,plain,(
% 1.09/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.09/1.00    inference(cnf_transformation,[],[f29])).
% 1.09/1.00  
% 1.09/1.00  fof(f19,axiom,(
% 1.09/1.00    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f62,plain,(
% 1.09/1.00    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 1.09/1.00    inference(cnf_transformation,[],[f19])).
% 1.09/1.00  
% 1.09/1.00  fof(f17,axiom,(
% 1.09/1.00    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f31,plain,(
% 1.09/1.00    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 1.09/1.00    inference(ennf_transformation,[],[f17])).
% 1.09/1.00  
% 1.09/1.00  fof(f60,plain,(
% 1.09/1.00    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 1.09/1.00    inference(cnf_transformation,[],[f31])).
% 1.09/1.00  
% 1.09/1.00  fof(f20,axiom,(
% 1.09/1.00    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f63,plain,(
% 1.09/1.00    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 1.09/1.00    inference(cnf_transformation,[],[f20])).
% 1.09/1.00  
% 1.09/1.00  fof(f76,plain,(
% 1.09/1.00    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 1.09/1.00    inference(definition_unfolding,[],[f60,f63])).
% 1.09/1.00  
% 1.09/1.00  fof(f22,conjecture,(
% 1.09/1.00    ! [X0] : (l1_orders_2(X0) => k6_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f23,negated_conjecture,(
% 1.09/1.00    ~! [X0] : (l1_orders_2(X0) => k6_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 1.09/1.00    inference(negated_conjecture,[],[f22])).
% 1.09/1.00  
% 1.09/1.00  fof(f35,plain,(
% 1.09/1.00    ? [X0] : (k6_yellow_1(k1_xboole_0,X0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) & l1_orders_2(X0))),
% 1.09/1.00    inference(ennf_transformation,[],[f23])).
% 1.09/1.00  
% 1.09/1.00  fof(f39,plain,(
% 1.09/1.00    ? [X0] : (k6_yellow_1(k1_xboole_0,X0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) & l1_orders_2(X0)) => (k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) & l1_orders_2(sK1))),
% 1.09/1.00    introduced(choice_axiom,[])).
% 1.09/1.00  
% 1.09/1.00  fof(f40,plain,(
% 1.09/1.00    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) & l1_orders_2(sK1)),
% 1.09/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f39])).
% 1.09/1.00  
% 1.09/1.00  fof(f65,plain,(
% 1.09/1.00    l1_orders_2(sK1)),
% 1.09/1.00    inference(cnf_transformation,[],[f40])).
% 1.09/1.00  
% 1.09/1.00  fof(f2,axiom,(
% 1.09/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f42,plain,(
% 1.09/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.09/1.00    inference(cnf_transformation,[],[f2])).
% 1.09/1.00  
% 1.09/1.00  fof(f10,axiom,(
% 1.09/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f30,plain,(
% 1.09/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.09/1.00    inference(ennf_transformation,[],[f10])).
% 1.09/1.00  
% 1.09/1.00  fof(f36,plain,(
% 1.09/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.09/1.00    inference(nnf_transformation,[],[f30])).
% 1.09/1.00  
% 1.09/1.00  fof(f51,plain,(
% 1.09/1.00    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.09/1.00    inference(cnf_transformation,[],[f36])).
% 1.09/1.00  
% 1.09/1.00  fof(f66,plain,(
% 1.09/1.00    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))),
% 1.09/1.00    inference(cnf_transformation,[],[f40])).
% 1.09/1.00  
% 1.09/1.00  fof(f78,plain,(
% 1.09/1.00    k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 1.09/1.00    inference(definition_unfolding,[],[f66,f72,f72])).
% 1.09/1.00  
% 1.09/1.00  fof(f11,axiom,(
% 1.09/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f52,plain,(
% 1.09/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.09/1.00    inference(cnf_transformation,[],[f11])).
% 1.09/1.00  
% 1.09/1.00  fof(f18,axiom,(
% 1.09/1.00    ! [X0,X1] : (l1_orders_2(X1) => v1_yellow_1(k2_funcop_1(X0,X1)))),
% 1.09/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.09/1.00  
% 1.09/1.00  fof(f32,plain,(
% 1.09/1.00    ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 1.09/1.00    inference(ennf_transformation,[],[f18])).
% 1.09/1.00  
% 1.09/1.00  fof(f61,plain,(
% 1.09/1.00    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 1.09/1.00    inference(cnf_transformation,[],[f32])).
% 1.09/1.00  
% 1.09/1.00  cnf(c_488,plain,
% 1.09/1.00      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 1.09/1.00      theory(equality) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_903,plain,
% 1.09/1.00      ( X0_47 != X1_47
% 1.09/1.00      | X0_47 = k6_partfun1(X2_47)
% 1.09/1.00      | k6_partfun1(X2_47) != X1_47 ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_488]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_904,plain,
% 1.09/1.00      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 1.09/1.00      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 1.09/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_903]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_490,plain,
% 1.09/1.00      ( ~ v4_relat_1(X0_47,X1_47)
% 1.09/1.00      | v4_relat_1(X2_47,X3_47)
% 1.09/1.00      | X2_47 != X0_47
% 1.09/1.00      | X3_47 != X1_47 ),
% 1.09/1.00      theory(equality) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_799,plain,
% 1.09/1.00      ( v4_relat_1(X0_47,X1_47)
% 1.09/1.00      | ~ v4_relat_1(k6_partfun1(X2_47),X3_47)
% 1.09/1.00      | X1_47 != X3_47
% 1.09/1.00      | X0_47 != k6_partfun1(X2_47) ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_490]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_801,plain,
% 1.09/1.00      ( ~ v4_relat_1(k6_partfun1(k1_xboole_0),k1_xboole_0)
% 1.09/1.00      | v4_relat_1(k1_xboole_0,k1_xboole_0)
% 1.09/1.00      | k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 1.09/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_799]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_6,plain,
% 1.09/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 1.09/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_482,plain,
% 1.09/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 1.09/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_9,plain,
% 1.09/1.00      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 1.09/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_7,plain,
% 1.09/1.00      ( v1_funct_1(k6_partfun1(X0)) ),
% 1.09/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_14,plain,
% 1.09/1.00      ( ~ v1_partfun1(X0,k1_xboole_0)
% 1.09/1.00      | ~ v4_relat_1(X0,k1_xboole_0)
% 1.09/1.00      | ~ v1_yellow_1(X0)
% 1.09/1.00      | ~ v1_funct_1(X0)
% 1.09/1.00      | ~ v1_relat_1(X0)
% 1.09/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,X0) ),
% 1.09/1.00      inference(cnf_transformation,[],[f77]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_208,plain,
% 1.09/1.00      ( ~ v1_partfun1(X0,k1_xboole_0)
% 1.09/1.00      | ~ v4_relat_1(X0,k1_xboole_0)
% 1.09/1.00      | ~ v1_yellow_1(X0)
% 1.09/1.00      | ~ v1_relat_1(X0)
% 1.09/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,X0)
% 1.09/1.00      | k6_partfun1(X1) != X0 ),
% 1.09/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_209,plain,
% 1.09/1.00      ( ~ v1_partfun1(k6_partfun1(X0),k1_xboole_0)
% 1.09/1.00      | ~ v4_relat_1(k6_partfun1(X0),k1_xboole_0)
% 1.09/1.00      | ~ v1_yellow_1(k6_partfun1(X0))
% 1.09/1.00      | ~ v1_relat_1(k6_partfun1(X0))
% 1.09/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0)) ),
% 1.09/1.00      inference(unflattening,[status(thm)],[c_208]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_8,plain,
% 1.09/1.00      ( v1_relat_1(k6_partfun1(X0)) ),
% 1.09/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_213,plain,
% 1.09/1.00      ( ~ v1_yellow_1(k6_partfun1(X0))
% 1.09/1.00      | ~ v4_relat_1(k6_partfun1(X0),k1_xboole_0)
% 1.09/1.00      | ~ v1_partfun1(k6_partfun1(X0),k1_xboole_0)
% 1.09/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0)) ),
% 1.09/1.00      inference(global_propositional_subsumption,
% 1.09/1.00                [status(thm)],
% 1.09/1.00                [c_209,c_8]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_214,plain,
% 1.09/1.00      ( ~ v1_partfun1(k6_partfun1(X0),k1_xboole_0)
% 1.09/1.00      | ~ v4_relat_1(k6_partfun1(X0),k1_xboole_0)
% 1.09/1.00      | ~ v1_yellow_1(k6_partfun1(X0))
% 1.09/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0)) ),
% 1.09/1.00      inference(renaming,[status(thm)],[c_213]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_237,plain,
% 1.09/1.00      ( ~ v4_relat_1(k6_partfun1(X0),k1_xboole_0)
% 1.09/1.00      | ~ v1_yellow_1(k6_partfun1(X0))
% 1.09/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0))
% 1.09/1.00      | k6_partfun1(X0) != k6_partfun1(X1)
% 1.09/1.00      | k1_xboole_0 != X1 ),
% 1.09/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_214]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_238,plain,
% 1.09/1.00      ( ~ v4_relat_1(k6_partfun1(X0),k1_xboole_0)
% 1.09/1.00      | ~ v1_yellow_1(k6_partfun1(X0))
% 1.09/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0))
% 1.09/1.00      | k6_partfun1(X0) != k6_partfun1(k1_xboole_0) ),
% 1.09/1.00      inference(unflattening,[status(thm)],[c_237]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_475,plain,
% 1.09/1.00      ( ~ v4_relat_1(k6_partfun1(X0_47),k1_xboole_0)
% 1.09/1.00      | ~ v1_yellow_1(k6_partfun1(X0_47))
% 1.09/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0_47))
% 1.09/1.00      | k6_partfun1(X0_47) != k6_partfun1(k1_xboole_0) ),
% 1.09/1.00      inference(subtyping,[status(esa)],[c_238]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_606,plain,
% 1.09/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0_47))
% 1.09/1.00      | k6_partfun1(X0_47) != k6_partfun1(k1_xboole_0)
% 1.09/1.00      | v4_relat_1(k6_partfun1(X0_47),k1_xboole_0) != iProver_top
% 1.09/1.00      | v1_yellow_1(k6_partfun1(X0_47)) != iProver_top ),
% 1.09/1.00      inference(predicate_to_equality,[status(thm)],[c_475]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_630,plain,
% 1.09/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(X0_47))
% 1.09/1.00      | k6_partfun1(X0_47) != k1_xboole_0
% 1.09/1.00      | v4_relat_1(k6_partfun1(X0_47),k1_xboole_0) != iProver_top
% 1.09/1.00      | v1_yellow_1(k6_partfun1(X0_47)) != iProver_top ),
% 1.09/1.00      inference(light_normalisation,[status(thm)],[c_606,c_482]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_761,plain,
% 1.09/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k6_partfun1(k1_xboole_0))
% 1.09/1.00      | v4_relat_1(k6_partfun1(k1_xboole_0),k1_xboole_0) != iProver_top
% 1.09/1.00      | v1_yellow_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 1.09/1.00      inference(superposition,[status(thm)],[c_482,c_630]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_0,plain,
% 1.09/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.09/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_13,plain,
% 1.09/1.00      ( v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
% 1.09/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_165,plain,
% 1.09/1.00      ( k2_funcop_1(k1_xboole_0,X0) != X1 | k1_xboole_0 = X1 ),
% 1.09/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_13]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_166,plain,
% 1.09/1.00      ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) ),
% 1.09/1.00      inference(unflattening,[status(thm)],[c_165]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_480,plain,
% 1.09/1.00      ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0_49) ),
% 1.09/1.00      inference(subtyping,[status(esa)],[c_166]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_11,plain,
% 1.09/1.00      ( ~ l1_orders_2(X0)
% 1.09/1.00      | k5_yellow_1(X1,k2_funcop_1(X1,X0)) = k6_yellow_1(X1,X0) ),
% 1.09/1.00      inference(cnf_transformation,[],[f76]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_16,negated_conjecture,
% 1.09/1.00      ( l1_orders_2(sK1) ),
% 1.09/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_196,plain,
% 1.09/1.00      ( k5_yellow_1(X0,k2_funcop_1(X0,X1)) = k6_yellow_1(X0,X1)
% 1.09/1.00      | sK1 != X1 ),
% 1.09/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_197,plain,
% 1.09/1.00      ( k5_yellow_1(X0,k2_funcop_1(X0,sK1)) = k6_yellow_1(X0,sK1) ),
% 1.09/1.00      inference(unflattening,[status(thm)],[c_196]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_476,plain,
% 1.09/1.00      ( k5_yellow_1(X0_47,k2_funcop_1(X0_47,sK1)) = k6_yellow_1(X0_47,sK1) ),
% 1.09/1.00      inference(subtyping,[status(esa)],[c_197]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_716,plain,
% 1.09/1.00      ( k5_yellow_1(k1_xboole_0,k1_xboole_0) = k6_yellow_1(k1_xboole_0,sK1) ),
% 1.09/1.00      inference(superposition,[status(thm)],[c_480,c_476]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_762,plain,
% 1.09/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK1)
% 1.09/1.00      | v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
% 1.09/1.00      | v1_yellow_1(k1_xboole_0) != iProver_top ),
% 1.09/1.00      inference(light_normalisation,[status(thm)],[c_761,c_482,c_716]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_763,plain,
% 1.09/1.00      ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
% 1.09/1.00      | ~ v1_yellow_1(k1_xboole_0)
% 1.09/1.00      | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k6_yellow_1(k1_xboole_0,sK1) ),
% 1.09/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_762]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_725,plain,
% 1.09/1.00      ( k1_relat_1(X0_47) != X1_47
% 1.09/1.00      | k1_xboole_0 != X1_47
% 1.09/1.00      | k1_xboole_0 = k1_relat_1(X0_47) ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_488]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_726,plain,
% 1.09/1.00      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 1.09/1.00      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 1.09/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_725]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_491,plain,
% 1.09/1.00      ( X0_47 != X1_47 | k1_relat_1(X0_47) = k1_relat_1(X1_47) ),
% 1.09/1.00      theory(equality) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_690,plain,
% 1.09/1.00      ( k6_partfun1(X0_47) != X1_47
% 1.09/1.00      | k1_relat_1(k6_partfun1(X0_47)) = k1_relat_1(X1_47) ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_491]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_692,plain,
% 1.09/1.00      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 1.09/1.00      | k1_relat_1(k6_partfun1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_690]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_658,plain,
% 1.09/1.00      ( k1_relat_1(k6_partfun1(X0_47)) != X1_47
% 1.09/1.00      | k1_relat_1(k6_partfun1(X0_47)) = k1_xboole_0
% 1.09/1.00      | k1_xboole_0 != X1_47 ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_488]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_689,plain,
% 1.09/1.00      ( k1_relat_1(k6_partfun1(X0_47)) != k1_relat_1(X1_47)
% 1.09/1.00      | k1_relat_1(k6_partfun1(X0_47)) = k1_xboole_0
% 1.09/1.00      | k1_xboole_0 != k1_relat_1(X1_47) ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_658]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_691,plain,
% 1.09/1.00      ( k1_relat_1(k6_partfun1(k1_xboole_0)) != k1_relat_1(k1_xboole_0)
% 1.09/1.00      | k1_relat_1(k6_partfun1(k1_xboole_0)) = k1_xboole_0
% 1.09/1.00      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_689]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_489,plain,
% 1.09/1.00      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 1.09/1.00      theory(equality) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_659,plain,
% 1.09/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != X0_48
% 1.09/1.00      | k6_yellow_1(k1_xboole_0,sK1) != X0_48
% 1.09/1.00      | k6_yellow_1(k1_xboole_0,sK1) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_489]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_669,plain,
% 1.09/1.00      ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK1)
% 1.09/1.00      | k6_yellow_1(k1_xboole_0,sK1) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
% 1.09/1.00      | k6_yellow_1(k1_xboole_0,sK1) != k6_yellow_1(k1_xboole_0,sK1) ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_659]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_497,plain,
% 1.09/1.00      ( ~ v1_yellow_1(X0_47) | v1_yellow_1(X1_47) | X1_47 != X0_47 ),
% 1.09/1.00      theory(equality) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_653,plain,
% 1.09/1.00      ( v1_yellow_1(X0_47)
% 1.09/1.00      | ~ v1_yellow_1(k2_funcop_1(X1_47,sK1))
% 1.09/1.00      | X0_47 != k2_funcop_1(X1_47,sK1) ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_497]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_655,plain,
% 1.09/1.00      ( ~ v1_yellow_1(k2_funcop_1(k1_xboole_0,sK1))
% 1.09/1.00      | v1_yellow_1(k1_xboole_0)
% 1.09/1.00      | k1_xboole_0 != k2_funcop_1(k1_xboole_0,sK1) ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_653]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_1,plain,
% 1.09/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 1.09/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_2,plain,
% 1.09/1.00      ( v4_relat_1(X0,X1)
% 1.09/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.09/1.00      | ~ v1_relat_1(X0) ),
% 1.09/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_272,plain,
% 1.09/1.00      ( v4_relat_1(X0,X1)
% 1.09/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.09/1.00      | k6_partfun1(X2) != X0 ),
% 1.09/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_8]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_273,plain,
% 1.09/1.00      ( v4_relat_1(k6_partfun1(X0),X1)
% 1.09/1.00      | ~ r1_tarski(k1_relat_1(k6_partfun1(X0)),X1) ),
% 1.09/1.00      inference(unflattening,[status(thm)],[c_272]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_291,plain,
% 1.09/1.00      ( v4_relat_1(k6_partfun1(X0),X1)
% 1.09/1.00      | X1 != X2
% 1.09/1.00      | k1_relat_1(k6_partfun1(X0)) != k1_xboole_0 ),
% 1.09/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_273]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_292,plain,
% 1.09/1.00      ( v4_relat_1(k6_partfun1(X0),X1)
% 1.09/1.00      | k1_relat_1(k6_partfun1(X0)) != k1_xboole_0 ),
% 1.09/1.00      inference(unflattening,[status(thm)],[c_291]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_474,plain,
% 1.09/1.00      ( v4_relat_1(k6_partfun1(X0_47),X1_47)
% 1.09/1.00      | k1_relat_1(k6_partfun1(X0_47)) != k1_xboole_0 ),
% 1.09/1.00      inference(subtyping,[status(esa)],[c_292]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_522,plain,
% 1.09/1.00      ( v4_relat_1(k6_partfun1(k1_xboole_0),k1_xboole_0)
% 1.09/1.00      | k1_relat_1(k6_partfun1(k1_xboole_0)) != k1_xboole_0 ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_474]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_513,plain,
% 1.09/1.00      ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,sK1) ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_480]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_15,negated_conjecture,
% 1.09/1.00      ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
% 1.09/1.00      inference(cnf_transformation,[],[f78]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_481,negated_conjecture,
% 1.09/1.00      ( k6_yellow_1(k1_xboole_0,sK1) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
% 1.09/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_5,plain,
% 1.09/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.09/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_483,plain,
% 1.09/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.09/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_486,plain,( X0_47 = X0_47 ),theory(equality) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_511,plain,
% 1.09/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_486]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_494,plain,
% 1.09/1.00      ( k6_yellow_1(X0_47,X0_49) = k6_yellow_1(X1_47,X0_49)
% 1.09/1.00      | X0_47 != X1_47 ),
% 1.09/1.00      theory(equality) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_504,plain,
% 1.09/1.00      ( k6_yellow_1(k1_xboole_0,sK1) = k6_yellow_1(k1_xboole_0,sK1)
% 1.09/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_494]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_12,plain,
% 1.09/1.00      ( v1_yellow_1(k2_funcop_1(X0,X1)) | ~ l1_orders_2(X1) ),
% 1.09/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_187,plain,
% 1.09/1.00      ( v1_yellow_1(k2_funcop_1(X0,X1)) | sK1 != X1 ),
% 1.09/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_188,plain,
% 1.09/1.00      ( v1_yellow_1(k2_funcop_1(X0,sK1)) ),
% 1.09/1.00      inference(unflattening,[status(thm)],[c_187]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(c_190,plain,
% 1.09/1.00      ( v1_yellow_1(k2_funcop_1(k1_xboole_0,sK1)) ),
% 1.09/1.00      inference(instantiation,[status(thm)],[c_188]) ).
% 1.09/1.00  
% 1.09/1.00  cnf(contradiction,plain,
% 1.09/1.00      ( $false ),
% 1.09/1.00      inference(minisat,
% 1.09/1.00                [status(thm)],
% 1.09/1.00                [c_904,c_801,c_763,c_726,c_692,c_691,c_669,c_655,c_522,
% 1.09/1.00                 c_513,c_481,c_482,c_483,c_511,c_504,c_190]) ).
% 1.09/1.00  
% 1.09/1.00  
% 1.09/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.09/1.00  
% 1.09/1.00  ------                               Statistics
% 1.09/1.00  
% 1.09/1.00  ------ General
% 1.09/1.00  
% 1.09/1.00  abstr_ref_over_cycles:                  0
% 1.09/1.00  abstr_ref_under_cycles:                 0
% 1.09/1.00  gc_basic_clause_elim:                   0
% 1.09/1.00  forced_gc_time:                         0
% 1.09/1.00  parsing_time:                           0.007
% 1.09/1.00  unif_index_cands_time:                  0.
% 1.09/1.00  unif_index_add_time:                    0.
% 1.09/1.00  orderings_time:                         0.
% 1.09/1.00  out_proof_time:                         0.009
% 1.09/1.00  total_time:                             0.046
% 1.09/1.00  num_of_symbols:                         50
% 1.09/1.00  num_of_terms:                           1047
% 1.09/1.00  
% 1.09/1.00  ------ Preprocessing
% 1.09/1.00  
% 1.09/1.00  num_of_splits:                          0
% 1.09/1.00  num_of_split_atoms:                     0
% 1.09/1.00  num_of_reused_defs:                     0
% 1.09/1.00  num_eq_ax_congr_red:                    5
% 1.09/1.00  num_of_sem_filtered_clauses:            1
% 1.09/1.00  num_of_subtypes:                        3
% 1.09/1.00  monotx_restored_types:                  0
% 1.09/1.00  sat_num_of_epr_types:                   0
% 1.09/1.00  sat_num_of_non_cyclic_types:            0
% 1.09/1.00  sat_guarded_non_collapsed_types:        0
% 1.09/1.00  num_pure_diseq_elim:                    0
% 1.09/1.00  simp_replaced_by:                       0
% 1.09/1.00  res_preprocessed:                       79
% 1.09/1.00  prep_upred:                             0
% 1.09/1.00  prep_unflattend:                        12
% 1.09/1.00  smt_new_axioms:                         0
% 1.09/1.00  pred_elim_cands:                        2
% 1.09/1.00  pred_elim:                              6
% 1.09/1.00  pred_elim_cl:                           6
% 1.09/1.00  pred_elim_cycles:                       10
% 1.09/1.00  merged_defs:                            0
% 1.09/1.00  merged_defs_ncl:                        0
% 1.09/1.00  bin_hyper_res:                          0
% 1.09/1.00  prep_cycles:                            4
% 1.09/1.00  pred_elim_time:                         0.003
% 1.09/1.00  splitting_time:                         0.
% 1.09/1.00  sem_filter_time:                        0.
% 1.09/1.00  monotx_time:                            0.
% 1.09/1.00  subtype_inf_time:                       0.
% 1.09/1.00  
% 1.09/1.00  ------ Problem properties
% 1.09/1.00  
% 1.09/1.00  clauses:                                11
% 1.09/1.00  conjectures:                            1
% 1.09/1.00  epr:                                    0
% 1.09/1.00  horn:                                   11
% 1.09/1.00  ground:                                 4
% 1.09/1.00  unary:                                  9
% 1.09/1.00  binary:                                 1
% 1.09/1.00  lits:                                   15
% 1.09/1.00  lits_eq:                                10
% 1.09/1.00  fd_pure:                                0
% 1.09/1.00  fd_pseudo:                              0
% 1.09/1.00  fd_cond:                                0
% 1.09/1.00  fd_pseudo_cond:                         0
% 1.09/1.00  ac_symbols:                             0
% 1.09/1.00  
% 1.09/1.00  ------ Propositional Solver
% 1.09/1.00  
% 1.09/1.00  prop_solver_calls:                      27
% 1.09/1.00  prop_fast_solver_calls:                 382
% 1.09/1.00  smt_solver_calls:                       0
% 1.09/1.00  smt_fast_solver_calls:                  0
% 1.09/1.00  prop_num_of_clauses:                    280
% 1.09/1.00  prop_preprocess_simplified:             1755
% 1.09/1.00  prop_fo_subsumed:                       3
% 1.09/1.00  prop_solver_time:                       0.
% 1.09/1.00  smt_solver_time:                        0.
% 1.09/1.00  smt_fast_solver_time:                   0.
% 1.09/1.00  prop_fast_solver_time:                  0.
% 1.09/1.00  prop_unsat_core_time:                   0.
% 1.09/1.00  
% 1.09/1.00  ------ QBF
% 1.09/1.00  
% 1.09/1.00  qbf_q_res:                              0
% 1.09/1.00  qbf_num_tautologies:                    0
% 1.09/1.00  qbf_prep_cycles:                        0
% 1.09/1.00  
% 1.09/1.00  ------ BMC1
% 1.09/1.00  
% 1.09/1.00  bmc1_current_bound:                     -1
% 1.09/1.00  bmc1_last_solved_bound:                 -1
% 1.09/1.00  bmc1_unsat_core_size:                   -1
% 1.09/1.00  bmc1_unsat_core_parents_size:           -1
% 1.09/1.00  bmc1_merge_next_fun:                    0
% 1.09/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.09/1.00  
% 1.09/1.00  ------ Instantiation
% 1.09/1.00  
% 1.09/1.00  inst_num_of_clauses:                    97
% 1.09/1.00  inst_num_in_passive:                    0
% 1.09/1.00  inst_num_in_active:                     71
% 1.09/1.00  inst_num_in_unprocessed:                25
% 1.09/1.00  inst_num_of_loops:                      84
% 1.09/1.00  inst_num_of_learning_restarts:          0
% 1.09/1.00  inst_num_moves_active_passive:          8
% 1.09/1.00  inst_lit_activity:                      0
% 1.09/1.00  inst_lit_activity_moves:                0
% 1.09/1.00  inst_num_tautologies:                   0
% 1.09/1.00  inst_num_prop_implied:                  0
% 1.09/1.00  inst_num_existing_simplified:           0
% 1.09/1.00  inst_num_eq_res_simplified:             0
% 1.09/1.00  inst_num_child_elim:                    0
% 1.09/1.00  inst_num_of_dismatching_blockings:      3
% 1.09/1.00  inst_num_of_non_proper_insts:           68
% 1.09/1.00  inst_num_of_duplicates:                 0
% 1.09/1.00  inst_inst_num_from_inst_to_res:         0
% 1.09/1.00  inst_dismatching_checking_time:         0.
% 1.09/1.00  
% 1.09/1.00  ------ Resolution
% 1.09/1.00  
% 1.09/1.00  res_num_of_clauses:                     0
% 1.09/1.00  res_num_in_passive:                     0
% 1.09/1.00  res_num_in_active:                      0
% 1.09/1.00  res_num_of_loops:                       83
% 1.09/1.00  res_forward_subset_subsumed:            20
% 1.09/1.00  res_backward_subset_subsumed:           0
% 1.09/1.00  res_forward_subsumed:                   0
% 1.09/1.00  res_backward_subsumed:                  0
% 1.09/1.00  res_forward_subsumption_resolution:     0
% 1.09/1.00  res_backward_subsumption_resolution:    0
% 1.09/1.00  res_clause_to_clause_subsumption:       25
% 1.09/1.00  res_orphan_elimination:                 0
% 1.09/1.00  res_tautology_del:                      11
% 1.09/1.00  res_num_eq_res_simplified:              0
% 1.09/1.00  res_num_sel_changes:                    0
% 1.09/1.00  res_moves_from_active_to_pass:          0
% 1.09/1.00  
% 1.09/1.00  ------ Superposition
% 1.09/1.00  
% 1.09/1.00  sup_time_total:                         0.
% 1.09/1.00  sup_time_generating:                    0.
% 1.09/1.00  sup_time_sim_full:                      0.
% 1.09/1.00  sup_time_sim_immed:                     0.
% 1.09/1.00  
% 1.09/1.00  sup_num_of_clauses:                     15
% 1.09/1.00  sup_num_in_active:                      14
% 1.09/1.00  sup_num_in_passive:                     1
% 1.09/1.00  sup_num_of_loops:                       16
% 1.09/1.00  sup_fw_superposition:                   3
% 1.09/1.00  sup_bw_superposition:                   2
% 1.09/1.00  sup_immediate_simplified:               1
% 1.09/1.00  sup_given_eliminated:                   0
% 1.09/1.00  comparisons_done:                       0
% 1.09/1.00  comparisons_avoided:                    0
% 1.09/1.00  
% 1.09/1.00  ------ Simplifications
% 1.09/1.00  
% 1.09/1.00  
% 1.09/1.00  sim_fw_subset_subsumed:                 0
% 1.09/1.00  sim_bw_subset_subsumed:                 0
% 1.09/1.00  sim_fw_subsumed:                        0
% 1.09/1.00  sim_bw_subsumed:                        0
% 1.09/1.00  sim_fw_subsumption_res:                 0
% 1.09/1.00  sim_bw_subsumption_res:                 0
% 1.09/1.00  sim_tautology_del:                      0
% 1.09/1.00  sim_eq_tautology_del:                   0
% 1.09/1.00  sim_eq_res_simp:                        0
% 1.09/1.00  sim_fw_demodulated:                     0
% 1.09/1.00  sim_bw_demodulated:                     2
% 1.09/1.00  sim_light_normalised:                   2
% 1.09/1.00  sim_joinable_taut:                      0
% 1.09/1.00  sim_joinable_simp:                      0
% 1.09/1.00  sim_ac_normalised:                      0
% 1.09/1.00  sim_smt_subsumption:                    0
% 1.09/1.00  
%------------------------------------------------------------------------------
