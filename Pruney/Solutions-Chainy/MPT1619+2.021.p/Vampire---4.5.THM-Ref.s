%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:51 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 160 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :  160 ( 309 expanded)
%              Number of equality atoms :   67 ( 140 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(subsumption_resolution,[],[f96,f57])).

fof(f57,plain,(
    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f30,f56,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

fof(f96,plain,(
    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f95,f71])).

fof(f71,plain,(
    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f70,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f38,f32])).

fof(f32,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f70,plain,(
    ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0)) ),
    inference(resolution,[],[f62,f29])).

fof(f29,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) ) ),
    inference(definition_unfolding,[],[f49,f47])).

fof(f47,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f95,plain,(
    g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f94,f65])).

fof(f65,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f60,f58])).

fof(f58,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f33,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f31,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f60,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f94,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f93,f64])).

fof(f64,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f37,f58])).

fof(f37,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f93,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f92,f66])).

fof(f66,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f59,f58])).

fof(f59,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f36,f33])).

fof(f36,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f92,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f89,f81])).

fof(f81,plain,(
    v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f43,f78])).

fof(f78,plain,(
    k1_xboole_0 = sK1(k1_xboole_0) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = sK1(X1) ) ),
    inference(subsumption_resolution,[],[f76,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_yellow_1(X1)
      & v1_partfun1(X1,X0)
      & v1_funct_1(X1)
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_yellow_1)).

fof(f76,plain,(
    ! [X1] :
      ( k1_xboole_0 != X1
      | ~ v1_relat_1(sK1(X1))
      | k1_xboole_0 = sK1(X1) ) ),
    inference(superposition,[],[f39,f74])).

fof(f74,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(subsumption_resolution,[],[f73,f45])).

fof(f45,plain,(
    ! [X0] : v1_partfun1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X0] :
      ( k1_relat_1(sK1(X0)) = X0
      | ~ v1_partfun1(sK1(X0),X0) ) ),
    inference(subsumption_resolution,[],[f72,f42])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1(X0))
      | k1_relat_1(sK1(X0)) = X0
      | ~ v1_partfun1(sK1(X0),X0) ) ),
    inference(resolution,[],[f51,f43])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f43,plain,(
    ! [X0] : v4_relat_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f89,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f61,f82])).

fof(f82,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(superposition,[],[f46,f78])).

fof(f46,plain,(
    ! [X0] : v1_yellow_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_yellow_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0)
      | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ) ),
    inference(definition_unfolding,[],[f41,f56,f56])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_yellow_1(X0)
      | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:19:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (5138)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.53/0.57  % (5154)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.53/0.58  % (5138)Refutation found. Thanks to Tanya!
% 1.53/0.58  % SZS status Theorem for theBenchmark
% 1.53/0.58  % SZS output start Proof for theBenchmark
% 1.53/0.58  fof(f97,plain,(
% 1.53/0.58    $false),
% 1.53/0.58    inference(subsumption_resolution,[],[f96,f57])).
% 1.53/0.58  fof(f57,plain,(
% 1.53/0.58    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 1.53/0.58    inference(definition_unfolding,[],[f30,f56,f56])).
% 1.53/0.58  fof(f56,plain,(
% 1.53/0.58    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.53/0.58    inference(definition_unfolding,[],[f34,f55])).
% 1.53/0.58  fof(f55,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.53/0.58    inference(definition_unfolding,[],[f48,f54])).
% 1.53/0.58  fof(f54,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.53/0.58    inference(definition_unfolding,[],[f52,f53])).
% 1.53/0.58  fof(f53,plain,(
% 1.53/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f5])).
% 1.53/0.58  fof(f5,axiom,(
% 1.53/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.53/0.58  fof(f52,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f4])).
% 1.53/0.58  fof(f4,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.53/0.58  fof(f48,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f3])).
% 1.53/0.58  fof(f3,axiom,(
% 1.53/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.53/0.58  fof(f34,plain,(
% 1.53/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f2])).
% 1.53/0.58  fof(f2,axiom,(
% 1.53/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.53/0.58  fof(f30,plain,(
% 1.53/0.58    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)),
% 1.53/0.58    inference(cnf_transformation,[],[f20])).
% 1.53/0.58  fof(f20,plain,(
% 1.53/0.58    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0))),
% 1.53/0.58    inference(ennf_transformation,[],[f18])).
% 1.53/0.58  fof(f18,negated_conjecture,(
% 1.53/0.58    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 1.53/0.58    inference(negated_conjecture,[],[f17])).
% 1.53/0.58  fof(f17,conjecture,(
% 1.53/0.58    ! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).
% 1.53/0.58  fof(f96,plain,(
% 1.53/0.58    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 1.53/0.58    inference(forward_demodulation,[],[f95,f71])).
% 1.53/0.58  fof(f71,plain,(
% 1.53/0.58    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 1.53/0.58    inference(superposition,[],[f70,f67])).
% 1.53/0.58  fof(f67,plain,(
% 1.53/0.58    ( ! [X0] : (k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)) )),
% 1.53/0.58    inference(resolution,[],[f38,f32])).
% 1.53/0.58  fof(f32,plain,(
% 1.53/0.58    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f13])).
% 1.53/0.58  fof(f13,axiom,(
% 1.53/0.58    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).
% 1.53/0.58  fof(f38,plain,(
% 1.53/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.53/0.58    inference(cnf_transformation,[],[f21])).
% 1.53/0.58  fof(f21,plain,(
% 1.53/0.58    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.53/0.58    inference(ennf_transformation,[],[f1])).
% 1.53/0.58  fof(f1,axiom,(
% 1.53/0.58    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.53/0.58  fof(f70,plain,(
% 1.53/0.58    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))) )),
% 1.53/0.58    inference(resolution,[],[f62,f29])).
% 1.53/0.58  fof(f29,plain,(
% 1.53/0.58    l1_orders_2(sK0)),
% 1.53/0.58    inference(cnf_transformation,[],[f20])).
% 1.53/0.58  fof(f62,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~l1_orders_2(X1) | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))) )),
% 1.53/0.58    inference(definition_unfolding,[],[f49,f47])).
% 1.53/0.58  fof(f47,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f15])).
% 1.53/0.58  fof(f15,axiom,(
% 1.53/0.58    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).
% 1.53/0.58  fof(f49,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~l1_orders_2(X1) | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f26])).
% 1.53/0.58  fof(f26,plain,(
% 1.53/0.58    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 1.53/0.58    inference(ennf_transformation,[],[f12])).
% 1.53/0.58  fof(f12,axiom,(
% 1.53/0.58    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).
% 1.53/0.58  fof(f95,plain,(
% 1.53/0.58    g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 1.53/0.58    inference(subsumption_resolution,[],[f94,f65])).
% 1.53/0.58  fof(f65,plain,(
% 1.53/0.58    v1_relat_1(k1_xboole_0)),
% 1.53/0.58    inference(superposition,[],[f60,f58])).
% 1.53/0.58  fof(f58,plain,(
% 1.53/0.58    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.53/0.58    inference(definition_unfolding,[],[f31,f33])).
% 1.53/0.58  fof(f33,plain,(
% 1.53/0.58    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f11])).
% 1.53/0.58  fof(f11,axiom,(
% 1.53/0.58    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.53/0.58  fof(f31,plain,(
% 1.53/0.58    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.53/0.58    inference(cnf_transformation,[],[f7])).
% 1.53/0.58  fof(f7,axiom,(
% 1.53/0.58    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.53/0.58  fof(f60,plain,(
% 1.53/0.58    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 1.53/0.58    inference(definition_unfolding,[],[f35,f33])).
% 1.53/0.58  fof(f35,plain,(
% 1.53/0.58    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f8])).
% 1.53/0.58  fof(f8,axiom,(
% 1.53/0.58    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.53/0.58  fof(f94,plain,(
% 1.53/0.58    ~v1_relat_1(k1_xboole_0) | g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 1.53/0.58    inference(subsumption_resolution,[],[f93,f64])).
% 1.53/0.58  fof(f64,plain,(
% 1.53/0.58    v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 1.53/0.58    inference(superposition,[],[f37,f58])).
% 1.53/0.58  fof(f37,plain,(
% 1.53/0.58    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f19])).
% 1.53/0.58  fof(f19,plain,(
% 1.53/0.58    ! [X0] : v1_partfun1(k6_partfun1(X0),X0)),
% 1.53/0.58    inference(pure_predicate_removal,[],[f10])).
% 1.53/0.58  fof(f10,axiom,(
% 1.53/0.58    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.53/0.58  fof(f93,plain,(
% 1.53/0.58    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 1.53/0.58    inference(subsumption_resolution,[],[f92,f66])).
% 1.53/0.58  fof(f66,plain,(
% 1.53/0.58    v1_funct_1(k1_xboole_0)),
% 1.53/0.58    inference(superposition,[],[f59,f58])).
% 1.53/0.58  fof(f59,plain,(
% 1.53/0.58    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 1.53/0.58    inference(definition_unfolding,[],[f36,f33])).
% 1.53/0.58  fof(f36,plain,(
% 1.53/0.58    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f8])).
% 1.53/0.58  fof(f92,plain,(
% 1.53/0.58    ~v1_funct_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 1.53/0.58    inference(subsumption_resolution,[],[f89,f81])).
% 1.53/0.58  fof(f81,plain,(
% 1.53/0.58    v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.53/0.58    inference(superposition,[],[f43,f78])).
% 1.53/0.58  fof(f78,plain,(
% 1.53/0.58    k1_xboole_0 = sK1(k1_xboole_0)),
% 1.53/0.58    inference(equality_resolution,[],[f77])).
% 1.53/0.58  fof(f77,plain,(
% 1.53/0.58    ( ! [X1] : (k1_xboole_0 != X1 | k1_xboole_0 = sK1(X1)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f76,f42])).
% 1.53/0.58  fof(f42,plain,(
% 1.53/0.58    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f14])).
% 1.53/0.58  fof(f14,axiom,(
% 1.53/0.58    ! [X0] : ? [X1] : (v1_yellow_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_yellow_1)).
% 1.53/0.58  fof(f76,plain,(
% 1.53/0.58    ( ! [X1] : (k1_xboole_0 != X1 | ~v1_relat_1(sK1(X1)) | k1_xboole_0 = sK1(X1)) )),
% 1.53/0.58    inference(superposition,[],[f39,f74])).
% 1.53/0.58  fof(f74,plain,(
% 1.53/0.58    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f73,f45])).
% 1.53/0.58  fof(f45,plain,(
% 1.53/0.58    ( ! [X0] : (v1_partfun1(sK1(X0),X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f14])).
% 1.53/0.58  fof(f73,plain,(
% 1.53/0.58    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0 | ~v1_partfun1(sK1(X0),X0)) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f72,f42])).
% 1.53/0.58  fof(f72,plain,(
% 1.53/0.58    ( ! [X0] : (~v1_relat_1(sK1(X0)) | k1_relat_1(sK1(X0)) = X0 | ~v1_partfun1(sK1(X0),X0)) )),
% 1.53/0.58    inference(resolution,[],[f51,f43])).
% 1.53/0.58  fof(f51,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f28])).
% 1.53/0.58  fof(f28,plain,(
% 1.53/0.58    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.53/0.58    inference(flattening,[],[f27])).
% 1.53/0.58  fof(f27,plain,(
% 1.53/0.58    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.53/0.58    inference(ennf_transformation,[],[f9])).
% 1.53/0.58  fof(f9,axiom,(
% 1.53/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 1.53/0.58  fof(f39,plain,(
% 1.53/0.58    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.53/0.58    inference(cnf_transformation,[],[f23])).
% 1.53/0.58  fof(f23,plain,(
% 1.53/0.58    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.53/0.58    inference(flattening,[],[f22])).
% 1.53/0.58  fof(f22,plain,(
% 1.53/0.58    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.53/0.58    inference(ennf_transformation,[],[f6])).
% 1.53/0.58  fof(f6,axiom,(
% 1.53/0.58    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.53/0.58  fof(f43,plain,(
% 1.53/0.58    ( ! [X0] : (v4_relat_1(sK1(X0),X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f14])).
% 1.53/0.58  fof(f89,plain,(
% 1.53/0.58    ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 1.53/0.58    inference(resolution,[],[f61,f82])).
% 1.53/0.58  fof(f82,plain,(
% 1.53/0.58    v1_yellow_1(k1_xboole_0)),
% 1.53/0.58    inference(superposition,[],[f46,f78])).
% 1.53/0.58  fof(f46,plain,(
% 1.53/0.58    ( ! [X0] : (v1_yellow_1(sK1(X0))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f14])).
% 1.53/0.58  fof(f61,plain,(
% 1.53/0.58    ( ! [X0] : (~v1_yellow_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_relat_1(X0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) )),
% 1.53/0.58    inference(definition_unfolding,[],[f41,f56,f56])).
% 1.53/0.58  fof(f41,plain,(
% 1.53/0.58    ( ! [X0] : (~v1_relat_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_yellow_1(X0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f25])).
% 1.53/0.58  fof(f25,plain,(
% 1.53/0.58    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.53/0.58    inference(flattening,[],[f24])).
% 1.53/0.58  fof(f24,plain,(
% 1.53/0.58    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 1.53/0.58    inference(ennf_transformation,[],[f16])).
% 1.53/0.58  fof(f16,axiom,(
% 1.53/0.58    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).
% 1.53/0.58  % SZS output end Proof for theBenchmark
% 1.53/0.58  % (5138)------------------------------
% 1.53/0.58  % (5138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (5138)Termination reason: Refutation
% 1.53/0.58  
% 1.53/0.58  % (5138)Memory used [KB]: 6268
% 1.53/0.58  % (5138)Time elapsed: 0.134 s
% 1.53/0.58  % (5138)------------------------------
% 1.53/0.58  % (5138)------------------------------
% 1.53/0.58  % (5131)Success in time 0.216 s
%------------------------------------------------------------------------------
