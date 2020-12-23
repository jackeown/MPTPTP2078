%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 196 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  174 ( 296 expanded)
%              Number of equality atoms :   55 ( 146 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f100,f102,f104,f106,f110,f112])).

fof(f112,plain,(
    ~ spl1_1 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | ~ spl1_1 ),
    inference(resolution,[],[f74,f32])).

fof(f32,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
        & l1_orders_2(X0) )
   => ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

fof(f74,plain,
    ( ! [X0] : ~ l1_orders_2(X0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl1_1
  <=> ! [X0] : ~ l1_orders_2(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f110,plain,(
    ~ spl1_6 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | ~ spl1_6 ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) != k6_yellow_1(k1_xboole_0,sK0)
    | ~ spl1_6 ),
    inference(superposition,[],[f59,f99])).

fof(f99,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl1_6
  <=> k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f59,plain,(
    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f33,f58,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f106,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl1_5 ),
    inference(resolution,[],[f95,f65])).

fof(f65,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f40,f60])).

fof(f60,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f36,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f34,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f40,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f95,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl1_5
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f104,plain,(
    spl1_4 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl1_4 ),
    inference(resolution,[],[f91,f67])).

fof(f67,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f61,f60])).

fof(f61,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f39,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f91,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl1_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl1_4
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f102,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl1_3 ),
    inference(resolution,[],[f87,f66])).

fof(f66,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f62,f60])).

fof(f62,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f38,f36])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f87,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl1_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f100,plain,
    ( ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_2
    | spl1_6 ),
    inference(avatar_split_clause,[],[f83,f97,f76,f93,f89,f85])).

fof(f76,plain,
    ( spl1_2
  <=> v1_yellow_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f83,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f82,f81])).

fof(f81,plain,(
    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f80,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f41,f35])).

fof(f35,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f80,plain,(
    ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0)) ),
    inference(resolution,[],[f64,f32])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) ) ),
    inference(definition_unfolding,[],[f47,f43])).

fof(f43,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f82,plain,
    ( ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f63,f45])).

fof(f45,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

fof(f63,plain,(
    ! [X0] :
      ( ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f42,f58,f58])).

fof(f42,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

fof(f79,plain,
    ( spl1_1
    | spl1_2 ),
    inference(avatar_split_clause,[],[f71,f76,f73])).

fof(f71,plain,(
    ! [X0] :
      ( v1_yellow_1(k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f46,f68])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => v1_yellow_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:48:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.41  % (5845)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.41  % (5845)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f113,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f79,f100,f102,f104,f106,f110,f112])).
% 0.20/0.41  fof(f112,plain,(
% 0.20/0.41    ~spl1_1),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f111])).
% 0.20/0.41  fof(f111,plain,(
% 0.20/0.41    $false | ~spl1_1),
% 0.20/0.41    inference(resolution,[],[f74,f32])).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    l1_orders_2(sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f30])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0)),
% 0.20/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f29])).
% 0.20/0.41  fof(f29,plain,(
% 0.20/0.41    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0)) => (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f20])).
% 0.20/0.41  fof(f20,negated_conjecture,(
% 0.20/0.41    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.20/0.41    inference(negated_conjecture,[],[f19])).
% 0.20/0.41  fof(f19,conjecture,(
% 0.20/0.41    ! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).
% 0.20/0.41  fof(f74,plain,(
% 0.20/0.41    ( ! [X0] : (~l1_orders_2(X0)) ) | ~spl1_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f73])).
% 0.20/0.41  fof(f73,plain,(
% 0.20/0.41    spl1_1 <=> ! [X0] : ~l1_orders_2(X0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.41  fof(f110,plain,(
% 0.20/0.41    ~spl1_6),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f109])).
% 0.20/0.41  fof(f109,plain,(
% 0.20/0.41    $false | ~spl1_6),
% 0.20/0.41    inference(trivial_inequality_removal,[],[f108])).
% 0.20/0.41  fof(f108,plain,(
% 0.20/0.41    k6_yellow_1(k1_xboole_0,sK0) != k6_yellow_1(k1_xboole_0,sK0) | ~spl1_6),
% 0.20/0.41    inference(superposition,[],[f59,f99])).
% 0.20/0.41  fof(f99,plain,(
% 0.20/0.41    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~spl1_6),
% 0.20/0.41    inference(avatar_component_clause,[],[f97])).
% 0.20/0.41  fof(f97,plain,(
% 0.20/0.41    spl1_6 <=> k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.41  fof(f59,plain,(
% 0.20/0.41    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 0.20/0.41    inference(definition_unfolding,[],[f33,f58,f58])).
% 0.20/0.41  fof(f58,plain,(
% 0.20/0.41    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f37,f57])).
% 0.20/0.41  fof(f57,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f44,f56])).
% 0.20/0.41  fof(f56,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f48,f55])).
% 0.20/0.41  fof(f55,plain,(
% 0.20/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f49,f54])).
% 0.20/0.41  fof(f54,plain,(
% 0.20/0.41    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f50,f53])).
% 0.20/0.41  fof(f53,plain,(
% 0.20/0.41    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f51,f52])).
% 0.20/0.41  fof(f52,plain,(
% 0.20/0.41    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.41  fof(f51,plain,(
% 0.20/0.41    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f7])).
% 0.20/0.41  fof(f7,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.41  fof(f50,plain,(
% 0.20/0.41    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.41  fof(f49,plain,(
% 0.20/0.41    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.41  fof(f48,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.41  fof(f44,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.41  fof(f37,plain,(
% 0.20/0.41    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f30])).
% 0.20/0.41  fof(f106,plain,(
% 0.20/0.41    spl1_5),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f105])).
% 0.20/0.41  fof(f105,plain,(
% 0.20/0.41    $false | spl1_5),
% 0.20/0.41    inference(resolution,[],[f95,f65])).
% 0.20/0.41  fof(f65,plain,(
% 0.20/0.41    v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.41    inference(superposition,[],[f40,f60])).
% 0.20/0.41  fof(f60,plain,(
% 0.20/0.41    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.20/0.41    inference(definition_unfolding,[],[f34,f36])).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f13])).
% 0.20/0.41  fof(f13,axiom,(
% 0.20/0.41    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,axiom,(
% 0.20/0.41    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f21])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ! [X0] : v1_partfun1(k6_partfun1(X0),X0)),
% 0.20/0.41    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.41  fof(f12,axiom,(
% 0.20/0.41    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.20/0.41  fof(f95,plain,(
% 0.20/0.41    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | spl1_5),
% 0.20/0.41    inference(avatar_component_clause,[],[f93])).
% 0.20/0.41  fof(f93,plain,(
% 0.20/0.41    spl1_5 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.41  fof(f104,plain,(
% 0.20/0.41    spl1_4),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f103])).
% 0.20/0.41  fof(f103,plain,(
% 0.20/0.41    $false | spl1_4),
% 0.20/0.41    inference(resolution,[],[f91,f67])).
% 0.20/0.41  fof(f67,plain,(
% 0.20/0.41    v1_funct_1(k1_xboole_0)),
% 0.20/0.41    inference(superposition,[],[f61,f60])).
% 0.20/0.41  fof(f61,plain,(
% 0.20/0.41    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 0.20/0.41    inference(definition_unfolding,[],[f39,f36])).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,axiom,(
% 0.20/0.41    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.41  fof(f91,plain,(
% 0.20/0.41    ~v1_funct_1(k1_xboole_0) | spl1_4),
% 0.20/0.41    inference(avatar_component_clause,[],[f89])).
% 0.20/0.41  fof(f89,plain,(
% 0.20/0.41    spl1_4 <=> v1_funct_1(k1_xboole_0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.41  fof(f102,plain,(
% 0.20/0.41    spl1_3),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f101])).
% 0.20/0.41  fof(f101,plain,(
% 0.20/0.41    $false | spl1_3),
% 0.20/0.41    inference(resolution,[],[f87,f66])).
% 0.20/0.41  fof(f66,plain,(
% 0.20/0.41    v1_relat_1(k1_xboole_0)),
% 0.20/0.41    inference(superposition,[],[f62,f60])).
% 0.20/0.41  fof(f62,plain,(
% 0.20/0.41    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.20/0.41    inference(definition_unfolding,[],[f38,f36])).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f87,plain,(
% 0.20/0.41    ~v1_relat_1(k1_xboole_0) | spl1_3),
% 0.20/0.41    inference(avatar_component_clause,[],[f85])).
% 0.20/0.41  fof(f85,plain,(
% 0.20/0.41    spl1_3 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.41  fof(f100,plain,(
% 0.20/0.41    ~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_2 | spl1_6),
% 0.20/0.41    inference(avatar_split_clause,[],[f83,f97,f76,f93,f89,f85])).
% 0.20/0.41  fof(f76,plain,(
% 0.20/0.41    spl1_2 <=> v1_yellow_1(k1_xboole_0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.41  fof(f83,plain,(
% 0.20/0.41    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.41    inference(forward_demodulation,[],[f82,f81])).
% 0.20/0.41  fof(f81,plain,(
% 0.20/0.41    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.41    inference(superposition,[],[f80,f68])).
% 0.20/0.41  fof(f68,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)) )),
% 0.20/0.41    inference(resolution,[],[f41,f35])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f16])).
% 0.20/0.41  fof(f16,axiom,(
% 0.20/0.41    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.41    inference(cnf_transformation,[],[f24])).
% 0.20/0.41  fof(f24,plain,(
% 0.20/0.41    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.41  fof(f80,plain,(
% 0.20/0.41    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))) )),
% 0.20/0.41    inference(resolution,[],[f64,f32])).
% 0.20/0.41  fof(f64,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~l1_orders_2(X1) | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))) )),
% 0.20/0.41    inference(definition_unfolding,[],[f47,f43])).
% 0.20/0.41  fof(f43,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,axiom,(
% 0.20/0.41    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f28])).
% 0.20/0.41  fof(f28,plain,(
% 0.20/0.41    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f14])).
% 0.20/0.41  fof(f14,axiom,(
% 0.20/0.41    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).
% 0.20/0.41  fof(f82,plain,(
% 0.20/0.41    ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.41    inference(resolution,[],[f63,f45])).
% 0.20/0.41  fof(f45,plain,(
% 0.20/0.41    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f31])).
% 0.20/0.41  fof(f31,plain,(
% 0.20/0.41    ! [X0] : v4_relat_1(k1_xboole_0,X0)),
% 0.20/0.41    inference(rectify,[],[f22])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0)),
% 0.20/0.41    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.41  fof(f9,axiom,(
% 0.20/0.41    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).
% 0.20/0.41  fof(f63,plain,(
% 0.20/0.41    ( ! [X0] : (~v4_relat_1(X0,k1_xboole_0) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_relat_1(X0)) )),
% 0.20/0.41    inference(definition_unfolding,[],[f42,f58,f58])).
% 0.20/0.41  fof(f42,plain,(
% 0.20/0.41    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f26])).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.41    inference(flattening,[],[f25])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f18])).
% 0.20/0.41  fof(f18,axiom,(
% 0.20/0.41    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).
% 0.20/0.41  fof(f79,plain,(
% 0.20/0.41    spl1_1 | spl1_2),
% 0.20/0.41    inference(avatar_split_clause,[],[f71,f76,f73])).
% 0.20/0.41  fof(f71,plain,(
% 0.20/0.41    ( ! [X0] : (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.20/0.41    inference(superposition,[],[f46,f68])).
% 0.20/0.41  fof(f46,plain,(
% 0.20/0.41    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f27])).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f15])).
% 0.20/0.41  fof(f15,axiom,(
% 0.20/0.41    ! [X0,X1] : (l1_orders_2(X1) => v1_yellow_1(k2_funcop_1(X0,X1)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (5845)------------------------------
% 0.20/0.41  % (5845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (5845)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (5845)Memory used [KB]: 6140
% 0.20/0.41  % (5845)Time elapsed: 0.029 s
% 0.20/0.41  % (5845)------------------------------
% 0.20/0.41  % (5845)------------------------------
% 0.20/0.41  % (5842)Success in time 0.061 s
%------------------------------------------------------------------------------
