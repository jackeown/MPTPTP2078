%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 138 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  234 ( 402 expanded)
%              Number of equality atoms :   32 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f63,f65,f67,f190,f227,f229,f234,f237,f297,f301,f304])).

fof(f304,plain,(
    spl2_20 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl2_20 ),
    inference(resolution,[],[f222,f34])).

fof(f34,plain,(
    ! [X0,X1] : v1_partfun1(k2_funcop_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_partfun1(k2_funcop_1(X0,X1),X0)
      & v1_funct_1(k2_funcop_1(X0,X1))
      & v4_relat_1(k2_funcop_1(X0,X1),X0)
      & v1_relat_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc20_funcop_1)).

fof(f222,plain,
    ( ~ v1_partfun1(k2_funcop_1(k1_xboole_0,sK0),k1_xboole_0)
    | spl2_20 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl2_20
  <=> v1_partfun1(k2_funcop_1(k1_xboole_0,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f301,plain,(
    spl2_18 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | spl2_18 ),
    inference(resolution,[],[f214,f32])).

fof(f32,plain,(
    ! [X0,X1] : v4_relat_1(k2_funcop_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f214,plain,
    ( ~ v4_relat_1(k2_funcop_1(k1_xboole_0,sK0),k1_xboole_0)
    | spl2_18 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl2_18
  <=> v4_relat_1(k2_funcop_1(k1_xboole_0,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f297,plain,
    ( ~ spl2_17
    | ~ spl2_19
    | ~ spl2_9
    | spl2_21 ),
    inference(avatar_split_clause,[],[f296,f224,f151,f216,f208])).

fof(f208,plain,
    ( spl2_17
  <=> v1_relat_1(k2_funcop_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f216,plain,
    ( spl2_19
  <=> v1_funct_1(k2_funcop_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f151,plain,
    ( spl2_9
  <=> v1_yellow_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f224,plain,
    ( spl2_21
  <=> v1_yellow_1(k2_funcop_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f296,plain,
    ( ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_funct_1(k2_funcop_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(k2_funcop_1(k1_xboole_0,sK0))
    | spl2_21 ),
    inference(superposition,[],[f226,f76])).

fof(f76,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)
      | ~ v1_funct_1(k2_funcop_1(k1_xboole_0,X0))
      | ~ v1_relat_1(k2_funcop_1(k1_xboole_0,X0)) ) ),
    inference(resolution,[],[f40,f32])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v4_relat_1(k2_funcop_1(k1_xboole_0,X0),k1_xboole_0)
      | ~ v1_funct_1(k2_funcop_1(k1_xboole_0,X0))
      | k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k2_funcop_1(k1_xboole_0,X0)) ) ),
    inference(resolution,[],[f24,f34])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_partfun1(X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_pboole)).

fof(f226,plain,
    ( ~ v1_yellow_1(k2_funcop_1(k1_xboole_0,sK0))
    | spl2_21 ),
    inference(avatar_component_clause,[],[f224])).

fof(f237,plain,(
    spl2_19 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl2_19 ),
    inference(resolution,[],[f218,f33])).

fof(f33,plain,(
    ! [X0,X1] : v1_funct_1(k2_funcop_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f218,plain,
    ( ~ v1_funct_1(k2_funcop_1(k1_xboole_0,sK0))
    | spl2_19 ),
    inference(avatar_component_clause,[],[f216])).

fof(f234,plain,(
    spl2_17 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | spl2_17 ),
    inference(resolution,[],[f210,f31])).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_funcop_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f210,plain,
    ( ~ v1_relat_1(k2_funcop_1(k1_xboole_0,sK0))
    | spl2_17 ),
    inference(avatar_component_clause,[],[f208])).

fof(f229,plain,(
    spl2_16 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl2_16 ),
    inference(resolution,[],[f206,f20])).

fof(f20,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
        & l1_orders_2(X0) )
   => ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

fof(f206,plain,
    ( ~ l1_orders_2(sK0)
    | spl2_16 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl2_16
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f227,plain,
    ( ~ spl2_16
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_19
    | ~ spl2_20
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f195,f224,f220,f216,f212,f208,f204])).

fof(f195,plain,
    ( ~ v1_yellow_1(k2_funcop_1(k1_xboole_0,sK0))
    | ~ v1_partfun1(k2_funcop_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ v1_funct_1(k2_funcop_1(k1_xboole_0,sK0))
    | ~ v4_relat_1(k2_funcop_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ v1_relat_1(k2_funcop_1(k1_xboole_0,sK0))
    | ~ l1_orders_2(sK0) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X1] :
      ( k6_yellow_1(k1_xboole_0,sK0) != k6_yellow_1(k1_xboole_0,X1)
      | ~ v1_yellow_1(k2_funcop_1(k1_xboole_0,X1))
      | ~ v1_partfun1(k2_funcop_1(k1_xboole_0,X1),k1_xboole_0)
      | ~ v1_funct_1(k2_funcop_1(k1_xboole_0,X1))
      | ~ v4_relat_1(k2_funcop_1(k1_xboole_0,X1),k1_xboole_0)
      | ~ v1_relat_1(k2_funcop_1(k1_xboole_0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(superposition,[],[f61,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(definition_unfolding,[],[f35,f30])).

fof(f30,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f61,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) != k6_yellow_1(k1_xboole_0,sK0)
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f23,f22,f22])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

fof(f36,plain,(
    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f21,f22,f22])).

fof(f21,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f190,plain,
    ( ~ spl2_4
    | spl2_9 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | ~ spl2_4
    | spl2_9 ),
    inference(resolution,[],[f153,f70])).

fof(f70,plain,
    ( v1_yellow_1(k1_xboole_0)
    | ~ spl2_4 ),
    inference(superposition,[],[f29,f56])).

fof(f56,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_4
  <=> k1_xboole_0 = sK1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f29,plain,(
    ! [X0] : v1_yellow_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_yellow_1(sK1(X0))
      & v1_partfun1(sK1(X0),X0)
      & v1_funct_1(sK1(X0))
      & v4_relat_1(sK1(X0),X0)
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f4,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_yellow_1(X1)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
     => ( v1_yellow_1(sK1(X0))
        & v1_partfun1(sK1(X0),X0)
        & v1_funct_1(sK1(X0))
        & v4_relat_1(sK1(X0),X0)
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_yellow_1(X1)
      & v1_partfun1(X1,X0)
      & v1_funct_1(X1)
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_1)).

fof(f153,plain,
    ( ~ v1_yellow_1(k1_xboole_0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f151])).

fof(f67,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl2_2 ),
    inference(resolution,[],[f48,f26])).

fof(f26,plain,(
    ! [X0] : v4_relat_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,
    ( ~ v4_relat_1(sK1(k1_xboole_0),k1_xboole_0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_2
  <=> v4_relat_1(sK1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f65,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f52,f27])).

fof(f27,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,
    ( ~ v1_funct_1(sK1(k1_xboole_0))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_3
  <=> v1_funct_1(sK1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f63,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f44,f25])).

fof(f25,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,
    ( ~ v1_relat_1(sK1(k1_xboole_0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_1
  <=> v1_relat_1(sK1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f57,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f39,f54,f50,f46,f42])).

fof(f39,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ v1_funct_1(sK1(k1_xboole_0))
    | ~ v4_relat_1(sK1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(sK1(k1_xboole_0)) ),
    inference(resolution,[],[f24,f28])).

fof(f28,plain,(
    ! [X0] : v1_partfun1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (12966)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (12965)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (12965)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f305,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f57,f63,f65,f67,f190,f227,f229,f234,f237,f297,f301,f304])).
% 0.20/0.46  fof(f304,plain,(
% 0.20/0.46    spl2_20),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f302])).
% 0.20/0.46  fof(f302,plain,(
% 0.20/0.46    $false | spl2_20),
% 0.20/0.46    inference(resolution,[],[f222,f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_partfun1(k2_funcop_1(X0,X1),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_partfun1(k2_funcop_1(X0,X1),X0) & v1_funct_1(k2_funcop_1(X0,X1)) & v4_relat_1(k2_funcop_1(X0,X1),X0) & v1_relat_1(k2_funcop_1(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc20_funcop_1)).
% 0.20/0.46  fof(f222,plain,(
% 0.20/0.46    ~v1_partfun1(k2_funcop_1(k1_xboole_0,sK0),k1_xboole_0) | spl2_20),
% 0.20/0.46    inference(avatar_component_clause,[],[f220])).
% 0.20/0.46  fof(f220,plain,(
% 0.20/0.46    spl2_20 <=> v1_partfun1(k2_funcop_1(k1_xboole_0,sK0),k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.20/0.46  fof(f301,plain,(
% 0.20/0.46    spl2_18),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f299])).
% 0.20/0.46  fof(f299,plain,(
% 0.20/0.46    $false | spl2_18),
% 0.20/0.46    inference(resolution,[],[f214,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v4_relat_1(k2_funcop_1(X0,X1),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f214,plain,(
% 0.20/0.46    ~v4_relat_1(k2_funcop_1(k1_xboole_0,sK0),k1_xboole_0) | spl2_18),
% 0.20/0.46    inference(avatar_component_clause,[],[f212])).
% 0.20/0.46  fof(f212,plain,(
% 0.20/0.46    spl2_18 <=> v4_relat_1(k2_funcop_1(k1_xboole_0,sK0),k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.46  fof(f297,plain,(
% 0.20/0.46    ~spl2_17 | ~spl2_19 | ~spl2_9 | spl2_21),
% 0.20/0.46    inference(avatar_split_clause,[],[f296,f224,f151,f216,f208])).
% 0.20/0.46  fof(f208,plain,(
% 0.20/0.46    spl2_17 <=> v1_relat_1(k2_funcop_1(k1_xboole_0,sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.46  fof(f216,plain,(
% 0.20/0.46    spl2_19 <=> v1_funct_1(k2_funcop_1(k1_xboole_0,sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.46  fof(f151,plain,(
% 0.20/0.46    spl2_9 <=> v1_yellow_1(k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.46  fof(f224,plain,(
% 0.20/0.46    spl2_21 <=> v1_yellow_1(k2_funcop_1(k1_xboole_0,sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.20/0.46  fof(f296,plain,(
% 0.20/0.46    ~v1_yellow_1(k1_xboole_0) | ~v1_funct_1(k2_funcop_1(k1_xboole_0,sK0)) | ~v1_relat_1(k2_funcop_1(k1_xboole_0,sK0)) | spl2_21),
% 0.20/0.46    inference(superposition,[],[f226,f76])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) | ~v1_funct_1(k2_funcop_1(k1_xboole_0,X0)) | ~v1_relat_1(k2_funcop_1(k1_xboole_0,X0))) )),
% 0.20/0.46    inference(resolution,[],[f40,f32])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ( ! [X0] : (~v4_relat_1(k2_funcop_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_funct_1(k2_funcop_1(k1_xboole_0,X0)) | k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) | ~v1_relat_1(k2_funcop_1(k1_xboole_0,X0))) )),
% 0.20/0.46    inference(resolution,[],[f24,f34])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_partfun1(X0,k1_xboole_0) | k1_xboole_0 = X0 | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(flattening,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0] : (k1_xboole_0 = X0 | (~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0] : ((v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k1_xboole_0 = X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_pboole)).
% 0.20/0.46  fof(f226,plain,(
% 0.20/0.46    ~v1_yellow_1(k2_funcop_1(k1_xboole_0,sK0)) | spl2_21),
% 0.20/0.46    inference(avatar_component_clause,[],[f224])).
% 0.20/0.46  fof(f237,plain,(
% 0.20/0.46    spl2_19),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f235])).
% 0.20/0.46  fof(f235,plain,(
% 0.20/0.46    $false | spl2_19),
% 0.20/0.46    inference(resolution,[],[f218,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_funct_1(k2_funcop_1(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f218,plain,(
% 0.20/0.46    ~v1_funct_1(k2_funcop_1(k1_xboole_0,sK0)) | spl2_19),
% 0.20/0.46    inference(avatar_component_clause,[],[f216])).
% 0.20/0.46  fof(f234,plain,(
% 0.20/0.46    spl2_17),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f232])).
% 0.20/0.46  fof(f232,plain,(
% 0.20/0.46    $false | spl2_17),
% 0.20/0.46    inference(resolution,[],[f210,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_relat_1(k2_funcop_1(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f210,plain,(
% 0.20/0.46    ~v1_relat_1(k2_funcop_1(k1_xboole_0,sK0)) | spl2_17),
% 0.20/0.46    inference(avatar_component_clause,[],[f208])).
% 0.20/0.46  fof(f229,plain,(
% 0.20/0.46    spl2_16),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f228])).
% 0.20/0.46  fof(f228,plain,(
% 0.20/0.46    $false | spl2_16),
% 0.20/0.46    inference(resolution,[],[f206,f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    l1_orders_2(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0)) => (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,negated_conjecture,(
% 0.20/0.46    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.20/0.46    inference(negated_conjecture,[],[f8])).
% 0.20/0.46  fof(f8,conjecture,(
% 0.20/0.46    ! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).
% 0.20/0.46  fof(f206,plain,(
% 0.20/0.46    ~l1_orders_2(sK0) | spl2_16),
% 0.20/0.46    inference(avatar_component_clause,[],[f204])).
% 0.20/0.46  fof(f204,plain,(
% 0.20/0.46    spl2_16 <=> l1_orders_2(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.46  fof(f227,plain,(
% 0.20/0.46    ~spl2_16 | ~spl2_17 | ~spl2_18 | ~spl2_19 | ~spl2_20 | ~spl2_21),
% 0.20/0.46    inference(avatar_split_clause,[],[f195,f224,f220,f216,f212,f208,f204])).
% 0.20/0.46  fof(f195,plain,(
% 0.20/0.46    ~v1_yellow_1(k2_funcop_1(k1_xboole_0,sK0)) | ~v1_partfun1(k2_funcop_1(k1_xboole_0,sK0),k1_xboole_0) | ~v1_funct_1(k2_funcop_1(k1_xboole_0,sK0)) | ~v4_relat_1(k2_funcop_1(k1_xboole_0,sK0),k1_xboole_0) | ~v1_relat_1(k2_funcop_1(k1_xboole_0,sK0)) | ~l1_orders_2(sK0)),
% 0.20/0.46    inference(equality_resolution,[],[f74])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    ( ! [X1] : (k6_yellow_1(k1_xboole_0,sK0) != k6_yellow_1(k1_xboole_0,X1) | ~v1_yellow_1(k2_funcop_1(k1_xboole_0,X1)) | ~v1_partfun1(k2_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_funct_1(k2_funcop_1(k1_xboole_0,X1)) | ~v4_relat_1(k2_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_relat_1(k2_funcop_1(k1_xboole_0,X1)) | ~l1_orders_2(X1)) )),
% 0.20/0.46    inference(superposition,[],[f61,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f35,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) != k6_yellow_1(k1_xboole_0,sK0) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(superposition,[],[f36,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f23,f22,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(flattening,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.46    inference(definition_unfolding,[],[f21,f22,f22])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f190,plain,(
% 0.20/0.46    ~spl2_4 | spl2_9),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f189])).
% 0.20/0.46  fof(f189,plain,(
% 0.20/0.46    $false | (~spl2_4 | spl2_9)),
% 0.20/0.46    inference(resolution,[],[f153,f70])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    v1_yellow_1(k1_xboole_0) | ~spl2_4),
% 0.20/0.46    inference(superposition,[],[f29,f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    k1_xboole_0 = sK1(k1_xboole_0) | ~spl2_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f54])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    spl2_4 <=> k1_xboole_0 = sK1(k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0] : (v1_yellow_1(sK1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0] : (v1_yellow_1(sK1(X0)) & v1_partfun1(sK1(X0),X0) & v1_funct_1(sK1(X0)) & v4_relat_1(sK1(X0),X0) & v1_relat_1(sK1(X0)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f4,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : (v1_yellow_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_yellow_1(sK1(X0)) & v1_partfun1(sK1(X0),X0) & v1_funct_1(sK1(X0)) & v4_relat_1(sK1(X0),X0) & v1_relat_1(sK1(X0))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : ? [X1] : (v1_yellow_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_1)).
% 0.20/0.46  fof(f153,plain,(
% 0.20/0.46    ~v1_yellow_1(k1_xboole_0) | spl2_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f151])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    spl2_2),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f66])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    $false | spl2_2),
% 0.20/0.46    inference(resolution,[],[f48,f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X0] : (v4_relat_1(sK1(X0),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ~v4_relat_1(sK1(k1_xboole_0),k1_xboole_0) | spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    spl2_2 <=> v4_relat_1(sK1(k1_xboole_0),k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    spl2_3),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f64])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    $false | spl2_3),
% 0.20/0.46    inference(resolution,[],[f52,f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ~v1_funct_1(sK1(k1_xboole_0)) | spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    spl2_3 <=> v1_funct_1(sK1(k1_xboole_0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    spl2_1),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f62])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    $false | spl2_1),
% 0.20/0.46    inference(resolution,[],[f44,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ~v1_relat_1(sK1(k1_xboole_0)) | spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    spl2_1 <=> v1_relat_1(sK1(k1_xboole_0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f39,f54,f50,f46,f42])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    k1_xboole_0 = sK1(k1_xboole_0) | ~v1_funct_1(sK1(k1_xboole_0)) | ~v4_relat_1(sK1(k1_xboole_0),k1_xboole_0) | ~v1_relat_1(sK1(k1_xboole_0))),
% 0.20/0.46    inference(resolution,[],[f24,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X0] : (v1_partfun1(sK1(X0),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (12965)------------------------------
% 0.20/0.46  % (12965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (12965)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (12965)Memory used [KB]: 6268
% 0.20/0.46  % (12965)Time elapsed: 0.049 s
% 0.20/0.46  % (12965)------------------------------
% 0.20/0.46  % (12965)------------------------------
% 0.20/0.46  % (12957)Success in time 0.106 s
%------------------------------------------------------------------------------
