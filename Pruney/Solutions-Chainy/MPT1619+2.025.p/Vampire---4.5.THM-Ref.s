%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 242 expanded)
%              Number of leaves         :   39 ( 106 expanded)
%              Depth                    :   10
%              Number of atoms          :  350 ( 532 expanded)
%              Number of equality atoms :   66 ( 140 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f180,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f68,f72,f76,f81,f85,f89,f96,f101,f107,f112,f117,f121,f127,f135,f144,f148,f153,f159,f164,f168,f177,f179])).

fof(f179,plain,
    ( ~ spl1_1
    | ~ spl1_17 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_17 ),
    inference(subsumption_resolution,[],[f58,f139])).

fof(f139,plain,
    ( ! [X0] : ~ l1_orders_2(X0)
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl1_17
  <=> ! [X0] : ~ l1_orders_2(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f58,plain,
    ( l1_orders_2(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl1_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f177,plain,
    ( ~ spl1_9
    | ~ spl1_10
    | ~ spl1_11
    | ~ spl1_13
    | ~ spl1_18
    | ~ spl1_21
    | spl1_22
    | ~ spl1_23 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_11
    | ~ spl1_13
    | ~ spl1_18
    | ~ spl1_21
    | spl1_22
    | ~ spl1_23 ),
    inference(subsumption_resolution,[],[f175,f163])).

fof(f163,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | spl1_22 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl1_22
  <=> k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f175,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_11
    | ~ spl1_13
    | ~ spl1_18
    | ~ spl1_21
    | ~ spl1_23 ),
    inference(forward_demodulation,[],[f174,f158])).

fof(f158,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_21 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl1_21
  <=> k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).

fof(f174,plain,
    ( g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_11
    | ~ spl1_13
    | ~ spl1_18
    | ~ spl1_23 ),
    inference(subsumption_resolution,[],[f173,f95])).

fof(f95,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl1_9
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f173,plain,
    ( g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_10
    | ~ spl1_11
    | ~ spl1_13
    | ~ spl1_18
    | ~ spl1_23 ),
    inference(subsumption_resolution,[],[f172,f116])).

fof(f116,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl1_13
  <=> v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f172,plain,
    ( g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_10
    | ~ spl1_11
    | ~ spl1_18
    | ~ spl1_23 ),
    inference(subsumption_resolution,[],[f171,f100])).

fof(f100,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl1_10
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f171,plain,
    ( g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_11
    | ~ spl1_18
    | ~ spl1_23 ),
    inference(subsumption_resolution,[],[f170,f106])).

fof(f106,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl1_11
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f170,plain,
    ( g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_18
    | ~ spl1_23 ),
    inference(resolution,[],[f167,f143])).

fof(f143,plain,
    ( v1_yellow_1(k1_xboole_0)
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl1_18
  <=> v1_yellow_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ v1_yellow_1(X0)
        | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_23 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl1_23
  <=> ! [X0] :
        ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).

fof(f168,plain,(
    spl1_23 ),
    inference(avatar_split_clause,[],[f53,f166])).

fof(f53,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f36,f46,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

fof(f164,plain,(
    ~ spl1_22 ),
    inference(avatar_split_clause,[],[f47,f161])).

fof(f47,plain,(
    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f26,f46,f46])).

fof(f26,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
        & l1_orders_2(X0) )
   => ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

fof(f159,plain,
    ( spl1_21
    | ~ spl1_16
    | ~ spl1_20 ),
    inference(avatar_split_clause,[],[f154,f151,f133,f156])).

fof(f133,plain,
    ( spl1_16
  <=> ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f151,plain,
    ( spl1_20
  <=> ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f154,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_16
    | ~ spl1_20 ),
    inference(superposition,[],[f152,f134])).

fof(f134,plain,
    ( ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f133])).

fof(f152,plain,
    ( ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))
    | ~ spl1_20 ),
    inference(avatar_component_clause,[],[f151])).

fof(f153,plain,
    ( spl1_20
    | ~ spl1_1
    | ~ spl1_19 ),
    inference(avatar_split_clause,[],[f149,f146,f56,f151])).

fof(f146,plain,
    ( spl1_19
  <=> ! [X1,X0] :
        ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f149,plain,
    ( ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))
    | ~ spl1_1
    | ~ spl1_19 ),
    inference(resolution,[],[f147,f58])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(X1)
        | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) )
    | ~ spl1_19 ),
    inference(avatar_component_clause,[],[f146])).

fof(f148,plain,(
    spl1_19 ),
    inference(avatar_split_clause,[],[f54,f146])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f37,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f144,plain,
    ( spl1_17
    | spl1_18
    | ~ spl1_12
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f136,f133,f110,f141,f138])).

fof(f110,plain,
    ( spl1_12
  <=> ! [X1,X0] :
        ( v1_yellow_1(k2_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f136,plain,
    ( ! [X0] :
        ( v1_yellow_1(k1_xboole_0)
        | ~ l1_orders_2(X0) )
    | ~ spl1_12
    | ~ spl1_16 ),
    inference(superposition,[],[f111,f134])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( v1_yellow_1(k2_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f135,plain,
    ( spl1_16
    | ~ spl1_5
    | ~ spl1_15 ),
    inference(avatar_split_clause,[],[f129,f125,f74,f133])).

fof(f74,plain,
    ( spl1_5
  <=> ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f125,plain,
    ( spl1_15
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f129,plain,
    ( ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)
    | ~ spl1_5
    | ~ spl1_15 ),
    inference(resolution,[],[f126,f75])).

fof(f75,plain,
    ( ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f125])).

fof(f127,plain,
    ( spl1_15
    | ~ spl1_2
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f122,f119,f61,f125])).

fof(f61,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f119,plain,
    ( spl1_14
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | X0 = X1
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f122,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl1_2
    | ~ spl1_14 ),
    inference(resolution,[],[f120,f63])).

fof(f63,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | X0 = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,(
    spl1_14 ),
    inference(avatar_split_clause,[],[f41,f119])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f117,plain,
    ( spl1_13
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f108,f87,f78,f114])).

fof(f78,plain,
    ( spl1_6
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f87,plain,
    ( spl1_8
  <=> ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f108,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(superposition,[],[f88,f80])).

fof(f80,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f88,plain,
    ( ! [X0] : v4_relat_1(k6_partfun1(X0),X0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f112,plain,(
    spl1_12 ),
    inference(avatar_split_clause,[],[f39,f110])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => v1_yellow_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).

fof(f107,plain,
    ( spl1_11
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f102,f83,f78,f104])).

fof(f83,plain,
    ( spl1_7
  <=> ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f102,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(superposition,[],[f84,f80])).

fof(f84,plain,
    ( ! [X0] : v1_partfun1(k6_partfun1(X0),X0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f101,plain,
    ( spl1_10
    | ~ spl1_3
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f91,f78,f66,f98])).

fof(f66,plain,
    ( spl1_3
  <=> ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f91,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_6 ),
    inference(superposition,[],[f67,f80])).

fof(f67,plain,
    ( ! [X0] : v1_funct_1(k6_partfun1(X0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f96,plain,
    ( spl1_9
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f90,f78,f70,f93])).

fof(f70,plain,
    ( spl1_4
  <=> ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f90,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(superposition,[],[f71,f80])).

fof(f71,plain,
    ( ! [X0] : v1_relat_1(k6_partfun1(X0))
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f89,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f51,f87])).

fof(f51,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(definition_unfolding,[],[f33,f30])).

fof(f30,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f33,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_partfun1(k6_relat_1(X0),X0)
      & v1_funct_1(k6_relat_1(X0))
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_funct_2)).

fof(f85,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f49,f83])).

fof(f49,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(definition_unfolding,[],[f35,f30])).

fof(f35,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f81,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f48,f78])).

fof(f48,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f28,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f76,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f29,f74])).

fof(f29,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(f72,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f52,f70])).

fof(f52,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f68,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f50,f66])).

fof(f50,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f34,f30])).

fof(f34,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f64,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f59,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:00:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (25532)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.44  % (25532)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f180,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f59,f64,f68,f72,f76,f81,f85,f89,f96,f101,f107,f112,f117,f121,f127,f135,f144,f148,f153,f159,f164,f168,f177,f179])).
% 0.21/0.44  fof(f179,plain,(
% 0.21/0.44    ~spl1_1 | ~spl1_17),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f178])).
% 0.21/0.44  fof(f178,plain,(
% 0.21/0.44    $false | (~spl1_1 | ~spl1_17)),
% 0.21/0.44    inference(subsumption_resolution,[],[f58,f139])).
% 0.21/0.44  fof(f139,plain,(
% 0.21/0.44    ( ! [X0] : (~l1_orders_2(X0)) ) | ~spl1_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f138])).
% 0.21/0.44  fof(f138,plain,(
% 0.21/0.44    spl1_17 <=> ! [X0] : ~l1_orders_2(X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    l1_orders_2(sK0) | ~spl1_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    spl1_1 <=> l1_orders_2(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.44  fof(f177,plain,(
% 0.21/0.44    ~spl1_9 | ~spl1_10 | ~spl1_11 | ~spl1_13 | ~spl1_18 | ~spl1_21 | spl1_22 | ~spl1_23),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f176])).
% 0.21/0.44  fof(f176,plain,(
% 0.21/0.44    $false | (~spl1_9 | ~spl1_10 | ~spl1_11 | ~spl1_13 | ~spl1_18 | ~spl1_21 | spl1_22 | ~spl1_23)),
% 0.21/0.44    inference(subsumption_resolution,[],[f175,f163])).
% 0.21/0.44  fof(f163,plain,(
% 0.21/0.44    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | spl1_22),
% 0.21/0.44    inference(avatar_component_clause,[],[f161])).
% 0.21/0.44  fof(f161,plain,(
% 0.21/0.44    spl1_22 <=> k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.21/0.44  fof(f175,plain,(
% 0.21/0.44    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (~spl1_9 | ~spl1_10 | ~spl1_11 | ~spl1_13 | ~spl1_18 | ~spl1_21 | ~spl1_23)),
% 0.21/0.44    inference(forward_demodulation,[],[f174,f158])).
% 0.21/0.44  fof(f158,plain,(
% 0.21/0.44    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~spl1_21),
% 0.21/0.44    inference(avatar_component_clause,[],[f156])).
% 0.21/0.44  fof(f156,plain,(
% 0.21/0.44    spl1_21 <=> k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).
% 0.21/0.44  fof(f174,plain,(
% 0.21/0.44    g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | (~spl1_9 | ~spl1_10 | ~spl1_11 | ~spl1_13 | ~spl1_18 | ~spl1_23)),
% 0.21/0.44    inference(subsumption_resolution,[],[f173,f95])).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    v1_relat_1(k1_xboole_0) | ~spl1_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f93])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    spl1_9 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.44  fof(f173,plain,(
% 0.21/0.44    g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl1_10 | ~spl1_11 | ~spl1_13 | ~spl1_18 | ~spl1_23)),
% 0.21/0.44    inference(subsumption_resolution,[],[f172,f116])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    v4_relat_1(k1_xboole_0,k1_xboole_0) | ~spl1_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f114])).
% 0.21/0.44  fof(f114,plain,(
% 0.21/0.44    spl1_13 <=> v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.21/0.44  fof(f172,plain,(
% 0.21/0.44    g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl1_10 | ~spl1_11 | ~spl1_18 | ~spl1_23)),
% 0.21/0.44    inference(subsumption_resolution,[],[f171,f100])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    v1_funct_1(k1_xboole_0) | ~spl1_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f98])).
% 0.21/0.44  fof(f98,plain,(
% 0.21/0.44    spl1_10 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.44  fof(f171,plain,(
% 0.21/0.44    g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl1_11 | ~spl1_18 | ~spl1_23)),
% 0.21/0.44    inference(subsumption_resolution,[],[f170,f106])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl1_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f104])).
% 0.21/0.44  fof(f104,plain,(
% 0.21/0.44    spl1_11 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.44  fof(f170,plain,(
% 0.21/0.44    g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl1_18 | ~spl1_23)),
% 0.21/0.44    inference(resolution,[],[f167,f143])).
% 0.21/0.44  fof(f143,plain,(
% 0.21/0.44    v1_yellow_1(k1_xboole_0) | ~spl1_18),
% 0.21/0.44    inference(avatar_component_clause,[],[f141])).
% 0.21/0.44  fof(f141,plain,(
% 0.21/0.44    spl1_18 <=> v1_yellow_1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.21/0.44  fof(f167,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_yellow_1(X0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl1_23),
% 0.21/0.44    inference(avatar_component_clause,[],[f166])).
% 0.21/0.44  fof(f166,plain,(
% 0.21/0.44    spl1_23 <=> ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).
% 0.21/0.44  fof(f168,plain,(
% 0.21/0.44    spl1_23),
% 0.21/0.44    inference(avatar_split_clause,[],[f53,f166])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f36,f46,f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f31,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f38,f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f42,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,axiom,(
% 0.21/0.44    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).
% 0.21/0.44  fof(f164,plain,(
% 0.21/0.44    ~spl1_22),
% 0.21/0.44    inference(avatar_split_clause,[],[f47,f161])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 0.21/0.44    inference(definition_unfolding,[],[f26,f46,f46])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0)) => (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.21/0.44    inference(negated_conjecture,[],[f15])).
% 0.21/0.44  fof(f15,conjecture,(
% 0.21/0.44    ! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).
% 0.21/0.44  fof(f159,plain,(
% 0.21/0.44    spl1_21 | ~spl1_16 | ~spl1_20),
% 0.21/0.44    inference(avatar_split_clause,[],[f154,f151,f133,f156])).
% 0.21/0.44  fof(f133,plain,(
% 0.21/0.44    spl1_16 <=> ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.21/0.44  fof(f151,plain,(
% 0.21/0.44    spl1_20 <=> ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.21/0.44  fof(f154,plain,(
% 0.21/0.44    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | (~spl1_16 | ~spl1_20)),
% 0.21/0.44    inference(superposition,[],[f152,f134])).
% 0.21/0.44  fof(f134,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)) ) | ~spl1_16),
% 0.21/0.44    inference(avatar_component_clause,[],[f133])).
% 0.21/0.44  fof(f152,plain,(
% 0.21/0.44    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))) ) | ~spl1_20),
% 0.21/0.44    inference(avatar_component_clause,[],[f151])).
% 0.21/0.44  fof(f153,plain,(
% 0.21/0.44    spl1_20 | ~spl1_1 | ~spl1_19),
% 0.21/0.44    inference(avatar_split_clause,[],[f149,f146,f56,f151])).
% 0.21/0.44  fof(f146,plain,(
% 0.21/0.44    spl1_19 <=> ! [X1,X0] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 0.21/0.44  fof(f149,plain,(
% 0.21/0.44    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))) ) | (~spl1_1 | ~spl1_19)),
% 0.21/0.44    inference(resolution,[],[f147,f58])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_orders_2(X1) | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))) ) | ~spl1_19),
% 0.21/0.44    inference(avatar_component_clause,[],[f146])).
% 0.21/0.44  fof(f148,plain,(
% 0.21/0.44    spl1_19),
% 0.21/0.44    inference(avatar_split_clause,[],[f54,f146])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f40,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,axiom,(
% 0.21/0.44    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,axiom,(
% 0.21/0.44    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    spl1_17 | spl1_18 | ~spl1_12 | ~spl1_16),
% 0.21/0.44    inference(avatar_split_clause,[],[f136,f133,f110,f141,f138])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    spl1_12 <=> ! [X1,X0] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.21/0.44  fof(f136,plain,(
% 0.21/0.44    ( ! [X0] : (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(X0)) ) | (~spl1_12 | ~spl1_16)),
% 0.21/0.44    inference(superposition,[],[f111,f134])).
% 0.21/0.44  fof(f111,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) ) | ~spl1_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f110])).
% 0.21/0.44  fof(f135,plain,(
% 0.21/0.44    spl1_16 | ~spl1_5 | ~spl1_15),
% 0.21/0.44    inference(avatar_split_clause,[],[f129,f125,f74,f133])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    spl1_5 <=> ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.44  fof(f125,plain,(
% 0.21/0.44    spl1_15 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.21/0.44  fof(f129,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)) ) | (~spl1_5 | ~spl1_15)),
% 0.21/0.44    inference(resolution,[],[f126,f75])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) ) | ~spl1_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f74])).
% 0.21/0.44  fof(f126,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl1_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f125])).
% 0.21/0.44  fof(f127,plain,(
% 0.21/0.44    spl1_15 | ~spl1_2 | ~spl1_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f122,f119,f61,f125])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.44  fof(f119,plain,(
% 0.21/0.44    spl1_14 <=> ! [X1,X0] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | (~spl1_2 | ~spl1_14)),
% 0.21/0.44    inference(resolution,[],[f120,f63])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f61])).
% 0.21/0.44  fof(f120,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) ) | ~spl1_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f119])).
% 0.21/0.44  fof(f121,plain,(
% 0.21/0.44    spl1_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f41,f119])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    spl1_13 | ~spl1_6 | ~spl1_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f108,f87,f78,f114])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    spl1_6 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    spl1_8 <=> ! [X0] : v4_relat_1(k6_partfun1(X0),X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    v4_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_6 | ~spl1_8)),
% 0.21/0.44    inference(superposition,[],[f88,f80])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl1_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f78])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) ) | ~spl1_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f87])).
% 0.21/0.44  fof(f112,plain,(
% 0.21/0.44    spl1_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f39,f110])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,axiom,(
% 0.21/0.44    ! [X0,X1] : (l1_orders_2(X1) => v1_yellow_1(k2_funcop_1(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    spl1_11 | ~spl1_6 | ~spl1_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f102,f83,f78,f104])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    spl1_7 <=> ! [X0] : v1_partfun1(k6_partfun1(X0),X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    v1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl1_6 | ~spl1_7)),
% 0.21/0.44    inference(superposition,[],[f84,f80])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) ) | ~spl1_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f83])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    spl1_10 | ~spl1_3 | ~spl1_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f91,f78,f66,f98])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    spl1_3 <=> ! [X0] : v1_funct_1(k6_partfun1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    v1_funct_1(k1_xboole_0) | (~spl1_3 | ~spl1_6)),
% 0.21/0.44    inference(superposition,[],[f67,f80])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) ) | ~spl1_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f66])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    spl1_9 | ~spl1_4 | ~spl1_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f90,f78,f70,f93])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    spl1_4 <=> ! [X0] : v1_relat_1(k6_partfun1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    v1_relat_1(k1_xboole_0) | (~spl1_4 | ~spl1_6)),
% 0.21/0.44    inference(superposition,[],[f71,f80])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) ) | ~spl1_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f70])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    spl1_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f51,f87])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f33,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0] : (v1_partfun1(k6_relat_1(X0),X0) & v1_funct_1(k6_relat_1(X0)) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_funct_2)).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    spl1_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f49,f83])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f35,f30])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X0] : (v1_partfun1(k6_relat_1(X0),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    spl1_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f48,f78])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.21/0.44    inference(definition_unfolding,[],[f28,f30])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    spl1_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f29,f74])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,axiom,(
% 0.21/0.44    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    spl1_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f52,f70])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f32,f30])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    spl1_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f50,f66])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f34,f30])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    spl1_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f27,f61])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    spl1_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f25,f56])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    l1_orders_2(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (25532)------------------------------
% 0.21/0.44  % (25532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (25532)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (25532)Memory used [KB]: 6140
% 0.21/0.44  % (25532)Time elapsed: 0.009 s
% 0.21/0.44  % (25532)------------------------------
% 0.21/0.44  % (25532)------------------------------
% 0.21/0.44  % (25524)Success in time 0.079 s
%------------------------------------------------------------------------------
