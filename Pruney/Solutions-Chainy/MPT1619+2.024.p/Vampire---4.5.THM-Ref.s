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

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 239 expanded)
%              Number of leaves         :   38 (  94 expanded)
%              Depth                    :   10
%              Number of atoms          :  314 ( 476 expanded)
%              Number of equality atoms :   71 ( 157 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f80,f84,f89,f93,f97,f103,f107,f119,f123,f132,f136,f141,f147,f152,f156,f164,f171])).

fof(f171,plain,
    ( ~ spl1_1
    | ~ spl1_13 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_13 ),
    inference(subsumption_resolution,[],[f69,f127])).

fof(f127,plain,
    ( ! [X0] : ~ l1_orders_2(X0)
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl1_13
  <=> ! [X0] : ~ l1_orders_2(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f69,plain,
    ( l1_orders_2(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl1_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f164,plain,
    ( ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_14
    | ~ spl1_17
    | spl1_18
    | ~ spl1_19 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_14
    | ~ spl1_17
    | spl1_18
    | ~ spl1_19 ),
    inference(subsumption_resolution,[],[f162,f151])).

fof(f151,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | spl1_18 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl1_18
  <=> k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f162,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_14
    | ~ spl1_17
    | ~ spl1_19 ),
    inference(forward_demodulation,[],[f161,f146])).

fof(f146,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl1_17
  <=> k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f161,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_14
    | ~ spl1_19 ),
    inference(subsumption_resolution,[],[f160,f74])).

fof(f74,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl1_2
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f160,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_14
    | ~ spl1_19 ),
    inference(subsumption_resolution,[],[f159,f83])).

fof(f83,plain,
    ( ! [X0] : v4_relat_1(k1_xboole_0,X0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl1_4
  <=> ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f159,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_8
    | ~ spl1_14
    | ~ spl1_19 ),
    inference(subsumption_resolution,[],[f158,f102])).

fof(f102,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl1_8
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f158,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_14
    | ~ spl1_19 ),
    inference(subsumption_resolution,[],[f157,f131])).

fof(f131,plain,
    ( v1_yellow_1(k1_xboole_0)
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl1_14
  <=> v1_yellow_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f157,plain,
    ( ~ v1_yellow_1(k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_19 ),
    inference(resolution,[],[f155,f79])).

fof(f79,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl1_3
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_19 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl1_19
  <=> ! [X0] :
        ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f156,plain,(
    spl1_19 ),
    inference(avatar_split_clause,[],[f64,f154])).

fof(f64,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f45,f61,f39,f61])).

fof(f39,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f152,plain,(
    ~ spl1_18 ),
    inference(avatar_split_clause,[],[f62,f149])).

fof(f62,plain,(
    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f36,f61,f39,f61])).

fof(f36,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
        & l1_orders_2(X0) )
   => ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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

fof(f147,plain,
    ( spl1_17
    | ~ spl1_11
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f142,f139,f117,f144])).

fof(f117,plain,
    ( spl1_11
  <=> ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f139,plain,
    ( spl1_16
  <=> ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f142,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_11
    | ~ spl1_16 ),
    inference(superposition,[],[f140,f118])).

fof(f118,plain,
    ( ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f140,plain,
    ( ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f139])).

fof(f141,plain,
    ( spl1_16
    | ~ spl1_1
    | ~ spl1_15 ),
    inference(avatar_split_clause,[],[f137,f134,f67,f139])).

fof(f134,plain,
    ( spl1_15
  <=> ! [X1,X0] :
        ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f137,plain,
    ( ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))
    | ~ spl1_1
    | ~ spl1_15 ),
    inference(resolution,[],[f135,f69])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(X1)
        | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) )
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f134])).

fof(f136,plain,(
    spl1_15 ),
    inference(avatar_split_clause,[],[f65,f134])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(definition_unfolding,[],[f50,f46])).

fof(f46,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f132,plain,
    ( spl1_13
    | spl1_14
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f124,f121,f117,f129,f126])).

fof(f121,plain,
    ( spl1_12
  <=> ! [X1,X0] :
        ( v1_yellow_1(k2_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f124,plain,
    ( ! [X0] :
        ( v1_yellow_1(k1_xboole_0)
        | ~ l1_orders_2(X0) )
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(superposition,[],[f122,f118])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( v1_yellow_1(k2_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,(
    spl1_12 ),
    inference(avatar_split_clause,[],[f49,f121])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => v1_yellow_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).

fof(f119,plain,
    ( spl1_11
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f108,f105,f91,f117])).

fof(f91,plain,
    ( spl1_6
  <=> ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f105,plain,
    ( spl1_9
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f108,plain,
    ( ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(resolution,[],[f106,f92])).

fof(f92,plain,
    ( ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f107,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f44,f105])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f103,plain,
    ( spl1_8
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f98,f95,f86,f100])).

fof(f86,plain,
    ( spl1_5
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f95,plain,
    ( spl1_7
  <=> ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f98,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(superposition,[],[f96,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f96,plain,
    ( ! [X0] : v1_partfun1(k6_relat_1(X0),X0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f97,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f63,f95])).

fof(f63,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(definition_unfolding,[],[f43,f39])).

fof(f43,plain,(
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

fof(f93,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f38,f91])).

fof(f38,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(f89,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f37,f86])).

fof(f37,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f84,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f48,f82])).

fof(f48,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

fof(f80,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f42,f77])).

fof(f42,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( v1_funct_1(k1_xboole_0)
    & v1_relat_1(k1_xboole_0) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

fof(f75,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f41,f72])).

fof(f41,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f35,f67])).

fof(f35,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.08  % Command    : run_vampire %s %d
% 0.07/0.27  % Computer   : n019.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 14:29:52 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.12/0.32  % (18058)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.12/0.33  % (18058)Refutation found. Thanks to Tanya!
% 0.12/0.33  % SZS status Theorem for theBenchmark
% 0.12/0.33  % SZS output start Proof for theBenchmark
% 0.12/0.33  fof(f172,plain,(
% 0.12/0.33    $false),
% 0.12/0.33    inference(avatar_sat_refutation,[],[f70,f75,f80,f84,f89,f93,f97,f103,f107,f119,f123,f132,f136,f141,f147,f152,f156,f164,f171])).
% 0.12/0.33  fof(f171,plain,(
% 0.12/0.33    ~spl1_1 | ~spl1_13),
% 0.12/0.33    inference(avatar_contradiction_clause,[],[f170])).
% 0.12/0.33  fof(f170,plain,(
% 0.12/0.33    $false | (~spl1_1 | ~spl1_13)),
% 0.12/0.33    inference(subsumption_resolution,[],[f69,f127])).
% 0.12/0.33  fof(f127,plain,(
% 0.12/0.33    ( ! [X0] : (~l1_orders_2(X0)) ) | ~spl1_13),
% 0.12/0.33    inference(avatar_component_clause,[],[f126])).
% 0.12/0.33  fof(f126,plain,(
% 0.12/0.33    spl1_13 <=> ! [X0] : ~l1_orders_2(X0)),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.12/0.33  fof(f69,plain,(
% 0.12/0.33    l1_orders_2(sK0) | ~spl1_1),
% 0.12/0.33    inference(avatar_component_clause,[],[f67])).
% 0.12/0.33  fof(f67,plain,(
% 0.12/0.33    spl1_1 <=> l1_orders_2(sK0)),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.12/0.33  fof(f164,plain,(
% 0.12/0.33    ~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_8 | ~spl1_14 | ~spl1_17 | spl1_18 | ~spl1_19),
% 0.12/0.33    inference(avatar_contradiction_clause,[],[f163])).
% 0.12/0.33  fof(f163,plain,(
% 0.12/0.33    $false | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_8 | ~spl1_14 | ~spl1_17 | spl1_18 | ~spl1_19)),
% 0.12/0.33    inference(subsumption_resolution,[],[f162,f151])).
% 0.12/0.33  fof(f151,plain,(
% 0.12/0.33    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | spl1_18),
% 0.12/0.33    inference(avatar_component_clause,[],[f149])).
% 0.12/0.33  fof(f149,plain,(
% 0.12/0.33    spl1_18 <=> k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.12/0.33  fof(f162,plain,(
% 0.12/0.33    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_8 | ~spl1_14 | ~spl1_17 | ~spl1_19)),
% 0.12/0.33    inference(forward_demodulation,[],[f161,f146])).
% 0.12/0.33  fof(f146,plain,(
% 0.12/0.33    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~spl1_17),
% 0.12/0.33    inference(avatar_component_clause,[],[f144])).
% 0.12/0.33  fof(f144,plain,(
% 0.12/0.33    spl1_17 <=> k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.12/0.33  fof(f161,plain,(
% 0.12/0.33    g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_8 | ~spl1_14 | ~spl1_19)),
% 0.12/0.33    inference(subsumption_resolution,[],[f160,f74])).
% 0.12/0.33  fof(f74,plain,(
% 0.12/0.33    v1_relat_1(k1_xboole_0) | ~spl1_2),
% 0.12/0.33    inference(avatar_component_clause,[],[f72])).
% 0.12/0.33  fof(f72,plain,(
% 0.12/0.33    spl1_2 <=> v1_relat_1(k1_xboole_0)),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.12/0.33  fof(f160,plain,(
% 0.12/0.33    g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl1_3 | ~spl1_4 | ~spl1_8 | ~spl1_14 | ~spl1_19)),
% 0.12/0.33    inference(subsumption_resolution,[],[f159,f83])).
% 0.12/0.33  fof(f83,plain,(
% 0.12/0.33    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) ) | ~spl1_4),
% 0.12/0.33    inference(avatar_component_clause,[],[f82])).
% 0.12/0.33  fof(f82,plain,(
% 0.12/0.33    spl1_4 <=> ! [X0] : v4_relat_1(k1_xboole_0,X0)),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.12/0.33  fof(f159,plain,(
% 0.12/0.33    g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl1_3 | ~spl1_8 | ~spl1_14 | ~spl1_19)),
% 0.12/0.33    inference(subsumption_resolution,[],[f158,f102])).
% 0.12/0.33  fof(f102,plain,(
% 0.12/0.33    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl1_8),
% 0.12/0.33    inference(avatar_component_clause,[],[f100])).
% 0.12/0.33  fof(f100,plain,(
% 0.12/0.33    spl1_8 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.12/0.33  fof(f158,plain,(
% 0.12/0.33    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl1_3 | ~spl1_14 | ~spl1_19)),
% 0.12/0.33    inference(subsumption_resolution,[],[f157,f131])).
% 0.12/0.33  fof(f131,plain,(
% 0.12/0.33    v1_yellow_1(k1_xboole_0) | ~spl1_14),
% 0.12/0.33    inference(avatar_component_clause,[],[f129])).
% 0.12/0.33  fof(f129,plain,(
% 0.12/0.33    spl1_14 <=> v1_yellow_1(k1_xboole_0)),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.12/0.33  fof(f157,plain,(
% 0.12/0.33    ~v1_yellow_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl1_3 | ~spl1_19)),
% 0.12/0.33    inference(resolution,[],[f155,f79])).
% 0.12/0.33  fof(f79,plain,(
% 0.12/0.33    v1_funct_1(k1_xboole_0) | ~spl1_3),
% 0.12/0.33    inference(avatar_component_clause,[],[f77])).
% 0.12/0.33  fof(f77,plain,(
% 0.12/0.33    spl1_3 <=> v1_funct_1(k1_xboole_0)),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.12/0.33  fof(f155,plain,(
% 0.12/0.33    ( ! [X0] : (~v1_funct_1(X0) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl1_19),
% 0.12/0.33    inference(avatar_component_clause,[],[f154])).
% 0.12/0.33  fof(f154,plain,(
% 0.12/0.33    spl1_19 <=> ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 0.12/0.33  fof(f156,plain,(
% 0.12/0.33    spl1_19),
% 0.12/0.33    inference(avatar_split_clause,[],[f64,f154])).
% 0.12/0.33  fof(f64,plain,(
% 0.12/0.33    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.12/0.33    inference(definition_unfolding,[],[f45,f61,f39,f61])).
% 0.12/0.33  fof(f39,plain,(
% 0.12/0.33    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.12/0.33    inference(cnf_transformation,[],[f13])).
% 0.12/0.33  fof(f13,axiom,(
% 0.12/0.33    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.12/0.33  fof(f61,plain,(
% 0.12/0.33    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.12/0.33    inference(definition_unfolding,[],[f40,f60])).
% 0.12/0.33  fof(f60,plain,(
% 0.12/0.33    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.12/0.33    inference(definition_unfolding,[],[f47,f59])).
% 0.12/0.33  fof(f59,plain,(
% 0.12/0.33    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.12/0.33    inference(definition_unfolding,[],[f51,f58])).
% 0.12/0.33  fof(f58,plain,(
% 0.12/0.33    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.12/0.33    inference(definition_unfolding,[],[f52,f57])).
% 0.12/0.33  fof(f57,plain,(
% 0.12/0.33    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.12/0.33    inference(definition_unfolding,[],[f53,f56])).
% 0.12/0.33  fof(f56,plain,(
% 0.12/0.33    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.12/0.33    inference(definition_unfolding,[],[f54,f55])).
% 0.12/0.33  fof(f55,plain,(
% 0.12/0.33    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.12/0.33    inference(cnf_transformation,[],[f8])).
% 0.12/0.33  fof(f8,axiom,(
% 0.12/0.33    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.12/0.33  fof(f54,plain,(
% 0.12/0.33    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.12/0.33    inference(cnf_transformation,[],[f7])).
% 0.12/0.33  fof(f7,axiom,(
% 0.12/0.33    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.12/0.33  fof(f53,plain,(
% 0.12/0.33    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.12/0.33    inference(cnf_transformation,[],[f6])).
% 0.12/0.33  fof(f6,axiom,(
% 0.12/0.33    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.12/0.33  fof(f52,plain,(
% 0.12/0.33    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.12/0.33    inference(cnf_transformation,[],[f5])).
% 0.12/0.33  fof(f5,axiom,(
% 0.12/0.33    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.12/0.33  fof(f51,plain,(
% 0.12/0.33    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.12/0.33    inference(cnf_transformation,[],[f4])).
% 0.12/0.33  fof(f4,axiom,(
% 0.12/0.33    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.12/0.33  fof(f47,plain,(
% 0.12/0.33    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.12/0.33    inference(cnf_transformation,[],[f3])).
% 0.12/0.33  fof(f3,axiom,(
% 0.12/0.33    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.12/0.33  fof(f40,plain,(
% 0.12/0.33    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.12/0.33    inference(cnf_transformation,[],[f2])).
% 0.12/0.33  fof(f2,axiom,(
% 0.12/0.33    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.12/0.33  fof(f45,plain,(
% 0.12/0.33    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.12/0.33    inference(cnf_transformation,[],[f28])).
% 0.12/0.33  fof(f28,plain,(
% 0.12/0.33    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.12/0.33    inference(flattening,[],[f27])).
% 0.12/0.33  fof(f27,plain,(
% 0.12/0.33    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.12/0.33    inference(ennf_transformation,[],[f18])).
% 0.12/0.33  fof(f18,axiom,(
% 0.12/0.33    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).
% 0.12/0.33  fof(f152,plain,(
% 0.12/0.33    ~spl1_18),
% 0.12/0.33    inference(avatar_split_clause,[],[f62,f149])).
% 0.12/0.33  fof(f62,plain,(
% 0.12/0.33    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_relat_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 0.12/0.33    inference(definition_unfolding,[],[f36,f61,f39,f61])).
% 0.12/0.33  fof(f36,plain,(
% 0.12/0.33    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)),
% 0.12/0.33    inference(cnf_transformation,[],[f32])).
% 0.12/0.33  fof(f32,plain,(
% 0.12/0.33    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0)),
% 0.12/0.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f31])).
% 0.12/0.33  fof(f31,plain,(
% 0.12/0.33    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0)) => (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0))),
% 0.12/0.33    introduced(choice_axiom,[])).
% 0.12/0.33  fof(f25,plain,(
% 0.12/0.33    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0))),
% 0.12/0.33    inference(ennf_transformation,[],[f20])).
% 0.12/0.33  fof(f20,negated_conjecture,(
% 0.12/0.33    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.12/0.33    inference(negated_conjecture,[],[f19])).
% 0.12/0.33  fof(f19,conjecture,(
% 0.12/0.33    ! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).
% 0.12/0.33  fof(f147,plain,(
% 0.12/0.33    spl1_17 | ~spl1_11 | ~spl1_16),
% 0.12/0.33    inference(avatar_split_clause,[],[f142,f139,f117,f144])).
% 0.12/0.33  fof(f117,plain,(
% 0.12/0.33    spl1_11 <=> ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.12/0.33  fof(f139,plain,(
% 0.12/0.33    spl1_16 <=> ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.12/0.33  fof(f142,plain,(
% 0.12/0.33    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | (~spl1_11 | ~spl1_16)),
% 0.12/0.33    inference(superposition,[],[f140,f118])).
% 0.12/0.33  fof(f118,plain,(
% 0.12/0.33    ( ! [X0] : (k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)) ) | ~spl1_11),
% 0.12/0.33    inference(avatar_component_clause,[],[f117])).
% 0.12/0.33  fof(f140,plain,(
% 0.12/0.33    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))) ) | ~spl1_16),
% 0.12/0.33    inference(avatar_component_clause,[],[f139])).
% 0.12/0.33  fof(f141,plain,(
% 0.12/0.33    spl1_16 | ~spl1_1 | ~spl1_15),
% 0.12/0.33    inference(avatar_split_clause,[],[f137,f134,f67,f139])).
% 0.12/0.33  fof(f134,plain,(
% 0.12/0.33    spl1_15 <=> ! [X1,X0] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.12/0.33  fof(f137,plain,(
% 0.12/0.33    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))) ) | (~spl1_1 | ~spl1_15)),
% 0.12/0.33    inference(resolution,[],[f135,f69])).
% 0.12/0.33  fof(f135,plain,(
% 0.12/0.33    ( ! [X0,X1] : (~l1_orders_2(X1) | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))) ) | ~spl1_15),
% 0.12/0.33    inference(avatar_component_clause,[],[f134])).
% 0.12/0.33  fof(f136,plain,(
% 0.12/0.33    spl1_15),
% 0.12/0.33    inference(avatar_split_clause,[],[f65,f134])).
% 0.12/0.33  fof(f65,plain,(
% 0.12/0.33    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.12/0.33    inference(definition_unfolding,[],[f50,f46])).
% 0.12/0.33  fof(f46,plain,(
% 0.12/0.33    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 0.12/0.33    inference(cnf_transformation,[],[f17])).
% 0.12/0.33  fof(f17,axiom,(
% 0.12/0.33    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).
% 0.12/0.33  fof(f50,plain,(
% 0.12/0.33    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.12/0.33    inference(cnf_transformation,[],[f30])).
% 0.12/0.33  fof(f30,plain,(
% 0.12/0.33    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.12/0.33    inference(ennf_transformation,[],[f14])).
% 0.12/0.33  fof(f14,axiom,(
% 0.12/0.33    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).
% 0.12/0.33  fof(f132,plain,(
% 0.12/0.33    spl1_13 | spl1_14 | ~spl1_11 | ~spl1_12),
% 0.12/0.33    inference(avatar_split_clause,[],[f124,f121,f117,f129,f126])).
% 0.12/0.33  fof(f121,plain,(
% 0.12/0.33    spl1_12 <=> ! [X1,X0] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.12/0.33  fof(f124,plain,(
% 0.12/0.33    ( ! [X0] : (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(X0)) ) | (~spl1_11 | ~spl1_12)),
% 0.12/0.33    inference(superposition,[],[f122,f118])).
% 0.12/0.33  fof(f122,plain,(
% 0.12/0.33    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) ) | ~spl1_12),
% 0.12/0.33    inference(avatar_component_clause,[],[f121])).
% 0.12/0.33  fof(f123,plain,(
% 0.12/0.33    spl1_12),
% 0.12/0.33    inference(avatar_split_clause,[],[f49,f121])).
% 0.12/0.33  fof(f49,plain,(
% 0.12/0.33    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.12/0.33    inference(cnf_transformation,[],[f29])).
% 0.12/0.33  fof(f29,plain,(
% 0.12/0.33    ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.12/0.33    inference(ennf_transformation,[],[f15])).
% 0.12/0.33  fof(f15,axiom,(
% 0.12/0.33    ! [X0,X1] : (l1_orders_2(X1) => v1_yellow_1(k2_funcop_1(X0,X1)))),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).
% 0.12/0.33  fof(f119,plain,(
% 0.12/0.33    spl1_11 | ~spl1_6 | ~spl1_9),
% 0.12/0.33    inference(avatar_split_clause,[],[f108,f105,f91,f117])).
% 0.12/0.33  fof(f91,plain,(
% 0.12/0.33    spl1_6 <=> ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.12/0.33  fof(f105,plain,(
% 0.12/0.33    spl1_9 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.12/0.33  fof(f108,plain,(
% 0.12/0.33    ( ! [X0] : (k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)) ) | (~spl1_6 | ~spl1_9)),
% 0.12/0.33    inference(resolution,[],[f106,f92])).
% 0.12/0.33  fof(f92,plain,(
% 0.12/0.33    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) ) | ~spl1_6),
% 0.12/0.33    inference(avatar_component_clause,[],[f91])).
% 0.12/0.33  fof(f106,plain,(
% 0.12/0.33    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl1_9),
% 0.12/0.33    inference(avatar_component_clause,[],[f105])).
% 0.12/0.33  fof(f107,plain,(
% 0.12/0.33    spl1_9),
% 0.12/0.33    inference(avatar_split_clause,[],[f44,f105])).
% 0.12/0.33  fof(f44,plain,(
% 0.12/0.33    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.12/0.33    inference(cnf_transformation,[],[f26])).
% 0.12/0.33  fof(f26,plain,(
% 0.12/0.33    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.12/0.33    inference(ennf_transformation,[],[f1])).
% 0.12/0.33  fof(f1,axiom,(
% 0.12/0.33    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.12/0.33  fof(f103,plain,(
% 0.12/0.33    spl1_8 | ~spl1_5 | ~spl1_7),
% 0.12/0.33    inference(avatar_split_clause,[],[f98,f95,f86,f100])).
% 0.12/0.33  fof(f86,plain,(
% 0.12/0.33    spl1_5 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.12/0.33  fof(f95,plain,(
% 0.12/0.33    spl1_7 <=> ! [X0] : v1_partfun1(k6_relat_1(X0),X0)),
% 0.12/0.33    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.12/0.33  fof(f98,plain,(
% 0.12/0.33    v1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl1_5 | ~spl1_7)),
% 0.12/0.33    inference(superposition,[],[f96,f88])).
% 0.12/0.33  fof(f88,plain,(
% 0.12/0.33    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_5),
% 0.12/0.33    inference(avatar_component_clause,[],[f86])).
% 0.12/0.33  fof(f96,plain,(
% 0.12/0.33    ( ! [X0] : (v1_partfun1(k6_relat_1(X0),X0)) ) | ~spl1_7),
% 0.12/0.33    inference(avatar_component_clause,[],[f95])).
% 0.12/0.33  fof(f97,plain,(
% 0.12/0.33    spl1_7),
% 0.12/0.33    inference(avatar_split_clause,[],[f63,f95])).
% 0.12/0.33  fof(f63,plain,(
% 0.12/0.33    ( ! [X0] : (v1_partfun1(k6_relat_1(X0),X0)) )),
% 0.12/0.33    inference(definition_unfolding,[],[f43,f39])).
% 0.12/0.33  fof(f43,plain,(
% 0.12/0.33    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.12/0.33    inference(cnf_transformation,[],[f21])).
% 0.12/0.33  fof(f21,plain,(
% 0.12/0.33    ! [X0] : v1_partfun1(k6_partfun1(X0),X0)),
% 0.12/0.33    inference(pure_predicate_removal,[],[f12])).
% 0.12/0.33  fof(f12,axiom,(
% 0.12/0.33    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.12/0.33  fof(f93,plain,(
% 0.12/0.33    spl1_6),
% 0.12/0.33    inference(avatar_split_clause,[],[f38,f91])).
% 0.12/0.33  fof(f38,plain,(
% 0.12/0.33    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 0.12/0.33    inference(cnf_transformation,[],[f16])).
% 0.12/0.33  fof(f16,axiom,(
% 0.12/0.33    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).
% 0.12/0.33  fof(f89,plain,(
% 0.12/0.33    spl1_5),
% 0.12/0.33    inference(avatar_split_clause,[],[f37,f86])).
% 0.12/0.33  fof(f37,plain,(
% 0.12/0.33    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.12/0.33    inference(cnf_transformation,[],[f10])).
% 0.12/0.33  fof(f10,axiom,(
% 0.12/0.33    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.12/0.33  fof(f84,plain,(
% 0.12/0.33    spl1_4),
% 0.12/0.33    inference(avatar_split_clause,[],[f48,f82])).
% 0.12/0.33  fof(f48,plain,(
% 0.12/0.33    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 0.12/0.33    inference(cnf_transformation,[],[f34])).
% 0.12/0.33  fof(f34,plain,(
% 0.12/0.33    ! [X0] : v4_relat_1(k1_xboole_0,X0)),
% 0.12/0.33    inference(rectify,[],[f23])).
% 0.12/0.33  fof(f23,plain,(
% 0.12/0.33    ! [X0,X1] : v4_relat_1(k1_xboole_0,X0)),
% 0.12/0.33    inference(pure_predicate_removal,[],[f9])).
% 0.12/0.33  fof(f9,axiom,(
% 0.12/0.33    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).
% 0.12/0.33  fof(f80,plain,(
% 0.12/0.33    spl1_3),
% 0.12/0.33    inference(avatar_split_clause,[],[f42,f77])).
% 0.12/0.33  fof(f42,plain,(
% 0.12/0.33    v1_funct_1(k1_xboole_0)),
% 0.12/0.33    inference(cnf_transformation,[],[f33])).
% 0.12/0.33  fof(f33,plain,(
% 0.12/0.33    v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0)),
% 0.12/0.33    inference(rectify,[],[f24])).
% 0.12/0.33  fof(f24,plain,(
% 0.12/0.33    ! [X0] : (v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0))),
% 0.12/0.33    inference(pure_predicate_removal,[],[f22])).
% 0.12/0.33  fof(f22,plain,(
% 0.12/0.33    ! [X0] : (v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.12/0.33    inference(pure_predicate_removal,[],[f11])).
% 0.12/0.33  fof(f11,axiom,(
% 0.12/0.33    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.12/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.12/0.33  fof(f75,plain,(
% 0.12/0.33    spl1_2),
% 0.12/0.33    inference(avatar_split_clause,[],[f41,f72])).
% 0.12/0.33  fof(f41,plain,(
% 0.12/0.33    v1_relat_1(k1_xboole_0)),
% 0.12/0.33    inference(cnf_transformation,[],[f33])).
% 0.12/0.33  fof(f70,plain,(
% 0.12/0.33    spl1_1),
% 0.12/0.33    inference(avatar_split_clause,[],[f35,f67])).
% 0.12/0.33  fof(f35,plain,(
% 0.12/0.33    l1_orders_2(sK0)),
% 0.12/0.33    inference(cnf_transformation,[],[f32])).
% 0.12/0.33  % SZS output end Proof for theBenchmark
% 0.12/0.33  % (18058)------------------------------
% 0.12/0.33  % (18058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.33  % (18058)Termination reason: Refutation
% 0.12/0.33  
% 0.12/0.33  % (18058)Memory used [KB]: 6140
% 0.12/0.33  % (18058)Time elapsed: 0.007 s
% 0.12/0.33  % (18058)------------------------------
% 0.12/0.33  % (18058)------------------------------
% 0.12/0.33  % (18046)Success in time 0.046 s
%------------------------------------------------------------------------------
