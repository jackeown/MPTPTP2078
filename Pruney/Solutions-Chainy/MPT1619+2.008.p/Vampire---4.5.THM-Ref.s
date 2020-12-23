%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 267 expanded)
%              Number of leaves         :   43 ( 111 expanded)
%              Depth                    :   10
%              Number of atoms          :  365 ( 561 expanded)
%              Number of equality atoms :   75 ( 169 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f76,f80,f84,f88,f92,f97,f101,f108,f113,f119,f123,f130,f134,f143,f147,f152,f158,f163,f167,f172,f180,f184])).

fof(f184,plain,
    ( ~ spl1_1
    | ~ spl1_15 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_15 ),
    inference(subsumption_resolution,[],[f70,f138])).

fof(f138,plain,
    ( ! [X0] : ~ l1_orders_2(X0)
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl1_15
  <=> ! [X0] : ~ l1_orders_2(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f70,plain,
    ( l1_orders_2(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl1_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f180,plain,
    ( ~ spl1_2
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_11
    | ~ spl1_16
    | ~ spl1_19
    | spl1_20
    | ~ spl1_22 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_11
    | ~ spl1_16
    | ~ spl1_19
    | spl1_20
    | ~ spl1_22 ),
    inference(subsumption_resolution,[],[f178,f162])).

fof(f162,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | spl1_20 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl1_20
  <=> k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f178,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ spl1_2
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_11
    | ~ spl1_16
    | ~ spl1_19
    | ~ spl1_22 ),
    inference(forward_demodulation,[],[f177,f157])).

fof(f157,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_19 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl1_19
  <=> k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f177,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_11
    | ~ spl1_16
    | ~ spl1_22 ),
    inference(subsumption_resolution,[],[f176,f142])).

fof(f142,plain,
    ( v1_yellow_1(k1_xboole_0)
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl1_16
  <=> v1_yellow_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f176,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_11
    | ~ spl1_22 ),
    inference(subsumption_resolution,[],[f175,f107])).

fof(f107,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl1_9
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f175,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_10
    | ~ spl1_11
    | ~ spl1_22 ),
    inference(subsumption_resolution,[],[f174,f118])).

fof(f118,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl1_11
  <=> v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f174,plain,
    ( g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_10
    | ~ spl1_22 ),
    inference(subsumption_resolution,[],[f173,f112])).

fof(f112,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl1_10
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f173,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_yellow_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_22 ),
    inference(resolution,[],[f171,f75])).

fof(f75,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_yellow_1(X0) )
    | ~ spl1_22 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl1_22
  <=> ! [X0] :
        ( ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f172,plain,
    ( spl1_22
    | ~ spl1_6
    | ~ spl1_21 ),
    inference(avatar_split_clause,[],[f168,f165,f90,f170])).

fof(f90,plain,
    ( spl1_6
  <=> ! [X0] :
        ( v1_funct_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f165,plain,
    ( spl1_21
  <=> ! [X0] :
        ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_6
    | ~ spl1_21 ),
    inference(resolution,[],[f166,f91])).

fof(f91,plain,
    ( ! [X0] :
        ( v1_funct_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_21 ),
    inference(avatar_component_clause,[],[f165])).

fof(f167,plain,(
    spl1_21 ),
    inference(avatar_split_clause,[],[f65,f165])).

fof(f65,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f45,f60,f60])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

fof(f163,plain,(
    ~ spl1_20 ),
    inference(avatar_split_clause,[],[f61,f160])).

fof(f61,plain,(
    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f34,f60,f60])).

fof(f34,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
        & l1_orders_2(X0) )
   => ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

fof(f158,plain,
    ( spl1_19
    | ~ spl1_13
    | ~ spl1_18 ),
    inference(avatar_split_clause,[],[f153,f150,f128,f155])).

fof(f128,plain,
    ( spl1_13
  <=> ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f150,plain,
    ( spl1_18
  <=> ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f153,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_13
    | ~ spl1_18 ),
    inference(superposition,[],[f151,f129])).

fof(f129,plain,
    ( ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f128])).

fof(f151,plain,
    ( ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f150])).

fof(f152,plain,
    ( spl1_18
    | ~ spl1_1
    | ~ spl1_17 ),
    inference(avatar_split_clause,[],[f148,f145,f68,f150])).

fof(f145,plain,
    ( spl1_17
  <=> ! [X1,X0] :
        ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f148,plain,
    ( ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))
    | ~ spl1_1
    | ~ spl1_17 ),
    inference(resolution,[],[f146,f70])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(X1)
        | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) )
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f145])).

fof(f147,plain,(
    spl1_17 ),
    inference(avatar_split_clause,[],[f66,f145])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(definition_unfolding,[],[f49,f46])).

fof(f46,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f143,plain,
    ( spl1_15
    | spl1_16
    | ~ spl1_13
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f135,f132,f128,f140,f137])).

fof(f132,plain,
    ( spl1_14
  <=> ! [X1,X0] :
        ( v1_yellow_1(k2_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f135,plain,
    ( ! [X0] :
        ( v1_yellow_1(k1_xboole_0)
        | ~ l1_orders_2(X0) )
    | ~ spl1_13
    | ~ spl1_14 ),
    inference(superposition,[],[f133,f129])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( v1_yellow_1(k2_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,(
    spl1_14 ),
    inference(avatar_split_clause,[],[f48,f132])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => v1_yellow_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).

fof(f130,plain,
    ( spl1_13
    | ~ spl1_4
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f125,f121,f82,f128])).

fof(f82,plain,
    ( spl1_4
  <=> ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f121,plain,
    ( spl1_12
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f125,plain,
    ( ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)
    | ~ spl1_4
    | ~ spl1_12 ),
    inference(resolution,[],[f122,f83])).

fof(f83,plain,
    ( ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,(
    spl1_12 ),
    inference(avatar_split_clause,[],[f44,f121])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f119,plain,
    ( spl1_11
    | ~ spl1_7
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f114,f99,f94,f116])).

fof(f94,plain,
    ( spl1_7
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f99,plain,
    ( spl1_8
  <=> ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f114,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_7
    | ~ spl1_8 ),
    inference(superposition,[],[f100,f96])).

fof(f96,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f100,plain,
    ( ! [X0] : v4_relat_1(k6_partfun1(X0),X0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f113,plain,
    ( spl1_10
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f102,f94,f86,f110])).

fof(f86,plain,
    ( spl1_5
  <=> ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f102,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(superposition,[],[f87,f96])).

fof(f87,plain,
    ( ! [X0] : v1_partfun1(k6_partfun1(X0),X0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f108,plain,
    ( spl1_9
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f103,f94,f78,f105])).

fof(f78,plain,
    ( spl1_3
  <=> ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f103,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(superposition,[],[f79,f96])).

fof(f79,plain,
    ( ! [X0] : v1_relat_1(k6_partfun1(X0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f101,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f63,f99])).

fof(f63,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f38,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f41,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f97,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f62,f94])).

fof(f62,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f36,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f92,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f43,f90])).

fof(f43,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f88,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f42,f86])).

fof(f42,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f84,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f37,f82])).

fof(f37,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(f80,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f64,f78])).

fof(f64,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f35,f73])).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f71,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (21203)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.45  % (21199)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.45  % (21201)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (21203)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f185,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f71,f76,f80,f84,f88,f92,f97,f101,f108,f113,f119,f123,f130,f134,f143,f147,f152,f158,f163,f167,f172,f180,f184])).
% 0.20/0.45  fof(f184,plain,(
% 0.20/0.45    ~spl1_1 | ~spl1_15),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f183])).
% 0.20/0.45  fof(f183,plain,(
% 0.20/0.45    $false | (~spl1_1 | ~spl1_15)),
% 0.20/0.45    inference(subsumption_resolution,[],[f70,f138])).
% 0.20/0.45  fof(f138,plain,(
% 0.20/0.45    ( ! [X0] : (~l1_orders_2(X0)) ) | ~spl1_15),
% 0.20/0.45    inference(avatar_component_clause,[],[f137])).
% 0.20/0.45  fof(f137,plain,(
% 0.20/0.45    spl1_15 <=> ! [X0] : ~l1_orders_2(X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.20/0.45  fof(f70,plain,(
% 0.20/0.45    l1_orders_2(sK0) | ~spl1_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f68])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    spl1_1 <=> l1_orders_2(sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.45  fof(f180,plain,(
% 0.20/0.45    ~spl1_2 | ~spl1_9 | ~spl1_10 | ~spl1_11 | ~spl1_16 | ~spl1_19 | spl1_20 | ~spl1_22),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f179])).
% 0.20/0.45  fof(f179,plain,(
% 0.20/0.45    $false | (~spl1_2 | ~spl1_9 | ~spl1_10 | ~spl1_11 | ~spl1_16 | ~spl1_19 | spl1_20 | ~spl1_22)),
% 0.20/0.45    inference(subsumption_resolution,[],[f178,f162])).
% 0.20/0.45  fof(f162,plain,(
% 0.20/0.45    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | spl1_20),
% 0.20/0.45    inference(avatar_component_clause,[],[f160])).
% 0.20/0.45  fof(f160,plain,(
% 0.20/0.45    spl1_20 <=> k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.20/0.45  fof(f178,plain,(
% 0.20/0.45    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (~spl1_2 | ~spl1_9 | ~spl1_10 | ~spl1_11 | ~spl1_16 | ~spl1_19 | ~spl1_22)),
% 0.20/0.45    inference(forward_demodulation,[],[f177,f157])).
% 0.20/0.45  fof(f157,plain,(
% 0.20/0.45    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~spl1_19),
% 0.20/0.45    inference(avatar_component_clause,[],[f155])).
% 0.20/0.45  fof(f155,plain,(
% 0.20/0.45    spl1_19 <=> k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 0.20/0.45  fof(f177,plain,(
% 0.20/0.45    g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | (~spl1_2 | ~spl1_9 | ~spl1_10 | ~spl1_11 | ~spl1_16 | ~spl1_22)),
% 0.20/0.45    inference(subsumption_resolution,[],[f176,f142])).
% 0.20/0.45  fof(f142,plain,(
% 0.20/0.45    v1_yellow_1(k1_xboole_0) | ~spl1_16),
% 0.20/0.45    inference(avatar_component_clause,[],[f140])).
% 0.20/0.45  fof(f140,plain,(
% 0.20/0.45    spl1_16 <=> v1_yellow_1(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.20/0.45  fof(f176,plain,(
% 0.20/0.45    g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | (~spl1_2 | ~spl1_9 | ~spl1_10 | ~spl1_11 | ~spl1_22)),
% 0.20/0.45    inference(subsumption_resolution,[],[f175,f107])).
% 0.20/0.45  fof(f107,plain,(
% 0.20/0.45    v1_relat_1(k1_xboole_0) | ~spl1_9),
% 0.20/0.45    inference(avatar_component_clause,[],[f105])).
% 0.20/0.45  fof(f105,plain,(
% 0.20/0.45    spl1_9 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.20/0.45  fof(f175,plain,(
% 0.20/0.45    g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | (~spl1_2 | ~spl1_10 | ~spl1_11 | ~spl1_22)),
% 0.20/0.45    inference(subsumption_resolution,[],[f174,f118])).
% 0.20/0.45  fof(f118,plain,(
% 0.20/0.45    v4_relat_1(k1_xboole_0,k1_xboole_0) | ~spl1_11),
% 0.20/0.45    inference(avatar_component_clause,[],[f116])).
% 0.20/0.45  fof(f116,plain,(
% 0.20/0.45    spl1_11 <=> v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.20/0.45  fof(f174,plain,(
% 0.20/0.45    g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | (~spl1_2 | ~spl1_10 | ~spl1_22)),
% 0.20/0.45    inference(subsumption_resolution,[],[f173,f112])).
% 0.20/0.45  fof(f112,plain,(
% 0.20/0.45    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl1_10),
% 0.20/0.45    inference(avatar_component_clause,[],[f110])).
% 0.20/0.45  fof(f110,plain,(
% 0.20/0.45    spl1_10 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.20/0.45  fof(f173,plain,(
% 0.20/0.45    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | (~spl1_2 | ~spl1_22)),
% 0.20/0.45    inference(resolution,[],[f171,f75])).
% 0.20/0.45  fof(f75,plain,(
% 0.20/0.45    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f73])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.45  fof(f171,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_xboole_0(X0) | ~v1_partfun1(X0,k1_xboole_0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0) | ~v1_yellow_1(X0)) ) | ~spl1_22),
% 0.20/0.45    inference(avatar_component_clause,[],[f170])).
% 0.20/0.45  fof(f170,plain,(
% 0.20/0.45    spl1_22 <=> ! [X0] : (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.20/0.45  fof(f172,plain,(
% 0.20/0.45    spl1_22 | ~spl1_6 | ~spl1_21),
% 0.20/0.45    inference(avatar_split_clause,[],[f168,f165,f90,f170])).
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    spl1_6 <=> ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.45  fof(f165,plain,(
% 0.20/0.45    spl1_21 <=> ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).
% 0.20/0.45  fof(f168,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | (~spl1_6 | ~spl1_21)),
% 0.20/0.45    inference(resolution,[],[f166,f91])).
% 0.20/0.45  fof(f91,plain,(
% 0.20/0.45    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) ) | ~spl1_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f90])).
% 0.20/0.45  fof(f166,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_funct_1(X0) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl1_21),
% 0.20/0.45    inference(avatar_component_clause,[],[f165])).
% 0.20/0.45  fof(f167,plain,(
% 0.20/0.45    spl1_21),
% 0.20/0.45    inference(avatar_split_clause,[],[f65,f165])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f45,f60,f60])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f39,f59])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f47,f58])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f50,f57])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f51,f56])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f52,f55])).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f53,f54])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(flattening,[],[f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,axiom,(
% 0.20/0.45    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).
% 0.20/0.45  fof(f163,plain,(
% 0.20/0.45    ~spl1_20),
% 0.20/0.45    inference(avatar_split_clause,[],[f61,f160])).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 0.20/0.45    inference(definition_unfolding,[],[f34,f60,f60])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0)) => (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f21])).
% 0.20/0.45  fof(f21,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.20/0.45    inference(negated_conjecture,[],[f20])).
% 0.20/0.45  fof(f20,conjecture,(
% 0.20/0.45    ! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).
% 0.20/0.45  fof(f158,plain,(
% 0.20/0.45    spl1_19 | ~spl1_13 | ~spl1_18),
% 0.20/0.45    inference(avatar_split_clause,[],[f153,f150,f128,f155])).
% 0.20/0.45  fof(f128,plain,(
% 0.20/0.45    spl1_13 <=> ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.20/0.45  fof(f150,plain,(
% 0.20/0.45    spl1_18 <=> ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.20/0.45  fof(f153,plain,(
% 0.20/0.45    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | (~spl1_13 | ~spl1_18)),
% 0.20/0.45    inference(superposition,[],[f151,f129])).
% 0.20/0.45  fof(f129,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)) ) | ~spl1_13),
% 0.20/0.45    inference(avatar_component_clause,[],[f128])).
% 0.20/0.45  fof(f151,plain,(
% 0.20/0.45    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))) ) | ~spl1_18),
% 0.20/0.45    inference(avatar_component_clause,[],[f150])).
% 0.20/0.45  fof(f152,plain,(
% 0.20/0.45    spl1_18 | ~spl1_1 | ~spl1_17),
% 0.20/0.45    inference(avatar_split_clause,[],[f148,f145,f68,f150])).
% 0.20/0.45  fof(f145,plain,(
% 0.20/0.45    spl1_17 <=> ! [X1,X0] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.20/0.45  fof(f148,plain,(
% 0.20/0.45    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))) ) | (~spl1_1 | ~spl1_17)),
% 0.20/0.45    inference(resolution,[],[f146,f70])).
% 0.20/0.45  fof(f146,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~l1_orders_2(X1) | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))) ) | ~spl1_17),
% 0.20/0.45    inference(avatar_component_clause,[],[f145])).
% 0.20/0.45  fof(f147,plain,(
% 0.20/0.45    spl1_17),
% 0.20/0.45    inference(avatar_split_clause,[],[f66,f145])).
% 0.20/0.45  fof(f66,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f49,f46])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,axiom,(
% 0.20/0.45    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f30])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,axiom,(
% 0.20/0.45    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).
% 0.20/0.45  fof(f143,plain,(
% 0.20/0.45    spl1_15 | spl1_16 | ~spl1_13 | ~spl1_14),
% 0.20/0.45    inference(avatar_split_clause,[],[f135,f132,f128,f140,f137])).
% 0.20/0.45  fof(f132,plain,(
% 0.20/0.45    spl1_14 <=> ! [X1,X0] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.20/0.45  fof(f135,plain,(
% 0.20/0.45    ( ! [X0] : (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(X0)) ) | (~spl1_13 | ~spl1_14)),
% 0.20/0.45    inference(superposition,[],[f133,f129])).
% 0.20/0.45  fof(f133,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) ) | ~spl1_14),
% 0.20/0.45    inference(avatar_component_clause,[],[f132])).
% 0.20/0.45  fof(f134,plain,(
% 0.20/0.45    spl1_14),
% 0.20/0.45    inference(avatar_split_clause,[],[f48,f132])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,axiom,(
% 0.20/0.45    ! [X0,X1] : (l1_orders_2(X1) => v1_yellow_1(k2_funcop_1(X0,X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).
% 0.20/0.45  fof(f130,plain,(
% 0.20/0.45    spl1_13 | ~spl1_4 | ~spl1_12),
% 0.20/0.45    inference(avatar_split_clause,[],[f125,f121,f82,f128])).
% 0.20/0.45  fof(f82,plain,(
% 0.20/0.45    spl1_4 <=> ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.45  fof(f121,plain,(
% 0.20/0.45    spl1_12 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.20/0.45  fof(f125,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)) ) | (~spl1_4 | ~spl1_12)),
% 0.20/0.45    inference(resolution,[],[f122,f83])).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) ) | ~spl1_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f82])).
% 0.20/0.45  fof(f122,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl1_12),
% 0.20/0.45    inference(avatar_component_clause,[],[f121])).
% 0.20/0.45  fof(f123,plain,(
% 0.20/0.45    spl1_12),
% 0.20/0.45    inference(avatar_split_clause,[],[f44,f121])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.45  fof(f119,plain,(
% 0.20/0.45    spl1_11 | ~spl1_7 | ~spl1_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f114,f99,f94,f116])).
% 0.20/0.45  fof(f94,plain,(
% 0.20/0.45    spl1_7 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.20/0.45  fof(f99,plain,(
% 0.20/0.45    spl1_8 <=> ! [X0] : v4_relat_1(k6_partfun1(X0),X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.45  fof(f114,plain,(
% 0.20/0.45    v4_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_7 | ~spl1_8)),
% 0.20/0.45    inference(superposition,[],[f100,f96])).
% 0.20/0.45  fof(f96,plain,(
% 0.20/0.45    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl1_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f94])).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) ) | ~spl1_8),
% 0.20/0.45    inference(avatar_component_clause,[],[f99])).
% 0.20/0.45  fof(f113,plain,(
% 0.20/0.45    spl1_10 | ~spl1_5 | ~spl1_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f102,f94,f86,f110])).
% 0.20/0.45  fof(f86,plain,(
% 0.20/0.45    spl1_5 <=> ! [X0] : v1_partfun1(k6_partfun1(X0),X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.45  fof(f102,plain,(
% 0.20/0.45    v1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl1_5 | ~spl1_7)),
% 0.20/0.45    inference(superposition,[],[f87,f96])).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) ) | ~spl1_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f86])).
% 0.20/0.45  fof(f108,plain,(
% 0.20/0.45    spl1_9 | ~spl1_3 | ~spl1_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f103,f94,f78,f105])).
% 0.20/0.45  fof(f78,plain,(
% 0.20/0.45    spl1_3 <=> ! [X0] : v1_relat_1(k6_partfun1(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.45  fof(f103,plain,(
% 0.20/0.45    v1_relat_1(k1_xboole_0) | (~spl1_3 | ~spl1_7)),
% 0.20/0.45    inference(superposition,[],[f79,f96])).
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) ) | ~spl1_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f78])).
% 0.20/0.45  fof(f101,plain,(
% 0.20/0.45    spl1_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f63,f99])).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f41,f38])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,axiom,(
% 0.20/0.45    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.45  fof(f12,axiom,(
% 0.20/0.45    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.20/0.45  fof(f97,plain,(
% 0.20/0.45    spl1_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f62,f94])).
% 0.20/0.45  fof(f62,plain,(
% 0.20/0.45    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.20/0.45    inference(definition_unfolding,[],[f36,f38])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.45  fof(f92,plain,(
% 0.20/0.45    spl1_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f43,f90])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,axiom,(
% 0.20/0.45    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    spl1_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f42,f86])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0] : v1_partfun1(k6_partfun1(X0),X0)),
% 0.20/0.45    inference(pure_predicate_removal,[],[f13])).
% 0.20/0.45  fof(f13,axiom,(
% 0.20/0.45    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.20/0.45  fof(f84,plain,(
% 0.20/0.45    spl1_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f37,f82])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,axiom,(
% 0.20/0.45    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    spl1_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f64,f78])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f40,f38])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f23])).
% 0.20/0.45  fof(f76,plain,(
% 0.20/0.45    spl1_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f35,f73])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    v1_xboole_0(k1_xboole_0)),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    v1_xboole_0(k1_xboole_0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    spl1_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f33,f68])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    l1_orders_2(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f32])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (21203)------------------------------
% 0.20/0.45  % (21203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (21203)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (21203)Memory used [KB]: 6140
% 0.20/0.45  % (21203)Time elapsed: 0.040 s
% 0.20/0.45  % (21203)------------------------------
% 0.20/0.45  % (21203)------------------------------
% 0.20/0.46  % (21195)Success in time 0.1 s
%------------------------------------------------------------------------------
