%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 145 expanded)
%              Number of leaves         :   29 (  70 expanded)
%              Depth                    :    5
%              Number of atoms          :  275 ( 399 expanded)
%              Number of equality atoms :   37 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f314,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f48,f52,f56,f60,f64,f68,f72,f80,f102,f106,f139,f143,f157,f166,f233,f251,f283,f289,f311])).

fof(f311,plain,
    ( spl9_2
    | ~ spl9_15
    | ~ spl9_26
    | ~ spl9_39 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl9_2
    | ~ spl9_15
    | ~ spl9_26
    | ~ spl9_39 ),
    inference(unit_resulting_resolution,[],[f101,f44,f279,f165])).

fof(f165,plain,
    ( ! [X2,X1] :
        ( r2_hidden(sK3(X1),X1)
        | X1 = X2
        | r2_hidden(sK3(X2),X2) )
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl9_26
  <=> ! [X1,X2] :
        ( X1 = X2
        | r2_hidden(sK3(X1),X1)
        | r2_hidden(sK3(X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f279,plain,
    ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(k1_xboole_0))
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl9_39
  <=> ! [X2] : ~ r2_hidden(X2,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f44,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl9_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f101,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl9_15
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f289,plain,
    ( ~ spl9_7
    | ~ spl9_15
    | spl9_40 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl9_7
    | ~ spl9_15
    | spl9_40 ),
    inference(subsumption_resolution,[],[f286,f101])).

fof(f286,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | ~ spl9_7
    | spl9_40 ),
    inference(resolution,[],[f282,f63])).

fof(f63,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | r2_hidden(sK0(X0),X0) )
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl9_7
  <=> ! [X0] :
        ( r2_hidden(sK0(X0),X0)
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f282,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl9_40 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl9_40
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f283,plain,
    ( spl9_39
    | ~ spl9_40
    | ~ spl9_1
    | ~ spl9_3
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f266,f155,f46,f39,f281,f278])).

fof(f39,plain,
    ( spl9_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f46,plain,
    ( spl9_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f155,plain,
    ( spl9_24
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_xboole_0(k1_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f266,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(k1_xboole_0)
        | ~ r2_hidden(X2,k2_relat_1(k1_xboole_0)) )
    | ~ spl9_1
    | ~ spl9_3
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f260,f40])).

fof(f40,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f260,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ r2_hidden(X2,k2_relat_1(k1_xboole_0)) )
    | ~ spl9_3
    | ~ spl9_24 ),
    inference(superposition,[],[f156,f250])).

fof(f250,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f155])).

fof(f251,plain,
    ( spl9_3
    | ~ spl9_15
    | ~ spl9_35 ),
    inference(avatar_split_clause,[],[f238,f231,f100,f46])).

fof(f231,plain,
    ( spl9_35
  <=> ! [X5] :
        ( r2_hidden(k4_tarski(sK6(X5,k1_xboole_0),sK8(X5,k1_xboole_0)),X5)
        | k1_xboole_0 = k1_relat_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f238,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl9_15
    | ~ spl9_35 ),
    inference(resolution,[],[f232,f101])).

fof(f232,plain,
    ( ! [X5] :
        ( r2_hidden(k4_tarski(sK6(X5,k1_xboole_0),sK8(X5,k1_xboole_0)),X5)
        | k1_xboole_0 = k1_relat_1(X5) )
    | ~ spl9_35 ),
    inference(avatar_component_clause,[],[f231])).

fof(f233,plain,
    ( spl9_35
    | ~ spl9_15
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f149,f141,f100,f231])).

fof(f141,plain,
    ( spl9_23
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(sK6(X0,X1),sK8(X0,X1)),X0)
        | r2_hidden(sK6(X0,X1),X1)
        | k1_relat_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f149,plain,
    ( ! [X5] :
        ( r2_hidden(k4_tarski(sK6(X5,k1_xboole_0),sK8(X5,k1_xboole_0)),X5)
        | k1_xboole_0 = k1_relat_1(X5) )
    | ~ spl9_15
    | ~ spl9_23 ),
    inference(resolution,[],[f142,f101])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(X0,X1),X1)
        | r2_hidden(k4_tarski(sK6(X0,X1),sK8(X0,X1)),X0)
        | k1_relat_1(X0) = X1 )
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f141])).

fof(f166,plain,
    ( spl9_26
    | ~ spl9_8
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f145,f137,f66,f164])).

fof(f66,plain,
    ( spl9_8
  <=> ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f137,plain,
    ( spl9_22
  <=> ! [X1,X2] :
        ( X1 = X2
        | ~ v1_xboole_0(X2)
        | r2_hidden(sK3(X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f145,plain,
    ( ! [X2,X1] :
        ( X1 = X2
        | r2_hidden(sK3(X1),X1)
        | r2_hidden(sK3(X2),X2) )
    | ~ spl9_8
    | ~ spl9_22 ),
    inference(resolution,[],[f138,f67])).

fof(f67,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f138,plain,
    ( ! [X2,X1] :
        ( ~ v1_xboole_0(X2)
        | X1 = X2
        | r2_hidden(sK3(X1),X1) )
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f137])).

fof(f157,plain,
    ( spl9_24
    | ~ spl9_6
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f122,f104,f58,f155])).

fof(f58,plain,
    ( spl9_6
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f104,plain,
    ( spl9_16
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r2_hidden(X0,k2_relat_1(X1))
        | r2_hidden(sK5(X1),k1_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_xboole_0(k1_relat_1(X1)) )
    | ~ spl9_6
    | ~ spl9_16 ),
    inference(resolution,[],[f105,f59])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(X1),k1_relat_1(X1))
        | ~ r2_hidden(X0,k2_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f104])).

fof(f143,plain,(
    spl9_23 ),
    inference(avatar_split_clause,[],[f33,f141])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1),sK8(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f139,plain,
    ( spl9_22
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f82,f70,f66,f137])).

fof(f70,plain,
    ( spl9_9
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | X0 = X1
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f82,plain,
    ( ! [X2,X1] :
        ( X1 = X2
        | ~ v1_xboole_0(X2)
        | r2_hidden(sK3(X1),X1) )
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(resolution,[],[f71,f67])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | X0 = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f106,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f30,f104])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | r2_hidden(sK5(X1),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f102,plain,
    ( spl9_15
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f92,f78,f54,f50,f100])).

fof(f50,plain,
    ( spl9_4
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f54,plain,
    ( spl9_5
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f78,plain,
    ( spl9_11
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f92,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f91,f51])).

fof(f51,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl9_5
    | ~ spl9_11 ),
    inference(superposition,[],[f79,f55])).

fof(f55,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f79,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f28,f78])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f72,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f35,f70])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f68,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f26,f66])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f64,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f24,f62])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f60,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f27,f58])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f56,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f52,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f48,plain,
    ( ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f19,f46,f43])).

fof(f19,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f41,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:06:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (10055)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (10055)Refutation not found, incomplete strategy% (10055)------------------------------
% 0.21/0.47  % (10055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (10055)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (10055)Memory used [KB]: 10618
% 0.21/0.47  % (10055)Time elapsed: 0.049 s
% 0.21/0.47  % (10055)------------------------------
% 0.21/0.47  % (10055)------------------------------
% 0.21/0.47  % (10069)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (10069)Refutation not found, incomplete strategy% (10069)------------------------------
% 0.21/0.47  % (10069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10061)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (10069)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (10069)Memory used [KB]: 6140
% 0.21/0.48  % (10069)Time elapsed: 0.007 s
% 0.21/0.48  % (10069)------------------------------
% 0.21/0.48  % (10069)------------------------------
% 0.21/0.48  % (10063)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (10063)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f41,f48,f52,f56,f60,f64,f68,f72,f80,f102,f106,f139,f143,f157,f166,f233,f251,f283,f289,f311])).
% 0.21/0.49  fof(f311,plain,(
% 0.21/0.49    spl9_2 | ~spl9_15 | ~spl9_26 | ~spl9_39),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f302])).
% 0.21/0.49  fof(f302,plain,(
% 0.21/0.49    $false | (spl9_2 | ~spl9_15 | ~spl9_26 | ~spl9_39)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f101,f44,f279,f165])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    ( ! [X2,X1] : (r2_hidden(sK3(X1),X1) | X1 = X2 | r2_hidden(sK3(X2),X2)) ) | ~spl9_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f164])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    spl9_26 <=> ! [X1,X2] : (X1 = X2 | r2_hidden(sK3(X1),X1) | r2_hidden(sK3(X2),X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(k1_xboole_0))) ) | ~spl9_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f278])).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    spl9_39 <=> ! [X2] : ~r2_hidden(X2,k2_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl9_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    spl9_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl9_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f100])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl9_15 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    ~spl9_7 | ~spl9_15 | spl9_40),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f288])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    $false | (~spl9_7 | ~spl9_15 | spl9_40)),
% 0.21/0.49    inference(subsumption_resolution,[],[f286,f101])).
% 0.21/0.49  fof(f286,plain,(
% 0.21/0.49    r2_hidden(sK0(k1_xboole_0),k1_xboole_0) | (~spl9_7 | spl9_40)),
% 0.21/0.49    inference(resolution,[],[f282,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK0(X0),X0)) ) | ~spl9_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl9_7 <=> ! [X0] : (r2_hidden(sK0(X0),X0) | v1_relat_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    ~v1_relat_1(k1_xboole_0) | spl9_40),
% 0.21/0.49    inference(avatar_component_clause,[],[f281])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    spl9_40 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    spl9_39 | ~spl9_40 | ~spl9_1 | ~spl9_3 | ~spl9_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f266,f155,f46,f39,f281,f278])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    spl9_1 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    spl9_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    spl9_24 <=> ! [X1,X0] : (~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_xboole_0(k1_relat_1(X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    ( ! [X2] : (~v1_relat_1(k1_xboole_0) | ~r2_hidden(X2,k2_relat_1(k1_xboole_0))) ) | (~spl9_1 | ~spl9_3 | ~spl9_24)),
% 0.21/0.49    inference(subsumption_resolution,[],[f260,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0) | ~spl9_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f39])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    ( ! [X2] : (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r2_hidden(X2,k2_relat_1(k1_xboole_0))) ) | (~spl9_3 | ~spl9_24)),
% 0.21/0.49    inference(superposition,[],[f156,f250])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl9_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f46])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(k1_relat_1(X1)) | ~v1_relat_1(X1) | ~r2_hidden(X0,k2_relat_1(X1))) ) | ~spl9_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f155])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    spl9_3 | ~spl9_15 | ~spl9_35),
% 0.21/0.49    inference(avatar_split_clause,[],[f238,f231,f100,f46])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    spl9_35 <=> ! [X5] : (r2_hidden(k4_tarski(sK6(X5,k1_xboole_0),sK8(X5,k1_xboole_0)),X5) | k1_xboole_0 = k1_relat_1(X5))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl9_15 | ~spl9_35)),
% 0.21/0.49    inference(resolution,[],[f232,f101])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ( ! [X5] : (r2_hidden(k4_tarski(sK6(X5,k1_xboole_0),sK8(X5,k1_xboole_0)),X5) | k1_xboole_0 = k1_relat_1(X5)) ) | ~spl9_35),
% 0.21/0.49    inference(avatar_component_clause,[],[f231])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    spl9_35 | ~spl9_15 | ~spl9_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f149,f141,f100,f231])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    spl9_23 <=> ! [X1,X0] : (r2_hidden(k4_tarski(sK6(X0,X1),sK8(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1) | k1_relat_1(X0) = X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ( ! [X5] : (r2_hidden(k4_tarski(sK6(X5,k1_xboole_0),sK8(X5,k1_xboole_0)),X5) | k1_xboole_0 = k1_relat_1(X5)) ) | (~spl9_15 | ~spl9_23)),
% 0.21/0.49    inference(resolution,[],[f142,f101])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | r2_hidden(k4_tarski(sK6(X0,X1),sK8(X0,X1)),X0) | k1_relat_1(X0) = X1) ) | ~spl9_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f141])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    spl9_26 | ~spl9_8 | ~spl9_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f145,f137,f66,f164])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl9_8 <=> ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl9_22 <=> ! [X1,X2] : (X1 = X2 | ~v1_xboole_0(X2) | r2_hidden(sK3(X1),X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ( ! [X2,X1] : (X1 = X2 | r2_hidden(sK3(X1),X1) | r2_hidden(sK3(X2),X2)) ) | (~spl9_8 | ~spl9_22)),
% 0.21/0.49    inference(resolution,[],[f138,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) ) | ~spl9_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X2,X1] : (~v1_xboole_0(X2) | X1 = X2 | r2_hidden(sK3(X1),X1)) ) | ~spl9_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    spl9_24 | ~spl9_6 | ~spl9_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f122,f104,f58,f155])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl9_6 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl9_16 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r2_hidden(X0,k2_relat_1(X1)) | r2_hidden(sK5(X1),k1_relat_1(X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_xboole_0(k1_relat_1(X1))) ) | (~spl9_6 | ~spl9_16)),
% 0.21/0.49    inference(resolution,[],[f105,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) ) | ~spl9_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK5(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl9_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f104])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    spl9_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f141])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1),sK8(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    spl9_22 | ~spl9_8 | ~spl9_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f82,f70,f66,f137])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl9_9 <=> ! [X1,X0] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X2,X1] : (X1 = X2 | ~v1_xboole_0(X2) | r2_hidden(sK3(X1),X1)) ) | (~spl9_8 | ~spl9_9)),
% 0.21/0.49    inference(resolution,[],[f71,f67])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) ) | ~spl9_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f70])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl9_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f104])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,k2_relat_1(X1)) | r2_hidden(sK5(X1),k1_relat_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl9_15 | ~spl9_4 | ~spl9_5 | ~spl9_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f92,f78,f54,f50,f100])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl9_4 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl9_5 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl9_11 <=> ! [X1,X0,X2] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | (~spl9_4 | ~spl9_5 | ~spl9_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f91,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl9_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f50])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) ) | (~spl9_5 | ~spl9_11)),
% 0.21/0.49    inference(superposition,[],[f79,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl9_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f54])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl9_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl9_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f78])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl9_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f70])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl9_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f66])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl9_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f62])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK0(X0),X0) | v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl9_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f58])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    spl9_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f54])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl9_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f50])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ~spl9_2 | ~spl9_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f46,f43])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl9_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f39])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (10063)------------------------------
% 0.21/0.49  % (10063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10063)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (10063)Memory used [KB]: 10746
% 0.21/0.49  % (10063)Time elapsed: 0.071 s
% 0.21/0.49  % (10063)------------------------------
% 0.21/0.49  % (10063)------------------------------
% 0.21/0.49  % (10053)Success in time 0.134 s
%------------------------------------------------------------------------------
