%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0762+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:47 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 424 expanded)
%              Number of leaves         :   21 ( 111 expanded)
%              Depth                    :   17
%              Number of atoms          :  459 (1865 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1937,f1938,f2135,f2144,f2154,f2164,f2174,f2184,f2208,f2209,f2222,f2225,f2228,f2231,f2234])).

fof(f2234,plain,
    ( ~ spl73_1
    | spl73_23 ),
    inference(avatar_contradiction_clause,[],[f2233])).

fof(f2233,plain,
    ( $false
    | ~ spl73_1
    | spl73_23 ),
    inference(subsumption_resolution,[],[f2232,f1484])).

fof(f1484,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1300])).

fof(f1300,plain,
    ( ( ~ v2_wellord1(sK0)
      | ~ r2_wellord1(sK0,k3_relat_1(sK0)) )
    & ( v2_wellord1(sK0)
      | r2_wellord1(sK0,k3_relat_1(sK0)) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1298,f1299])).

fof(f1299,plain,
    ( ? [X0] :
        ( ( ~ v2_wellord1(X0)
          | ~ r2_wellord1(X0,k3_relat_1(X0)) )
        & ( v2_wellord1(X0)
          | r2_wellord1(X0,k3_relat_1(X0)) )
        & v1_relat_1(X0) )
   => ( ( ~ v2_wellord1(sK0)
        | ~ r2_wellord1(sK0,k3_relat_1(sK0)) )
      & ( v2_wellord1(sK0)
        | r2_wellord1(sK0,k3_relat_1(sK0)) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1298,plain,(
    ? [X0] :
      ( ( ~ v2_wellord1(X0)
        | ~ r2_wellord1(X0,k3_relat_1(X0)) )
      & ( v2_wellord1(X0)
        | r2_wellord1(X0,k3_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1297])).

fof(f1297,plain,(
    ? [X0] :
      ( ( ~ v2_wellord1(X0)
        | ~ r2_wellord1(X0,k3_relat_1(X0)) )
      & ( v2_wellord1(X0)
        | r2_wellord1(X0,k3_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1146])).

fof(f1146,plain,(
    ? [X0] :
      ( ( r2_wellord1(X0,k3_relat_1(X0))
      <~> v2_wellord1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1140])).

fof(f1140,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( r2_wellord1(X0,k3_relat_1(X0))
        <=> v2_wellord1(X0) ) ) ),
    inference(negated_conjecture,[],[f1139])).

fof(f1139,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord1)).

fof(f2232,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl73_1
    | spl73_23 ),
    inference(subsumption_resolution,[],[f2219,f2179])).

fof(f2179,plain,
    ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | spl73_23 ),
    inference(avatar_component_clause,[],[f2177])).

fof(f2177,plain,
    ( spl73_23
  <=> r1_wellord1(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl73_23])])).

fof(f2219,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl73_1 ),
    inference(resolution,[],[f1931,f1497])).

fof(f1497,plain,(
    ! [X0,X1] :
      ( r1_wellord1(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1304])).

fof(f1304,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1303])).

fof(f1303,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1148])).

fof(f1148,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1133])).

fof(f1133,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_wellord1)).

fof(f1931,plain,
    ( r2_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl73_1 ),
    inference(avatar_component_clause,[],[f1930])).

fof(f1930,plain,
    ( spl73_1
  <=> r2_wellord1(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl73_1])])).

fof(f2231,plain,
    ( ~ spl73_1
    | spl73_21 ),
    inference(avatar_contradiction_clause,[],[f2230])).

fof(f2230,plain,
    ( $false
    | ~ spl73_1
    | spl73_21 ),
    inference(subsumption_resolution,[],[f2229,f1484])).

fof(f2229,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl73_1
    | spl73_21 ),
    inference(subsumption_resolution,[],[f2218,f2169])).

fof(f2169,plain,
    ( ~ r6_relat_2(sK0,k3_relat_1(sK0))
    | spl73_21 ),
    inference(avatar_component_clause,[],[f2167])).

fof(f2167,plain,
    ( spl73_21
  <=> r6_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl73_21])])).

fof(f2218,plain,
    ( r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl73_1 ),
    inference(resolution,[],[f1931,f1496])).

fof(f1496,plain,(
    ! [X0,X1] :
      ( r6_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1304])).

fof(f2228,plain,
    ( ~ spl73_1
    | spl73_19 ),
    inference(avatar_contradiction_clause,[],[f2227])).

fof(f2227,plain,
    ( $false
    | ~ spl73_1
    | spl73_19 ),
    inference(subsumption_resolution,[],[f2226,f1484])).

fof(f2226,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl73_1
    | spl73_19 ),
    inference(subsumption_resolution,[],[f2217,f2159])).

fof(f2159,plain,
    ( ~ r4_relat_2(sK0,k3_relat_1(sK0))
    | spl73_19 ),
    inference(avatar_component_clause,[],[f2157])).

fof(f2157,plain,
    ( spl73_19
  <=> r4_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl73_19])])).

fof(f2217,plain,
    ( r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl73_1 ),
    inference(resolution,[],[f1931,f1495])).

fof(f1495,plain,(
    ! [X0,X1] :
      ( r4_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1304])).

fof(f2225,plain,
    ( ~ spl73_1
    | spl73_17 ),
    inference(avatar_contradiction_clause,[],[f2224])).

fof(f2224,plain,
    ( $false
    | ~ spl73_1
    | spl73_17 ),
    inference(subsumption_resolution,[],[f2223,f1484])).

fof(f2223,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl73_1
    | spl73_17 ),
    inference(subsumption_resolution,[],[f2216,f2149])).

fof(f2149,plain,
    ( ~ r8_relat_2(sK0,k3_relat_1(sK0))
    | spl73_17 ),
    inference(avatar_component_clause,[],[f2147])).

fof(f2147,plain,
    ( spl73_17
  <=> r8_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl73_17])])).

fof(f2216,plain,
    ( r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl73_1 ),
    inference(resolution,[],[f1931,f1494])).

fof(f1494,plain,(
    ! [X0,X1] :
      ( r8_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1304])).

fof(f2222,plain,
    ( ~ spl73_1
    | spl73_15 ),
    inference(avatar_contradiction_clause,[],[f2221])).

fof(f2221,plain,
    ( $false
    | ~ spl73_1
    | spl73_15 ),
    inference(subsumption_resolution,[],[f2220,f1484])).

fof(f2220,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl73_1
    | spl73_15 ),
    inference(subsumption_resolution,[],[f2215,f2139])).

fof(f2139,plain,
    ( ~ r1_relat_2(sK0,k3_relat_1(sK0))
    | spl73_15 ),
    inference(avatar_component_clause,[],[f2137])).

fof(f2137,plain,
    ( spl73_15
  <=> r1_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl73_15])])).

fof(f2215,plain,
    ( r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl73_1 ),
    inference(resolution,[],[f1931,f1493])).

fof(f1493,plain,(
    ! [X0,X1] :
      ( r1_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1304])).

fof(f2209,plain,
    ( ~ spl73_2
    | spl73_24 ),
    inference(avatar_split_clause,[],[f1943,f2181,f1934])).

fof(f1934,plain,
    ( spl73_2
  <=> v2_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl73_2])])).

fof(f2181,plain,
    ( spl73_24
  <=> v1_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl73_24])])).

fof(f1943,plain,
    ( v1_wellord1(sK0)
    | ~ v2_wellord1(sK0) ),
    inference(resolution,[],[f1484,f1491])).

fof(f1491,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1302])).

fof(f1302,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1301])).

fof(f1301,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1147])).

fof(f1147,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1132])).

fof(f1132,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f2208,plain,
    ( ~ spl73_16
    | ~ spl73_18
    | ~ spl73_20
    | ~ spl73_22
    | ~ spl73_24
    | spl73_2 ),
    inference(avatar_split_clause,[],[f1944,f1934,f2181,f2171,f2161,f2151,f2141])).

fof(f2141,plain,
    ( spl73_16
  <=> v1_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl73_16])])).

fof(f2151,plain,
    ( spl73_18
  <=> v8_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl73_18])])).

fof(f2161,plain,
    ( spl73_20
  <=> v4_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl73_20])])).

fof(f2171,plain,
    ( spl73_22
  <=> v6_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl73_22])])).

fof(f1944,plain,
    ( v2_wellord1(sK0)
    | ~ v1_wellord1(sK0)
    | ~ v6_relat_2(sK0)
    | ~ v4_relat_2(sK0)
    | ~ v8_relat_2(sK0)
    | ~ v1_relat_2(sK0) ),
    inference(resolution,[],[f1484,f1492])).

fof(f1492,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1302])).

fof(f2184,plain,
    ( ~ spl73_23
    | spl73_24 ),
    inference(avatar_split_clause,[],[f1966,f2181,f2177])).

fof(f1966,plain,
    ( v1_wellord1(sK0)
    | ~ r1_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(resolution,[],[f1484,f1514])).

fof(f1514,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ r1_wellord1(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1310])).

fof(f1310,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ~ r1_wellord1(X0,k3_relat_1(X0)) )
        & ( r1_wellord1(X0,k3_relat_1(X0))
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1157])).

fof(f1157,plain,(
    ! [X0] :
      ( ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1138])).

fof(f1138,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord1)).

fof(f2174,plain,
    ( ~ spl73_21
    | spl73_22 ),
    inference(avatar_split_clause,[],[f1968,f2171,f2167])).

fof(f1968,plain,
    ( v6_relat_2(sK0)
    | ~ r6_relat_2(sK0,k3_relat_1(sK0)) ),
    inference(resolution,[],[f1484,f1516])).

fof(f1516,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ r6_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1311])).

fof(f1311,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ~ r6_relat_2(X0,k3_relat_1(X0)) )
        & ( r6_relat_2(X0,k3_relat_1(X0))
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1158])).

fof(f1158,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1127])).

fof(f1127,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_2)).

fof(f2164,plain,
    ( ~ spl73_19
    | spl73_20 ),
    inference(avatar_split_clause,[],[f1970,f2161,f2157])).

fof(f1970,plain,
    ( v4_relat_2(sK0)
    | ~ r4_relat_2(sK0,k3_relat_1(sK0)) ),
    inference(resolution,[],[f1484,f1518])).

fof(f1518,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ r4_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1312])).

fof(f1312,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ~ r4_relat_2(X0,k3_relat_1(X0)) )
        & ( r4_relat_2(X0,k3_relat_1(X0))
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1159])).

fof(f1159,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1126])).

fof(f1126,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_2)).

fof(f2154,plain,
    ( ~ spl73_17
    | spl73_18 ),
    inference(avatar_split_clause,[],[f1972,f2151,f2147])).

fof(f1972,plain,
    ( v8_relat_2(sK0)
    | ~ r8_relat_2(sK0,k3_relat_1(sK0)) ),
    inference(resolution,[],[f1484,f1520])).

fof(f1520,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ r8_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1313])).

fof(f1313,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ~ r8_relat_2(X0,k3_relat_1(X0)) )
        & ( r8_relat_2(X0,k3_relat_1(X0))
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1160])).

fof(f1160,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1128])).

fof(f1128,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_2)).

fof(f2144,plain,
    ( ~ spl73_15
    | spl73_16 ),
    inference(avatar_split_clause,[],[f1974,f2141,f2137])).

fof(f1974,plain,
    ( v1_relat_2(sK0)
    | ~ r1_relat_2(sK0,k3_relat_1(sK0)) ),
    inference(resolution,[],[f1484,f1522])).

fof(f1522,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1314])).

fof(f1314,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ~ r1_relat_2(X0,k3_relat_1(X0)) )
        & ( r1_relat_2(X0,k3_relat_1(X0))
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1161])).

fof(f1161,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1134])).

fof(f1134,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_relat_2)).

fof(f2135,plain,
    ( spl73_1
    | ~ spl73_2 ),
    inference(avatar_contradiction_clause,[],[f2134])).

fof(f2134,plain,
    ( $false
    | spl73_1
    | ~ spl73_2 ),
    inference(subsumption_resolution,[],[f2133,f1484])).

fof(f2133,plain,
    ( ~ v1_relat_1(sK0)
    | spl73_1
    | ~ spl73_2 ),
    inference(subsumption_resolution,[],[f2132,f2063])).

fof(f2063,plain,
    ( r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl73_2 ),
    inference(subsumption_resolution,[],[f1973,f2052])).

fof(f2052,plain,
    ( v1_relat_2(sK0)
    | ~ spl73_2 ),
    inference(subsumption_resolution,[],[f1939,f1935])).

fof(f1935,plain,
    ( v2_wellord1(sK0)
    | ~ spl73_2 ),
    inference(avatar_component_clause,[],[f1934])).

fof(f1939,plain,
    ( v1_relat_2(sK0)
    | ~ v2_wellord1(sK0) ),
    inference(resolution,[],[f1484,f1487])).

fof(f1487,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1302])).

fof(f1973,plain,
    ( r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_2(sK0) ),
    inference(resolution,[],[f1484,f1521])).

fof(f1521,plain,(
    ! [X0] :
      ( r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1314])).

fof(f2132,plain,
    ( ~ r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl73_1
    | ~ spl73_2 ),
    inference(subsumption_resolution,[],[f2131,f2062])).

fof(f2062,plain,
    ( r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl73_2 ),
    inference(subsumption_resolution,[],[f1971,f2053])).

fof(f2053,plain,
    ( v8_relat_2(sK0)
    | ~ spl73_2 ),
    inference(subsumption_resolution,[],[f1940,f1935])).

fof(f1940,plain,
    ( v8_relat_2(sK0)
    | ~ v2_wellord1(sK0) ),
    inference(resolution,[],[f1484,f1488])).

fof(f1488,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1302])).

fof(f1971,plain,
    ( r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ v8_relat_2(sK0) ),
    inference(resolution,[],[f1484,f1519])).

fof(f1519,plain,(
    ! [X0] :
      ( r8_relat_2(X0,k3_relat_1(X0))
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1313])).

fof(f2131,plain,
    ( ~ r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl73_1
    | ~ spl73_2 ),
    inference(subsumption_resolution,[],[f2130,f2061])).

fof(f2061,plain,
    ( r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl73_2 ),
    inference(subsumption_resolution,[],[f1969,f2054])).

fof(f2054,plain,
    ( v4_relat_2(sK0)
    | ~ spl73_2 ),
    inference(subsumption_resolution,[],[f1941,f1935])).

fof(f1941,plain,
    ( v4_relat_2(sK0)
    | ~ v2_wellord1(sK0) ),
    inference(resolution,[],[f1484,f1489])).

fof(f1489,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1302])).

fof(f1969,plain,
    ( r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ v4_relat_2(sK0) ),
    inference(resolution,[],[f1484,f1517])).

fof(f1517,plain,(
    ! [X0] :
      ( r4_relat_2(X0,k3_relat_1(X0))
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1312])).

fof(f2130,plain,
    ( ~ r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl73_1
    | ~ spl73_2 ),
    inference(subsumption_resolution,[],[f2129,f2060])).

fof(f2060,plain,
    ( r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl73_2 ),
    inference(subsumption_resolution,[],[f1967,f2055])).

fof(f2055,plain,
    ( v6_relat_2(sK0)
    | ~ spl73_2 ),
    inference(subsumption_resolution,[],[f1942,f1935])).

fof(f1942,plain,
    ( v6_relat_2(sK0)
    | ~ v2_wellord1(sK0) ),
    inference(resolution,[],[f1484,f1490])).

fof(f1490,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1302])).

fof(f1967,plain,
    ( r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ v6_relat_2(sK0) ),
    inference(resolution,[],[f1484,f1515])).

fof(f1515,plain,(
    ! [X0] :
      ( r6_relat_2(X0,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1311])).

fof(f2129,plain,
    ( ~ r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl73_1
    | ~ spl73_2 ),
    inference(subsumption_resolution,[],[f2128,f2059])).

fof(f2059,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl73_2 ),
    inference(subsumption_resolution,[],[f1965,f2056])).

fof(f2056,plain,
    ( v1_wellord1(sK0)
    | ~ spl73_2 ),
    inference(subsumption_resolution,[],[f1943,f1935])).

fof(f1965,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_wellord1(sK0) ),
    inference(resolution,[],[f1484,f1513])).

fof(f1513,plain,(
    ! [X0] :
      ( r1_wellord1(X0,k3_relat_1(X0))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1310])).

fof(f2128,plain,
    ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl73_1 ),
    inference(resolution,[],[f1932,f1498])).

fof(f1498,plain,(
    ! [X0,X1] :
      ( r2_wellord1(X0,X1)
      | ~ r1_wellord1(X0,X1)
      | ~ r6_relat_2(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1304])).

fof(f1932,plain,
    ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
    | spl73_1 ),
    inference(avatar_component_clause,[],[f1930])).

fof(f1938,plain,
    ( spl73_1
    | spl73_2 ),
    inference(avatar_split_clause,[],[f1485,f1934,f1930])).

fof(f1485,plain,
    ( v2_wellord1(sK0)
    | r2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f1300])).

fof(f1937,plain,
    ( ~ spl73_1
    | ~ spl73_2 ),
    inference(avatar_split_clause,[],[f1486,f1934,f1930])).

fof(f1486,plain,
    ( ~ v2_wellord1(sK0)
    | ~ r2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f1300])).
%------------------------------------------------------------------------------
