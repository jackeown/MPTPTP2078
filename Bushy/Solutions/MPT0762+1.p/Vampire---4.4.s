%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t8_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:16 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 647 expanded)
%              Number of leaves         :   34 ( 227 expanded)
%              Depth                    :    9
%              Number of atoms          :  767 (2636 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f270,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f84,f85,f93,f105,f112,f119,f134,f141,f149,f150,f154,f161,f168,f175,f182,f187,f199,f201,f203,f205,f207,f209,f211,f213,f225,f227,f229,f231,f234,f236,f243,f246,f253,f256,f264,f267,f269])).

fof(f269,plain,
    ( ~ spl1_0
    | spl1_5
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_12
    | ~ spl1_14
    | ~ spl1_16 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_5
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_12
    | ~ spl1_14
    | ~ spl1_16 ),
    inference(subsumption_resolution,[],[f148,f257])).

fof(f257,plain,
    ( ~ v8_relat_2(sK0)
    | ~ spl1_0
    | ~ spl1_5
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_12
    | ~ spl1_14 ),
    inference(unit_resulting_resolution,[],[f70,f133,f80,f111,f104,f118,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t8_wellord1.p',d4_wellord1)).

fof(f118,plain,
    ( v4_relat_2(sK0)
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl1_12
  <=> v4_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f104,plain,
    ( v1_wellord1(sK0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl1_8
  <=> v1_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f111,plain,
    ( v6_relat_2(sK0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl1_10
  <=> v6_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f80,plain,
    ( ~ v2_wellord1(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl1_5
  <=> ~ v2_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f133,plain,
    ( v1_relat_2(sK0)
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl1_14
  <=> v1_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f70,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_0 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl1_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_0])])).

fof(f148,plain,
    ( v8_relat_2(sK0)
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl1_16
  <=> v8_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f267,plain,
    ( ~ spl1_0
    | ~ spl1_2
    | spl1_17 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_17 ),
    inference(subsumption_resolution,[],[f265,f70])).

fof(f265,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_17 ),
    inference(subsumption_resolution,[],[f261,f222])).

fof(f222,plain,
    ( r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f70,f77,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r8_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t8_wellord1.p',d5_wellord1)).

fof(f77,plain,
    ( r2_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl1_2
  <=> r2_wellord1(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f261,plain,
    ( ~ r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_17 ),
    inference(resolution,[],[f145,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ r8_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ~ r8_relat_2(X0,k3_relat_1(X0)) )
        & ( r8_relat_2(X0,k3_relat_1(X0))
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t8_wellord1.p',d16_relat_2)).

fof(f145,plain,
    ( ~ v8_relat_2(sK0)
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl1_17
  <=> ~ v8_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f264,plain,
    ( ~ spl1_0
    | ~ spl1_2
    | spl1_17 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_17 ),
    inference(subsumption_resolution,[],[f259,f222])).

fof(f259,plain,
    ( ~ r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_17 ),
    inference(unit_resulting_resolution,[],[f70,f145,f48])).

fof(f256,plain,
    ( ~ spl1_0
    | ~ spl1_2
    | spl1_13 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_13 ),
    inference(subsumption_resolution,[],[f254,f70])).

fof(f254,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_13 ),
    inference(subsumption_resolution,[],[f250,f221])).

fof(f221,plain,
    ( r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f70,f77,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r4_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f250,plain,
    ( ~ r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_13 ),
    inference(resolution,[],[f115,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ r4_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ~ r4_relat_2(X0,k3_relat_1(X0)) )
        & ( r4_relat_2(X0,k3_relat_1(X0))
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t8_wellord1.p',d12_relat_2)).

fof(f115,plain,
    ( ~ v4_relat_2(sK0)
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl1_13
  <=> ~ v4_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f253,plain,
    ( ~ spl1_0
    | ~ spl1_2
    | spl1_13 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_13 ),
    inference(subsumption_resolution,[],[f248,f221])).

fof(f248,plain,
    ( ~ r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_13 ),
    inference(unit_resulting_resolution,[],[f70,f115,f44])).

fof(f246,plain,
    ( ~ spl1_0
    | ~ spl1_2
    | spl1_11 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f244,f70])).

fof(f244,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f240,f220])).

fof(f220,plain,
    ( r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f70,f77,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r6_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f240,plain,
    ( ~ r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_11 ),
    inference(resolution,[],[f108,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ r6_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ~ r6_relat_2(X0,k3_relat_1(X0)) )
        & ( r6_relat_2(X0,k3_relat_1(X0))
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t8_wellord1.p',d14_relat_2)).

fof(f108,plain,
    ( ~ v6_relat_2(sK0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl1_11
  <=> ~ v6_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f243,plain,
    ( ~ spl1_0
    | ~ spl1_2
    | spl1_11 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f238,f220])).

fof(f238,plain,
    ( ~ r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_11 ),
    inference(unit_resulting_resolution,[],[f70,f108,f46])).

fof(f236,plain,
    ( ~ spl1_0
    | ~ spl1_2
    | spl1_9 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f215,f219])).

fof(f219,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f70,f77,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_wellord1(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f215,plain,
    ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_9 ),
    inference(unit_resulting_resolution,[],[f70,f101,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ r1_wellord1(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ~ r1_wellord1(X0,k3_relat_1(X0)) )
        & ( r1_wellord1(X0,k3_relat_1(X0))
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t8_wellord1.p',t5_wellord1)).

fof(f101,plain,
    ( ~ v1_wellord1(sK0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl1_9
  <=> ~ v1_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f234,plain,
    ( ~ spl1_0
    | ~ spl1_2
    | spl1_9 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f232,f70])).

fof(f232,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f217,f219])).

fof(f217,plain,
    ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_9 ),
    inference(resolution,[],[f101,f42])).

fof(f231,plain,
    ( ~ spl1_0
    | ~ spl1_2
    | spl1_19 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_19 ),
    inference(subsumption_resolution,[],[f219,f157])).

fof(f157,plain,
    ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl1_19 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl1_19
  <=> ~ r1_wellord1(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f229,plain,
    ( ~ spl1_0
    | ~ spl1_2
    | spl1_21 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_21 ),
    inference(subsumption_resolution,[],[f220,f164])).

fof(f164,plain,
    ( ~ r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_21 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl1_21
  <=> ~ r6_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).

fof(f227,plain,
    ( ~ spl1_0
    | ~ spl1_2
    | spl1_23 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_23 ),
    inference(subsumption_resolution,[],[f221,f171])).

fof(f171,plain,
    ( ~ r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_23 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl1_23
  <=> ~ r4_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).

fof(f225,plain,
    ( ~ spl1_0
    | ~ spl1_2
    | spl1_25 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_25 ),
    inference(subsumption_resolution,[],[f222,f178])).

fof(f178,plain,
    ( ~ r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_25 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl1_25
  <=> ~ r8_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_25])])).

fof(f213,plain,
    ( ~ spl1_0
    | spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(subsumption_resolution,[],[f190,f70])).

fof(f190,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(unit_resulting_resolution,[],[f74,f92,f181,f174,f167,f160,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_wellord1(X0,X1)
      | ~ r6_relat_2(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ r1_relat_2(X0,X1)
      | r2_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f160,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl1_18
  <=> r1_wellord1(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f167,plain,
    ( r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_20 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl1_20
  <=> r6_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f174,plain,
    ( r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_22 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl1_22
  <=> r4_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f181,plain,
    ( r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_24 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl1_24
  <=> r8_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).

fof(f92,plain,
    ( r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl1_6
  <=> r1_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f74,plain,
    ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl1_3
  <=> ~ r2_wellord1(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f211,plain,
    ( ~ spl1_0
    | spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(subsumption_resolution,[],[f191,f160])).

fof(f191,plain,
    ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(unit_resulting_resolution,[],[f74,f92,f181,f174,f167,f70,f62])).

fof(f209,plain,
    ( ~ spl1_0
    | spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(subsumption_resolution,[],[f192,f167])).

fof(f192,plain,
    ( ~ r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(unit_resulting_resolution,[],[f74,f92,f181,f174,f160,f70,f62])).

fof(f207,plain,
    ( ~ spl1_0
    | spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(subsumption_resolution,[],[f193,f174])).

fof(f193,plain,
    ( ~ r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_24 ),
    inference(unit_resulting_resolution,[],[f74,f92,f181,f167,f160,f70,f62])).

fof(f205,plain,
    ( ~ spl1_0
    | spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(subsumption_resolution,[],[f194,f181])).

fof(f194,plain,
    ( ~ r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22 ),
    inference(unit_resulting_resolution,[],[f74,f92,f174,f167,f160,f70,f62])).

fof(f203,plain,
    ( ~ spl1_0
    | spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(subsumption_resolution,[],[f195,f92])).

fof(f195,plain,
    ( ~ r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_3
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(unit_resulting_resolution,[],[f74,f181,f174,f167,f160,f70,f62])).

fof(f201,plain,
    ( ~ spl1_0
    | spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(subsumption_resolution,[],[f196,f74])).

fof(f196,plain,
    ( r2_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(unit_resulting_resolution,[],[f92,f181,f174,f167,f160,f70,f62])).

fof(f199,plain,
    ( ~ spl1_0
    | spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_20
    | ~ spl1_22
    | ~ spl1_24 ),
    inference(unit_resulting_resolution,[],[f74,f92,f181,f174,f167,f160,f70,f62])).

fof(f187,plain,
    ( spl1_6
    | ~ spl1_0
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f152,f132,f69,f91])).

fof(f152,plain,
    ( r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_14 ),
    inference(unit_resulting_resolution,[],[f70,f133,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ~ r1_relat_2(X0,k3_relat_1(X0)) )
        & ( r1_relat_2(X0,k3_relat_1(X0))
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t8_wellord1.p',d9_relat_2)).

fof(f182,plain,
    ( spl1_24
    | ~ spl1_0
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f151,f147,f69,f180])).

fof(f151,plain,
    ( r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_16 ),
    inference(unit_resulting_resolution,[],[f70,f148,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r8_relat_2(X0,k3_relat_1(X0))
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f175,plain,
    ( spl1_22
    | ~ spl1_0
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f142,f117,f69,f173])).

fof(f142,plain,
    ( r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_12 ),
    inference(unit_resulting_resolution,[],[f70,f118,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r4_relat_2(X0,k3_relat_1(X0))
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f168,plain,
    ( spl1_20
    | ~ spl1_0
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f122,f110,f69,f166])).

fof(f122,plain,
    ( r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_10 ),
    inference(unit_resulting_resolution,[],[f70,f111,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r6_relat_2(X0,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f161,plain,
    ( spl1_18
    | ~ spl1_0
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f120,f103,f69,f159])).

fof(f120,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_8 ),
    inference(unit_resulting_resolution,[],[f70,f104,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r1_wellord1(X0,k3_relat_1(X0))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f154,plain,
    ( ~ spl1_0
    | spl1_7
    | ~ spl1_14 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_7
    | ~ spl1_14 ),
    inference(subsumption_resolution,[],[f152,f89])).

fof(f89,plain,
    ( ~ r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl1_7
  <=> ~ r1_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f150,plain,
    ( spl1_14
    | ~ spl1_0
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f139,f82,f69,f132])).

fof(f82,plain,
    ( spl1_4
  <=> v2_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f139,plain,
    ( v1_relat_2(sK0)
    | ~ spl1_0
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f70,f83,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,
    ( v2_wellord1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f149,plain,
    ( spl1_16
    | ~ spl1_0
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f138,f82,f69,f147])).

fof(f138,plain,
    ( v8_relat_2(sK0)
    | ~ spl1_0
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f70,f83,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f141,plain,
    ( ~ spl1_0
    | ~ spl1_4
    | spl1_15 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_4
    | ~ spl1_15 ),
    inference(subsumption_resolution,[],[f139,f130])).

fof(f130,plain,
    ( ~ v1_relat_2(sK0)
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl1_15
  <=> ~ v1_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f134,plain,
    ( spl1_14
    | ~ spl1_0
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f127,f91,f69,f132])).

fof(f127,plain,
    ( v1_relat_2(sK0)
    | ~ spl1_0
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f70,f92,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f119,plain,
    ( spl1_12
    | ~ spl1_0
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f96,f82,f69,f117])).

fof(f96,plain,
    ( v4_relat_2(sK0)
    | ~ spl1_0
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f70,f83,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f112,plain,
    ( spl1_10
    | ~ spl1_0
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f95,f82,f69,f110])).

fof(f95,plain,
    ( v6_relat_2(sK0)
    | ~ spl1_0
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f70,f83,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f105,plain,
    ( spl1_8
    | ~ spl1_0
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f94,f82,f69,f103])).

fof(f94,plain,
    ( v1_wellord1(sK0)
    | ~ spl1_0
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f70,f83,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,
    ( spl1_6
    | ~ spl1_0
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f86,f76,f69,f91])).

fof(f86,plain,
    ( r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f70,f77,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,
    ( ~ spl1_3
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f40,f79,f73])).

fof(f40,plain,
    ( ~ v2_wellord1(sK0)
    | ~ r2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ v2_wellord1(sK0)
      | ~ r2_wellord1(sK0,k3_relat_1(sK0)) )
    & ( v2_wellord1(sK0)
      | r2_wellord1(sK0,k3_relat_1(sK0)) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f27,plain,
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

fof(f26,plain,(
    ? [X0] :
      ( ( ~ v2_wellord1(X0)
        | ~ r2_wellord1(X0,k3_relat_1(X0)) )
      & ( v2_wellord1(X0)
        | r2_wellord1(X0,k3_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ( ~ v2_wellord1(X0)
        | ~ r2_wellord1(X0,k3_relat_1(X0)) )
      & ( v2_wellord1(X0)
        | r2_wellord1(X0,k3_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ( r2_wellord1(X0,k3_relat_1(X0))
      <~> v2_wellord1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( r2_wellord1(X0,k3_relat_1(X0))
        <=> v2_wellord1(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t8_wellord1.p',t8_wellord1)).

fof(f84,plain,
    ( spl1_2
    | spl1_4 ),
    inference(avatar_split_clause,[],[f39,f82,f76])).

fof(f39,plain,
    ( v2_wellord1(sK0)
    | r2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    spl1_0 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
