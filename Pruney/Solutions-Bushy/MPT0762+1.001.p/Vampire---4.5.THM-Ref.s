%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0762+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 476 expanded)
%              Number of leaves         :   22 ( 213 expanded)
%              Depth                    :    8
%              Number of atoms          :  520 (1713 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f65,f70,f80,f85,f90,f95,f100,f110,f115,f120,f125,f130,f132,f134,f136,f138,f141,f143,f146,f149,f151,f154,f157,f160,f166,f167,f168,f169,f171,f173,f175,f178,f184])).

fof(f184,plain,
    ( ~ spl1_8
    | spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f183,f92,f87,f82,f77,f67,f57,f97])).

fof(f97,plain,
    ( spl1_8
  <=> r1_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f57,plain,
    ( spl1_1
  <=> r2_wellord1(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f67,plain,
    ( spl1_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f77,plain,
    ( spl1_4
  <=> r1_wellord1(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f82,plain,
    ( spl1_5
  <=> r6_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f87,plain,
    ( spl1_6
  <=> r4_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f92,plain,
    ( spl1_7
  <=> r8_relat_2(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f183,plain,
    ( ~ r1_relat_2(sK0,k3_relat_1(sK0))
    | spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(unit_resulting_resolution,[],[f69,f59,f89,f84,f79,f94,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_wellord1(X0,X1)
      | ~ r1_wellord1(X0,X1)
      | ~ r6_relat_2(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_wellord1)).

fof(f94,plain,
    ( r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f79,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f84,plain,
    ( r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f89,plain,
    ( r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f59,plain,
    ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f69,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f178,plain,
    ( spl1_8
    | ~ spl1_3
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f177,f127,f67,f97])).

fof(f127,plain,
    ( spl1_13
  <=> v1_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f177,plain,
    ( r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_3
    | ~ spl1_13 ),
    inference(unit_resulting_resolution,[],[f69,f129,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ~ r1_relat_2(X0,k3_relat_1(X0)) )
        & ( r1_relat_2(X0,k3_relat_1(X0))
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_relat_2)).

fof(f129,plain,
    ( v1_relat_2(sK0)
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f175,plain,
    ( spl1_7
    | ~ spl1_3
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f174,f122,f67,f92])).

fof(f122,plain,
    ( spl1_12
  <=> v8_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f174,plain,
    ( r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_3
    | ~ spl1_12 ),
    inference(unit_resulting_resolution,[],[f69,f124,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r8_relat_2(X0,k3_relat_1(X0))
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ~ r8_relat_2(X0,k3_relat_1(X0)) )
        & ( r8_relat_2(X0,k3_relat_1(X0))
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_2)).

fof(f124,plain,
    ( v8_relat_2(sK0)
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f122])).

fof(f173,plain,
    ( spl1_6
    | ~ spl1_3
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f172,f117,f67,f87])).

fof(f117,plain,
    ( spl1_11
  <=> v4_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f172,plain,
    ( r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_3
    | ~ spl1_11 ),
    inference(unit_resulting_resolution,[],[f69,f119,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r4_relat_2(X0,k3_relat_1(X0))
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ~ r4_relat_2(X0,k3_relat_1(X0)) )
        & ( r4_relat_2(X0,k3_relat_1(X0))
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_2)).

fof(f119,plain,
    ( v4_relat_2(sK0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f171,plain,
    ( spl1_5
    | ~ spl1_3
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f170,f112,f67,f82])).

fof(f112,plain,
    ( spl1_10
  <=> v6_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f170,plain,
    ( r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_3
    | ~ spl1_10 ),
    inference(unit_resulting_resolution,[],[f69,f114,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r6_relat_2(X0,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ~ r6_relat_2(X0,k3_relat_1(X0)) )
        & ( r6_relat_2(X0,k3_relat_1(X0))
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_2)).

fof(f114,plain,
    ( v6_relat_2(sK0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f169,plain,
    ( spl1_13
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f161,f67,f61,f127])).

fof(f61,plain,
    ( spl1_2
  <=> v2_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f161,plain,
    ( v1_relat_2(sK0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f69,f62,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(f62,plain,
    ( v2_wellord1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f168,plain,
    ( spl1_12
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f162,f67,f61,f122])).

fof(f162,plain,
    ( v8_relat_2(sK0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f69,f62,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f167,plain,
    ( spl1_11
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f163,f67,f61,f117])).

fof(f163,plain,
    ( v4_relat_2(sK0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f69,f62,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f166,plain,
    ( spl1_10
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f164,f67,f61,f112])).

fof(f164,plain,
    ( v6_relat_2(sK0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f69,f62,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f160,plain,
    ( ~ spl1_5
    | ~ spl1_3
    | spl1_10 ),
    inference(avatar_split_clause,[],[f159,f112,f67,f82])).

fof(f159,plain,
    ( ~ r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_3
    | spl1_10 ),
    inference(unit_resulting_resolution,[],[f69,f113,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ r6_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f113,plain,
    ( ~ v6_relat_2(sK0)
    | spl1_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f157,plain,
    ( ~ spl1_6
    | ~ spl1_3
    | spl1_11 ),
    inference(avatar_split_clause,[],[f156,f117,f67,f87])).

fof(f156,plain,
    ( ~ r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_3
    | spl1_11 ),
    inference(unit_resulting_resolution,[],[f69,f118,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ r4_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f118,plain,
    ( ~ v4_relat_2(sK0)
    | spl1_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f154,plain,
    ( ~ spl1_7
    | ~ spl1_3
    | spl1_12 ),
    inference(avatar_split_clause,[],[f153,f122,f67,f92])).

fof(f153,plain,
    ( ~ r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_3
    | spl1_12 ),
    inference(unit_resulting_resolution,[],[f69,f123,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ r8_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f123,plain,
    ( ~ v8_relat_2(sK0)
    | spl1_12 ),
    inference(avatar_component_clause,[],[f122])).

fof(f151,plain,
    ( spl1_4
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f150,f107,f67,f77])).

fof(f107,plain,
    ( spl1_9
  <=> v1_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f150,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(unit_resulting_resolution,[],[f69,f109,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r1_wellord1(X0,k3_relat_1(X0))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ~ r1_wellord1(X0,k3_relat_1(X0)) )
        & ( r1_wellord1(X0,k3_relat_1(X0))
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord1)).

fof(f109,plain,
    ( v1_wellord1(sK0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f149,plain,
    ( ~ spl1_4
    | ~ spl1_3
    | spl1_9 ),
    inference(avatar_split_clause,[],[f148,f107,f67,f77])).

fof(f148,plain,
    ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl1_3
    | spl1_9 ),
    inference(unit_resulting_resolution,[],[f69,f108,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ r1_wellord1(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f108,plain,
    ( ~ v1_wellord1(sK0)
    | spl1_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f146,plain,
    ( ~ spl1_8
    | ~ spl1_3
    | spl1_13 ),
    inference(avatar_split_clause,[],[f145,f127,f67,f97])).

fof(f145,plain,
    ( ~ r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_3
    | spl1_13 ),
    inference(unit_resulting_resolution,[],[f69,f128,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f128,plain,
    ( ~ v1_relat_2(sK0)
    | spl1_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f143,plain,
    ( ~ spl1_13
    | spl1_2
    | ~ spl1_3
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f142,f122,f117,f112,f107,f67,f61,f127])).

fof(f142,plain,
    ( ~ v1_relat_2(sK0)
    | spl1_2
    | ~ spl1_3
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(unit_resulting_resolution,[],[f69,f124,f119,f114,f109,f63,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,
    ( ~ v2_wellord1(sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f141,plain,
    ( spl1_8
    | ~ spl1_3
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f140,f127,f67,f97])).

fof(f140,plain,
    ( r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_3
    | ~ spl1_13 ),
    inference(unit_resulting_resolution,[],[f69,f129,f42])).

fof(f138,plain,
    ( spl1_7
    | ~ spl1_3
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f137,f122,f67,f92])).

fof(f137,plain,
    ( r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_3
    | ~ spl1_12 ),
    inference(unit_resulting_resolution,[],[f69,f124,f38])).

fof(f136,plain,
    ( spl1_6
    | ~ spl1_3
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f135,f117,f67,f87])).

fof(f135,plain,
    ( r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_3
    | ~ spl1_11 ),
    inference(unit_resulting_resolution,[],[f69,f119,f34])).

fof(f134,plain,
    ( spl1_5
    | ~ spl1_3
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f133,f112,f67,f82])).

fof(f133,plain,
    ( r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_3
    | ~ spl1_10 ),
    inference(unit_resulting_resolution,[],[f69,f114,f36])).

fof(f132,plain,
    ( spl1_4
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f131,f107,f67,f77])).

fof(f131,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(unit_resulting_resolution,[],[f69,f109,f40])).

fof(f130,plain,
    ( spl1_13
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f101,f67,f61,f127])).

fof(f101,plain,
    ( v1_relat_2(sK0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f69,f62,f44])).

fof(f125,plain,
    ( spl1_12
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f102,f67,f61,f122])).

fof(f102,plain,
    ( v8_relat_2(sK0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f69,f62,f45])).

fof(f120,plain,
    ( spl1_11
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f103,f67,f61,f117])).

fof(f103,plain,
    ( v4_relat_2(sK0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f69,f62,f46])).

fof(f115,plain,
    ( spl1_10
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f104,f67,f61,f112])).

fof(f104,plain,
    ( v6_relat_2(sK0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f69,f62,f47])).

fof(f110,plain,
    ( spl1_9
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f105,f67,f61,f107])).

fof(f105,plain,
    ( v1_wellord1(sK0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f69,f62,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,
    ( spl1_8
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f71,f67,f57,f97])).

fof(f71,plain,
    ( r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f69,f58,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,
    ( r2_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f95,plain,
    ( spl1_7
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f72,f67,f57,f92])).

fof(f72,plain,
    ( r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f69,f58,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r8_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f90,plain,
    ( spl1_6
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f73,f67,f57,f87])).

fof(f73,plain,
    ( r4_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f69,f58,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r4_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,
    ( spl1_5
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f74,f67,f57,f82])).

fof(f74,plain,
    ( r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f69,f58,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r6_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

% (1355)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
fof(f80,plain,
    ( spl1_4
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f75,f67,f57,f77])).

fof(f75,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f69,f58,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_wellord1(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f31,f67])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ v2_wellord1(sK0)
      | ~ r2_wellord1(sK0,k3_relat_1(sK0)) )
    & ( v2_wellord1(sK0)
      | r2_wellord1(sK0,k3_relat_1(sK0)) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f20,plain,
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

fof(f19,plain,(
    ? [X0] :
      ( ( ~ v2_wellord1(X0)
        | ~ r2_wellord1(X0,k3_relat_1(X0)) )
      & ( v2_wellord1(X0)
        | r2_wellord1(X0,k3_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ( ~ v2_wellord1(X0)
        | ~ r2_wellord1(X0,k3_relat_1(X0)) )
      & ( v2_wellord1(X0)
        | r2_wellord1(X0,k3_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( r2_wellord1(X0,k3_relat_1(X0))
      <~> v2_wellord1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( r2_wellord1(X0,k3_relat_1(X0))
        <=> v2_wellord1(X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord1)).

fof(f65,plain,
    ( spl1_1
    | spl1_2 ),
    inference(avatar_split_clause,[],[f32,f61,f57])).

fof(f32,plain,
    ( v2_wellord1(sK0)
    | r2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f33,f61,f57])).

fof(f33,plain,
    ( ~ v2_wellord1(sK0)
    | ~ r2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
