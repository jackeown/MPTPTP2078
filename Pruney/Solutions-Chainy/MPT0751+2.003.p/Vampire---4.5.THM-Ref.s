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
% DateTime   : Thu Dec  3 12:55:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 240 expanded)
%              Number of leaves         :   28 ( 104 expanded)
%              Depth                    :   11
%              Number of atoms          :  392 ( 847 expanded)
%              Number of equality atoms :   40 ( 108 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f136,f142,f147,f334,f398,f436,f459,f460,f461,f516,f545,f615,f1122,f1167,f1218])).

fof(f1218,plain,
    ( ~ spl9_96
    | ~ spl9_5
    | ~ spl9_19
    | spl9_90 ),
    inference(avatar_split_clause,[],[f1213,f1119,f316,f144,f1162])).

fof(f1162,plain,
    ( spl9_96
  <=> r2_hidden(sK0,k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).

fof(f144,plain,
    ( spl9_5
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f316,plain,
    ( spl9_19
  <=> v3_ordinal1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f1119,plain,
    ( spl9_90
  <=> r1_ordinal1(sK0,sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).

fof(f1213,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))
    | ~ spl9_5
    | ~ spl9_19
    | spl9_90 ),
    inference(unit_resulting_resolution,[],[f146,f318,f1121,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f81,f73])).

fof(f73,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f1121,plain,
    ( ~ r1_ordinal1(sK0,sK2(sK0))
    | spl9_90 ),
    inference(avatar_component_clause,[],[f1119])).

fof(f318,plain,
    ( v3_ordinal1(sK2(sK0))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f316])).

fof(f146,plain,
    ( v3_ordinal1(sK0)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f1167,plain,
    ( ~ spl9_30
    | spl9_96
    | spl9_32
    | ~ spl9_5
    | spl9_17 ),
    inference(avatar_split_clause,[],[f1166,f306,f144,f539,f1162,f513])).

fof(f513,plain,
    ( spl9_30
  <=> v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f539,plain,
    ( spl9_32
  <=> sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f306,plain,
    ( spl9_17
  <=> r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f1166,plain,
    ( sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))
    | r2_hidden(sK0,k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))
    | ~ v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))
    | ~ spl9_5
    | spl9_17 ),
    inference(subsumption_resolution,[],[f1143,f146])).

fof(f1143,plain,
    ( sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))
    | r2_hidden(sK0,k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))
    | ~ v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))
    | ~ v3_ordinal1(sK0)
    | spl9_17 ),
    inference(resolution,[],[f308,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f308,plain,
    ( ~ r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0)
    | spl9_17 ),
    inference(avatar_component_clause,[],[f306])).

fof(f1122,plain,
    ( ~ spl9_90
    | ~ spl9_5
    | ~ spl9_19
    | spl9_39 ),
    inference(avatar_split_clause,[],[f1114,f606,f316,f144,f1119])).

fof(f606,plain,
    ( spl9_39
  <=> r1_tarski(sK0,sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f1114,plain,
    ( ~ r1_ordinal1(sK0,sK2(sK0))
    | ~ spl9_5
    | ~ spl9_19
    | spl9_39 ),
    inference(unit_resulting_resolution,[],[f146,f318,f608,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f608,plain,
    ( ~ r1_tarski(sK0,sK2(sK0))
    | spl9_39 ),
    inference(avatar_component_clause,[],[f606])).

fof(f615,plain,
    ( ~ spl9_39
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f585,f311,f606])).

fof(f311,plain,
    ( spl9_18
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f585,plain,
    ( ~ r1_tarski(sK0,sK2(sK0))
    | ~ spl9_18 ),
    inference(resolution,[],[f313,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f313,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f311])).

fof(f545,plain,
    ( ~ spl9_32
    | ~ spl9_1
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f536,f316,f124,f539])).

fof(f124,plain,
    ( spl9_1
  <=> ! [X2] :
        ( sK0 != k2_xboole_0(X2,k1_tarski(X2))
        | ~ v3_ordinal1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f536,plain,
    ( sK0 != k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))
    | ~ spl9_1
    | ~ spl9_19 ),
    inference(resolution,[],[f125,f318])).

fof(f125,plain,
    ( ! [X2] :
        ( ~ v3_ordinal1(X2)
        | sK0 != k2_xboole_0(X2,k1_tarski(X2)) )
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f516,plain,
    ( spl9_30
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f467,f316,f513])).

fof(f467,plain,
    ( v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))
    | ~ spl9_19 ),
    inference(unit_resulting_resolution,[],[f318,f111])).

fof(f111,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f74,f73])).

fof(f74,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f461,plain,
    ( spl9_19
    | spl9_2
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f453,f144,f127,f316])).

fof(f127,plain,
    ( spl9_2
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f453,plain,
    ( v3_ordinal1(sK2(sK0))
    | spl9_2
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f146,f128,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | v3_ordinal1(sK2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
            & r2_hidden(sK2(X0),X0)
            & v3_ordinal1(sK2(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
        & r2_hidden(sK2(X0),X0)
        & v3_ordinal1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X1] :
              ( r2_hidden(k1_ordinal1(X1),X0)
              | ~ r2_hidden(X1,X0)
              | ~ v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f128,plain,
    ( ~ v4_ordinal1(sK0)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f460,plain,
    ( spl9_18
    | spl9_2
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f454,f144,f127,f311])).

fof(f454,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | spl9_2
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f146,f128,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | r2_hidden(sK2(X0),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f459,plain,
    ( ~ spl9_17
    | spl9_2
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f455,f144,f127,f306])).

fof(f455,plain,
    ( ~ r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0)
    | spl9_2
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f146,f128,f112])).

fof(f112,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k2_xboole_0(sK2(X0),k1_tarski(sK2(X0))),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f78,f73])).

fof(f78,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f436,plain,(
    ~ spl9_22 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f427,f119])).

fof(f119,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f427,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl9_22 ),
    inference(resolution,[],[f397,f105])).

fof(f397,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl9_22
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f398,plain,
    ( spl9_22
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f393,f290,f144,f138,f132,f127,f395])).

fof(f132,plain,
    ( spl9_3
  <=> sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f138,plain,
    ( spl9_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f290,plain,
    ( spl9_16
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f393,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f369,f134])).

fof(f134,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f369,plain,
    ( r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_16 ),
    inference(unit_resulting_resolution,[],[f146,f129,f140,f292,f113])).

fof(f113,plain,(
    ! [X2,X0] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f75,f73])).

fof(f75,plain,(
    ! [X2,X0] :
      ( r2_hidden(k1_ordinal1(X2),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f292,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f290])).

fof(f140,plain,
    ( v3_ordinal1(sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f138])).

fof(f129,plain,
    ( v4_ordinal1(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f334,plain,
    ( spl9_16
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f327,f132,f290])).

fof(f327,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl9_3 ),
    inference(superposition,[],[f110,f134])).

fof(f110,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f72,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f147,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f65,f144])).

fof(f65,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ( v4_ordinal1(sK0)
        & sK0 = k1_ordinal1(sK1)
        & v3_ordinal1(sK1) )
      | ( ! [X2] :
            ( k1_ordinal1(X2) != sK0
            | ~ v3_ordinal1(X2) )
        & ~ v4_ordinal1(sK0) ) )
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ( ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
          | ( ! [X2] :
                ( k1_ordinal1(X2) != X0
                | ~ v3_ordinal1(X2) )
            & ~ v4_ordinal1(X0) ) )
        & v3_ordinal1(X0) )
   => ( ( ( v4_ordinal1(sK0)
          & ? [X1] :
              ( k1_ordinal1(X1) = sK0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != sK0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(sK0) ) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( k1_ordinal1(X1) = sK0
        & v3_ordinal1(X1) )
   => ( sK0 = k1_ordinal1(sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ( ( v4_ordinal1(X0)
          & ? [X1] :
              ( k1_ordinal1(X1) = X0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != X0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(X0) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X2] :
                  ( v3_ordinal1(X2)
                 => k1_ordinal1(X2) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X1] :
                  ( v3_ordinal1(X1)
                 => k1_ordinal1(X1) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( ~ ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
        & ~ ( ! [X1] :
                ( v3_ordinal1(X1)
               => k1_ordinal1(X1) != X0 )
            & ~ v4_ordinal1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_ordinal1)).

fof(f142,plain,
    ( ~ spl9_2
    | spl9_4 ),
    inference(avatar_split_clause,[],[f66,f138,f127])).

fof(f66,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f136,plain,
    ( ~ spl9_2
    | spl9_3 ),
    inference(avatar_split_clause,[],[f108,f132,f127])).

fof(f108,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | ~ v4_ordinal1(sK0) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f68,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f130,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f106,f127,f124])).

fof(f106,plain,(
    ! [X2] :
      ( v4_ordinal1(sK0)
      | sK0 != k2_xboole_0(X2,k1_tarski(X2))
      | ~ v3_ordinal1(X2) ) ),
    inference(definition_unfolding,[],[f71,f73])).

fof(f71,plain,(
    ! [X2] :
      ( v4_ordinal1(sK0)
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (23142)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.48  % (23142)Refutation not found, incomplete strategy% (23142)------------------------------
% 0.20/0.48  % (23142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23142)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (23142)Memory used [KB]: 10746
% 0.20/0.49  % (23142)Time elapsed: 0.006 s
% 0.20/0.49  % (23142)------------------------------
% 0.20/0.49  % (23142)------------------------------
% 0.20/0.49  % (23126)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (23134)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (23125)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (23131)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (23124)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (23122)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (23147)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (23121)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (23127)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (23145)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (23123)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (23139)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (23144)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (23133)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (23148)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (23120)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.55  % (23137)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (23149)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (23136)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (23140)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (23128)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (23129)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (23141)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  % (23135)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.56  % (23132)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (23130)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (23150)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.20/0.56  % (23143)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.56  % (23145)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f1225,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f130,f136,f142,f147,f334,f398,f436,f459,f460,f461,f516,f545,f615,f1122,f1167,f1218])).
% 0.20/0.57  fof(f1218,plain,(
% 0.20/0.57    ~spl9_96 | ~spl9_5 | ~spl9_19 | spl9_90),
% 0.20/0.57    inference(avatar_split_clause,[],[f1213,f1119,f316,f144,f1162])).
% 0.20/0.57  fof(f1162,plain,(
% 0.20/0.57    spl9_96 <=> r2_hidden(sK0,k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).
% 0.20/0.57  fof(f144,plain,(
% 0.20/0.57    spl9_5 <=> v3_ordinal1(sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.20/0.57  fof(f316,plain,(
% 0.20/0.57    spl9_19 <=> v3_ordinal1(sK2(sK0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.20/0.57  fof(f1119,plain,(
% 0.20/0.57    spl9_90 <=> r1_ordinal1(sK0,sK2(sK0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).
% 0.20/0.57  fof(f1213,plain,(
% 0.20/0.57    ~r2_hidden(sK0,k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) | (~spl9_5 | ~spl9_19 | spl9_90)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f146,f318,f1121,f117])).
% 0.20/0.57  fof(f117,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f81,f73])).
% 0.20/0.57  fof(f73,plain,(
% 0.20/0.57    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.57  fof(f81,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f45])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,axiom,(
% 0.20/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.20/0.57  fof(f1121,plain,(
% 0.20/0.57    ~r1_ordinal1(sK0,sK2(sK0)) | spl9_90),
% 0.20/0.57    inference(avatar_component_clause,[],[f1119])).
% 0.20/0.57  fof(f318,plain,(
% 0.20/0.57    v3_ordinal1(sK2(sK0)) | ~spl9_19),
% 0.20/0.57    inference(avatar_component_clause,[],[f316])).
% 0.20/0.57  fof(f146,plain,(
% 0.20/0.57    v3_ordinal1(sK0) | ~spl9_5),
% 0.20/0.57    inference(avatar_component_clause,[],[f144])).
% 0.20/0.57  fof(f1167,plain,(
% 0.20/0.57    ~spl9_30 | spl9_96 | spl9_32 | ~spl9_5 | spl9_17),
% 0.20/0.57    inference(avatar_split_clause,[],[f1166,f306,f144,f539,f1162,f513])).
% 0.20/0.57  fof(f513,plain,(
% 0.20/0.57    spl9_30 <=> v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 0.20/0.57  fof(f539,plain,(
% 0.20/0.57    spl9_32 <=> sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 0.20/0.57  fof(f306,plain,(
% 0.20/0.57    spl9_17 <=> r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.20/0.57  fof(f1166,plain,(
% 0.20/0.57    sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))) | r2_hidden(sK0,k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) | ~v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) | (~spl9_5 | spl9_17)),
% 0.20/0.57    inference(subsumption_resolution,[],[f1143,f146])).
% 0.20/0.57  fof(f1143,plain,(
% 0.20/0.57    sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))) | r2_hidden(sK0,k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) | ~v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) | ~v3_ordinal1(sK0) | spl9_17),
% 0.20/0.57    inference(resolution,[],[f308,f83])).
% 0.20/0.57  fof(f83,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.57    inference(flattening,[],[f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.20/0.57  fof(f308,plain,(
% 0.20/0.57    ~r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0) | spl9_17),
% 0.20/0.57    inference(avatar_component_clause,[],[f306])).
% 0.20/0.57  fof(f1122,plain,(
% 0.20/0.57    ~spl9_90 | ~spl9_5 | ~spl9_19 | spl9_39),
% 0.20/0.57    inference(avatar_split_clause,[],[f1114,f606,f316,f144,f1119])).
% 0.20/0.57  fof(f606,plain,(
% 0.20/0.57    spl9_39 <=> r1_tarski(sK0,sK2(sK0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 0.20/0.57  fof(f1114,plain,(
% 0.20/0.57    ~r1_ordinal1(sK0,sK2(sK0)) | (~spl9_5 | ~spl9_19 | spl9_39)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f146,f318,f608,f91])).
% 0.20/0.57  fof(f91,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f52])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.57    inference(flattening,[],[f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.57  fof(f608,plain,(
% 0.20/0.57    ~r1_tarski(sK0,sK2(sK0)) | spl9_39),
% 0.20/0.57    inference(avatar_component_clause,[],[f606])).
% 0.20/0.57  fof(f615,plain,(
% 0.20/0.57    ~spl9_39 | ~spl9_18),
% 0.20/0.57    inference(avatar_split_clause,[],[f585,f311,f606])).
% 0.20/0.57  fof(f311,plain,(
% 0.20/0.57    spl9_18 <=> r2_hidden(sK2(sK0),sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.20/0.57  fof(f585,plain,(
% 0.20/0.57    ~r1_tarski(sK0,sK2(sK0)) | ~spl9_18),
% 0.20/0.57    inference(resolution,[],[f313,f105])).
% 0.20/0.57  fof(f105,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,axiom,(
% 0.20/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.57  fof(f313,plain,(
% 0.20/0.57    r2_hidden(sK2(sK0),sK0) | ~spl9_18),
% 0.20/0.57    inference(avatar_component_clause,[],[f311])).
% 0.20/0.57  fof(f545,plain,(
% 0.20/0.57    ~spl9_32 | ~spl9_1 | ~spl9_19),
% 0.20/0.57    inference(avatar_split_clause,[],[f536,f316,f124,f539])).
% 0.20/0.57  fof(f124,plain,(
% 0.20/0.57    spl9_1 <=> ! [X2] : (sK0 != k2_xboole_0(X2,k1_tarski(X2)) | ~v3_ordinal1(X2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.20/0.57  fof(f536,plain,(
% 0.20/0.57    sK0 != k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))) | (~spl9_1 | ~spl9_19)),
% 0.20/0.57    inference(resolution,[],[f125,f318])).
% 0.20/0.57  fof(f125,plain,(
% 0.20/0.57    ( ! [X2] : (~v3_ordinal1(X2) | sK0 != k2_xboole_0(X2,k1_tarski(X2))) ) | ~spl9_1),
% 0.20/0.57    inference(avatar_component_clause,[],[f124])).
% 0.20/0.57  fof(f516,plain,(
% 0.20/0.57    spl9_30 | ~spl9_19),
% 0.20/0.57    inference(avatar_split_clause,[],[f467,f316,f513])).
% 0.20/0.57  fof(f467,plain,(
% 0.20/0.57    v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) | ~spl9_19),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f318,f111])).
% 0.20/0.57  fof(f111,plain,(
% 0.20/0.57    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f74,f73])).
% 0.20/0.57  fof(f74,plain,(
% 0.20/0.57    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.20/0.57  fof(f461,plain,(
% 0.20/0.57    spl9_19 | spl9_2 | ~spl9_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f453,f144,f127,f316])).
% 0.20/0.57  fof(f127,plain,(
% 0.20/0.57    spl9_2 <=> v4_ordinal1(sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.20/0.57  fof(f453,plain,(
% 0.20/0.57    v3_ordinal1(sK2(sK0)) | (spl9_2 | ~spl9_5)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f146,f128,f76])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    ( ! [X0] : (v4_ordinal1(X0) | v3_ordinal1(sK2(X0)) | ~v3_ordinal1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ! [X0] : (((v4_ordinal1(X0) | (~r2_hidden(k1_ordinal1(sK2(X0)),X0) & r2_hidden(sK2(X0),X0) & v3_ordinal1(sK2(X0)))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK2(X0)),X0) & r2_hidden(sK2(X0),X0) & v3_ordinal1(sK2(X0))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 0.20/0.57    inference(rectify,[],[f40])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f23])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 0.20/0.57    inference(flattening,[],[f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,axiom,(
% 0.20/0.57    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).
% 0.20/0.57  fof(f128,plain,(
% 0.20/0.57    ~v4_ordinal1(sK0) | spl9_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f127])).
% 0.20/0.57  fof(f460,plain,(
% 0.20/0.57    spl9_18 | spl9_2 | ~spl9_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f454,f144,f127,f311])).
% 0.20/0.57  fof(f454,plain,(
% 0.20/0.57    r2_hidden(sK2(sK0),sK0) | (spl9_2 | ~spl9_5)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f146,f128,f77])).
% 0.20/0.57  fof(f77,plain,(
% 0.20/0.57    ( ! [X0] : (v4_ordinal1(X0) | r2_hidden(sK2(X0),X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f43])).
% 0.20/0.57  fof(f459,plain,(
% 0.20/0.57    ~spl9_17 | spl9_2 | ~spl9_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f455,f144,f127,f306])).
% 0.20/0.57  fof(f455,plain,(
% 0.20/0.57    ~r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0) | (spl9_2 | ~spl9_5)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f146,f128,f112])).
% 0.20/0.57  fof(f112,plain,(
% 0.20/0.57    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k2_xboole_0(sK2(X0),k1_tarski(sK2(X0))),X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f78,f73])).
% 0.20/0.57  fof(f78,plain,(
% 0.20/0.57    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k1_ordinal1(sK2(X0)),X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f43])).
% 0.20/0.57  fof(f436,plain,(
% 0.20/0.57    ~spl9_22),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f435])).
% 0.20/0.57  fof(f435,plain,(
% 0.20/0.57    $false | ~spl9_22),
% 0.20/0.57    inference(subsumption_resolution,[],[f427,f119])).
% 0.20/0.57  fof(f119,plain,(
% 0.20/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.57    inference(equality_resolution,[],[f93])).
% 0.20/0.57  fof(f93,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f54])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.57    inference(flattening,[],[f53])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.57  fof(f427,plain,(
% 0.20/0.57    ~r1_tarski(sK0,sK0) | ~spl9_22),
% 0.20/0.57    inference(resolution,[],[f397,f105])).
% 0.20/0.57  fof(f397,plain,(
% 0.20/0.57    r2_hidden(sK0,sK0) | ~spl9_22),
% 0.20/0.57    inference(avatar_component_clause,[],[f395])).
% 0.20/0.57  fof(f395,plain,(
% 0.20/0.57    spl9_22 <=> r2_hidden(sK0,sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.20/0.57  fof(f398,plain,(
% 0.20/0.57    spl9_22 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_16),
% 0.20/0.57    inference(avatar_split_clause,[],[f393,f290,f144,f138,f132,f127,f395])).
% 0.20/0.57  fof(f132,plain,(
% 0.20/0.57    spl9_3 <=> sK0 = k2_xboole_0(sK1,k1_tarski(sK1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.20/0.57  fof(f138,plain,(
% 0.20/0.57    spl9_4 <=> v3_ordinal1(sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.20/0.57  fof(f290,plain,(
% 0.20/0.57    spl9_16 <=> r2_hidden(sK1,sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.20/0.57  fof(f393,plain,(
% 0.20/0.57    r2_hidden(sK0,sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_16)),
% 0.20/0.57    inference(forward_demodulation,[],[f369,f134])).
% 0.20/0.57  fof(f134,plain,(
% 0.20/0.57    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | ~spl9_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f132])).
% 0.20/0.57  fof(f369,plain,(
% 0.20/0.57    r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | (~spl9_2 | ~spl9_4 | ~spl9_5 | ~spl9_16)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f146,f129,f140,f292,f113])).
% 0.20/0.57  fof(f113,plain,(
% 0.20/0.57    ( ! [X2,X0] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f75,f73])).
% 0.20/0.57  fof(f75,plain,(
% 0.20/0.57    ( ! [X2,X0] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f43])).
% 0.20/0.57  fof(f292,plain,(
% 0.20/0.57    r2_hidden(sK1,sK0) | ~spl9_16),
% 0.20/0.57    inference(avatar_component_clause,[],[f290])).
% 0.20/0.57  fof(f140,plain,(
% 0.20/0.57    v3_ordinal1(sK1) | ~spl9_4),
% 0.20/0.57    inference(avatar_component_clause,[],[f138])).
% 0.20/0.57  fof(f129,plain,(
% 0.20/0.57    v4_ordinal1(sK0) | ~spl9_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f127])).
% 0.20/0.57  fof(f334,plain,(
% 0.20/0.57    spl9_16 | ~spl9_3),
% 0.20/0.57    inference(avatar_split_clause,[],[f327,f132,f290])).
% 0.20/0.57  fof(f327,plain,(
% 0.20/0.57    r2_hidden(sK1,sK0) | ~spl9_3),
% 0.20/0.57    inference(superposition,[],[f110,f134])).
% 0.20/0.57  fof(f110,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f72,f73])).
% 0.20/0.57  fof(f72,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.20/0.57  fof(f147,plain,(
% 0.20/0.57    spl9_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f65,f144])).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    v3_ordinal1(sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ((v4_ordinal1(sK0) & (sK0 = k1_ordinal1(sK1) & v3_ordinal1(sK1))) | (! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK0))) & v3_ordinal1(sK0)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f38,f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0)) => (((v4_ordinal1(sK0) & ? [X1] : (k1_ordinal1(X1) = sK0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK0))) & v3_ordinal1(sK0))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ? [X1] : (k1_ordinal1(X1) = sK0 & v3_ordinal1(X1)) => (sK0 = k1_ordinal1(sK1) & v3_ordinal1(sK1))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X2] : (v3_ordinal1(X2) => k1_ordinal1(X2) != X0) & ~v4_ordinal1(X0))))),
% 0.20/0.57    inference(rectify,[],[f18])).
% 0.20/0.57  fof(f18,negated_conjecture,(
% 0.20/0.57    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 0.20/0.57    inference(negated_conjecture,[],[f17])).
% 0.20/0.57  fof(f17,conjecture,(
% 0.20/0.57    ! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_ordinal1)).
% 0.20/0.57  fof(f142,plain,(
% 0.20/0.57    ~spl9_2 | spl9_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f66,f138,f127])).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f39])).
% 0.20/0.57  fof(f136,plain,(
% 0.20/0.57    ~spl9_2 | spl9_3),
% 0.20/0.57    inference(avatar_split_clause,[],[f108,f132,f127])).
% 0.20/0.57  fof(f108,plain,(
% 0.20/0.57    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | ~v4_ordinal1(sK0)),
% 0.20/0.57    inference(definition_unfolding,[],[f68,f73])).
% 0.20/0.57  fof(f68,plain,(
% 0.20/0.57    sK0 = k1_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f39])).
% 0.20/0.57  fof(f130,plain,(
% 0.20/0.57    spl9_1 | spl9_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f106,f127,f124])).
% 0.20/0.57  fof(f106,plain,(
% 0.20/0.57    ( ! [X2] : (v4_ordinal1(sK0) | sK0 != k2_xboole_0(X2,k1_tarski(X2)) | ~v3_ordinal1(X2)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f71,f73])).
% 0.20/0.57  fof(f71,plain,(
% 0.20/0.57    ( ! [X2] : (v4_ordinal1(sK0) | k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f39])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (23145)------------------------------
% 0.20/0.57  % (23145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (23145)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (23145)Memory used [KB]: 6908
% 0.20/0.57  % (23138)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.57  % (23146)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.59  % (23145)Time elapsed: 0.164 s
% 0.20/0.59  % (23145)------------------------------
% 0.20/0.59  % (23145)------------------------------
% 0.20/0.59  % (23119)Success in time 0.228 s
%------------------------------------------------------------------------------
