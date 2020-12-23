%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:29 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 489 expanded)
%              Number of leaves         :   37 ( 186 expanded)
%              Depth                    :   12
%              Number of atoms          :  486 (1128 expanded)
%              Number of equality atoms :   47 ( 263 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1340,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f105,f110,f115,f149,f737,f900,f906,f945,f1124,f1130,f1177,f1178,f1209,f1229,f1238,f1290,f1331,f1339])).

fof(f1339,plain,
    ( ~ spl3_22
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f1306,f650,f378])).

fof(f378,plain,
    ( spl3_22
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f650,plain,
    ( spl3_29
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f1306,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl3_29 ),
    inference(unit_resulting_resolution,[],[f652,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f652,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f650])).

fof(f1331,plain,
    ( ~ spl3_18
    | spl3_21
    | spl3_22 ),
    inference(avatar_split_clause,[],[f1312,f378,f373,f333])).

fof(f333,plain,
    ( spl3_18
  <=> r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f373,plain,
    ( spl3_21
  <=> r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f1312,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl3_21
    | spl3_22 ),
    inference(unit_resulting_resolution,[],[f380,f375,f95])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f63,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f375,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f373])).

fof(f380,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f378])).

fof(f1290,plain,
    ( spl3_29
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f1289,f399,f112,f107,f650])).

fof(f107,plain,
    ( spl3_3
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f112,plain,
    ( spl3_4
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f399,plain,
    ( spl3_23
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f1289,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f1288,f114])).

fof(f114,plain,
    ( v3_ordinal1(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f1288,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f1286,f109])).

fof(f109,plain,
    ( v3_ordinal1(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f1286,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl3_23 ),
    inference(resolution,[],[f401,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f401,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f399])).

fof(f1238,plain,
    ( ~ spl3_21
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f1235,f166,f373])).

fof(f166,plain,
    ( spl3_8
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f1235,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_8 ),
    inference(resolution,[],[f167,f61])).

fof(f167,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f166])).

fof(f1229,plain,
    ( spl3_23
    | ~ spl3_3
    | ~ spl3_4
    | spl3_7 ),
    inference(avatar_split_clause,[],[f1228,f161,f112,f107,f399])).

fof(f161,plain,
    ( spl3_7
  <=> r1_ordinal1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f1228,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | spl3_7 ),
    inference(subsumption_resolution,[],[f1227,f114])).

fof(f1227,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl3_3
    | spl3_7 ),
    inference(subsumption_resolution,[],[f1216,f109])).

fof(f1216,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl3_7 ),
    inference(resolution,[],[f162,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f162,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f161])).

fof(f1209,plain,
    ( spl3_18
    | spl3_2
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f1208,f146,f107,f101,f333])).

fof(f101,plain,
    ( spl3_2
  <=> r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

% (10841)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f146,plain,
    ( spl3_6
  <=> v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1208,plain,
    ( r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f1207,f148])).

fof(f148,plain,
    ( v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f146])).

fof(f1207,plain,
    ( r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f1186,f109])).

fof(f1186,plain,
    ( r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl3_2 ),
    inference(resolution,[],[f103,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f103,plain,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f1178,plain,
    ( ~ spl3_10
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f1171,f97,f179])).

fof(f179,plain,
    ( spl3_10
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f97,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1171,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f98,f61])).

fof(f98,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f1177,plain,
    ( spl3_8
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f1172,f97,f166])).

fof(f1172,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f98,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f79])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f77])).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1130,plain,
    ( ~ spl3_3
    | spl3_24
    | spl3_1
    | ~ spl3_4
    | spl3_22 ),
    inference(avatar_split_clause,[],[f1129,f378,f112,f97,f404,f107])).

fof(f404,plain,
    ( spl3_24
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f1129,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ spl3_4
    | spl3_22 ),
    inference(subsumption_resolution,[],[f955,f114])).

fof(f955,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | spl3_22 ),
    inference(resolution,[],[f380,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f1124,plain,
    ( spl3_18
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f1123])).

fof(f1123,plain,
    ( $false
    | spl3_18
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1075,f83])).

fof(f83,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f48,f80])).

fof(f80,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f50,f78,f79])).

fof(f50,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f48,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f1075,plain,
    ( ~ r2_hidden(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl3_18
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f335,f406])).

fof(f406,plain,
    ( sK0 = sK1
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f404])).

fof(f335,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f333])).

fof(f945,plain,
    ( ~ spl3_18
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f939,f233,f333])).

fof(f233,plain,
    ( spl3_11
  <=> r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f939,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl3_11 ),
    inference(resolution,[],[f235,f61])).

fof(f235,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f233])).

fof(f906,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f905,f161,f112,f107,f179])).

fof(f905,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f904,f109])).

fof(f904,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f902,f114])).

fof(f902,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f163,f57])).

fof(f163,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f161])).

fof(f900,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f899,f146,f107,f101,f233])).

fof(f899,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f898,f148])).

fof(f898,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f893,f109])).

fof(f893,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl3_2 ),
    inference(resolution,[],[f102,f57])).

fof(f102,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f737,plain,
    ( ~ spl3_22
    | spl3_18 ),
    inference(avatar_split_clause,[],[f344,f333,f378])).

fof(f344,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f335,f94])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f64,f78])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f149,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f133,f112,f146])).

fof(f133,plain,
    ( v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f114,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f51,f80])).

fof(f51,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f115,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f44,f112])).

fof(f44,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
          | ~ r2_hidden(sK0,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK0),X1)
          | r2_hidden(sK0,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
        | ~ r2_hidden(sK0,sK1) )
      & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
        | r2_hidden(sK0,sK1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f110,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f45,f107])).

fof(f45,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f105,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f82,f101,f97])).

fof(f82,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f46,f80])).

fof(f46,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f104,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f81,f101,f97])).

fof(f81,plain,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f47,f80])).

fof(f47,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:47:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (10839)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (10861)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.49  % (10853)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.50  % (10847)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (10835)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.20/0.52  % (10836)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.20/0.52  % (10858)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.20/0.52  % (10840)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.20/0.52  % (10857)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.20/0.52  % (10850)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.20/0.52  % (10844)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.20/0.53  % (10865)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.20/0.53  % (10856)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.20/0.53  % (10838)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.20/0.53  % (10861)Refutation found. Thanks to Tanya!
% 1.20/0.53  % SZS status Theorem for theBenchmark
% 1.20/0.53  % SZS output start Proof for theBenchmark
% 1.20/0.53  fof(f1340,plain,(
% 1.20/0.53    $false),
% 1.20/0.53    inference(avatar_sat_refutation,[],[f104,f105,f110,f115,f149,f737,f900,f906,f945,f1124,f1130,f1177,f1178,f1209,f1229,f1238,f1290,f1331,f1339])).
% 1.20/0.53  fof(f1339,plain,(
% 1.20/0.53    ~spl3_22 | ~spl3_29),
% 1.20/0.53    inference(avatar_split_clause,[],[f1306,f650,f378])).
% 1.20/0.53  fof(f378,plain,(
% 1.20/0.53    spl3_22 <=> r2_hidden(sK1,sK0)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.20/0.53  fof(f650,plain,(
% 1.20/0.53    spl3_29 <=> r1_tarski(sK0,sK1)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 1.20/0.53  fof(f1306,plain,(
% 1.20/0.53    ~r2_hidden(sK1,sK0) | ~spl3_29),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f652,f61])).
% 1.20/0.53  fof(f61,plain,(
% 1.20/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f31])).
% 1.20/0.53  fof(f31,plain,(
% 1.20/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.20/0.53    inference(ennf_transformation,[],[f18])).
% 1.20/0.53  fof(f18,axiom,(
% 1.20/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.20/0.53  fof(f652,plain,(
% 1.20/0.53    r1_tarski(sK0,sK1) | ~spl3_29),
% 1.20/0.53    inference(avatar_component_clause,[],[f650])).
% 1.20/0.53  fof(f1331,plain,(
% 1.20/0.53    ~spl3_18 | spl3_21 | spl3_22),
% 1.20/0.53    inference(avatar_split_clause,[],[f1312,f378,f373,f333])).
% 1.20/0.53  fof(f333,plain,(
% 1.20/0.53    spl3_18 <=> r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.20/0.53  fof(f373,plain,(
% 1.20/0.53    spl3_21 <=> r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.20/0.53  fof(f1312,plain,(
% 1.20/0.53    ~r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (spl3_21 | spl3_22)),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f380,f375,f95])).
% 1.20/0.53  fof(f95,plain,(
% 1.20/0.53    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.20/0.53    inference(equality_resolution,[],[f92])).
% 1.20/0.53  fof(f92,plain,(
% 1.20/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.20/0.53    inference(definition_unfolding,[],[f63,f78])).
% 1.20/0.53  fof(f78,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.20/0.53    inference(definition_unfolding,[],[f54,f77])).
% 1.20/0.53  fof(f77,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.20/0.53    inference(definition_unfolding,[],[f55,f76])).
% 1.20/0.53  fof(f76,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.20/0.53    inference(definition_unfolding,[],[f62,f75])).
% 1.20/0.53  fof(f75,plain,(
% 1.20/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.20/0.53    inference(definition_unfolding,[],[f69,f74])).
% 1.20/0.53  fof(f74,plain,(
% 1.20/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.20/0.53    inference(definition_unfolding,[],[f70,f73])).
% 1.20/0.53  fof(f73,plain,(
% 1.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.20/0.53    inference(definition_unfolding,[],[f71,f72])).
% 1.20/0.53  fof(f72,plain,(
% 1.20/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f8])).
% 1.20/0.53  fof(f8,axiom,(
% 1.20/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.20/0.53  fof(f71,plain,(
% 1.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f7])).
% 1.20/0.53  fof(f7,axiom,(
% 1.20/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.20/0.53  fof(f70,plain,(
% 1.20/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f6])).
% 1.20/0.53  fof(f6,axiom,(
% 1.20/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.20/0.53  fof(f69,plain,(
% 1.20/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f5])).
% 1.20/0.53  fof(f5,axiom,(
% 1.20/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.20/0.53  fof(f62,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f4])).
% 1.20/0.53  fof(f4,axiom,(
% 1.20/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.20/0.53  fof(f55,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f3])).
% 1.20/0.53  fof(f3,axiom,(
% 1.20/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.20/0.53  fof(f54,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f10])).
% 1.20/0.53  fof(f10,axiom,(
% 1.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.20/0.53  fof(f63,plain,(
% 1.20/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.20/0.53    inference(cnf_transformation,[],[f43])).
% 1.20/0.53  fof(f43,plain,(
% 1.20/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 1.20/0.53  fof(f42,plain,(
% 1.20/0.53    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.20/0.53    introduced(choice_axiom,[])).
% 1.20/0.53  fof(f41,plain,(
% 1.20/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.20/0.53    inference(rectify,[],[f40])).
% 1.20/0.53  fof(f40,plain,(
% 1.20/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.20/0.53    inference(flattening,[],[f39])).
% 1.20/0.53  fof(f39,plain,(
% 1.20/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.20/0.53    inference(nnf_transformation,[],[f1])).
% 1.20/0.53  fof(f1,axiom,(
% 1.20/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.20/0.53  fof(f375,plain,(
% 1.20/0.53    ~r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl3_21),
% 1.20/0.53    inference(avatar_component_clause,[],[f373])).
% 1.20/0.53  fof(f380,plain,(
% 1.20/0.53    ~r2_hidden(sK1,sK0) | spl3_22),
% 1.20/0.53    inference(avatar_component_clause,[],[f378])).
% 1.20/0.53  fof(f1290,plain,(
% 1.20/0.53    spl3_29 | ~spl3_3 | ~spl3_4 | ~spl3_23),
% 1.20/0.53    inference(avatar_split_clause,[],[f1289,f399,f112,f107,f650])).
% 1.20/0.53  fof(f107,plain,(
% 1.20/0.53    spl3_3 <=> v3_ordinal1(sK1)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.20/0.53  fof(f112,plain,(
% 1.20/0.53    spl3_4 <=> v3_ordinal1(sK0)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.20/0.53  fof(f399,plain,(
% 1.20/0.53    spl3_23 <=> r1_ordinal1(sK0,sK1)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.20/0.53  fof(f1289,plain,(
% 1.20/0.53    r1_tarski(sK0,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_23)),
% 1.20/0.53    inference(subsumption_resolution,[],[f1288,f114])).
% 1.20/0.53  fof(f114,plain,(
% 1.20/0.53    v3_ordinal1(sK0) | ~spl3_4),
% 1.20/0.53    inference(avatar_component_clause,[],[f112])).
% 1.20/0.53  fof(f1288,plain,(
% 1.20/0.53    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | (~spl3_3 | ~spl3_23)),
% 1.20/0.53    inference(subsumption_resolution,[],[f1286,f109])).
% 1.20/0.53  fof(f109,plain,(
% 1.20/0.53    v3_ordinal1(sK1) | ~spl3_3),
% 1.20/0.53    inference(avatar_component_clause,[],[f107])).
% 1.20/0.53  fof(f1286,plain,(
% 1.20/0.53    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~spl3_23),
% 1.20/0.53    inference(resolution,[],[f401,f57])).
% 1.20/0.53  fof(f57,plain,(
% 1.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f37])).
% 1.20/0.53  fof(f37,plain,(
% 1.20/0.53    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.20/0.53    inference(nnf_transformation,[],[f30])).
% 1.20/0.53  fof(f30,plain,(
% 1.20/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.20/0.53    inference(flattening,[],[f29])).
% 1.20/0.53  fof(f29,plain,(
% 1.20/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.20/0.53    inference(ennf_transformation,[],[f13])).
% 1.20/0.53  fof(f13,axiom,(
% 1.20/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.20/0.53  fof(f401,plain,(
% 1.20/0.53    r1_ordinal1(sK0,sK1) | ~spl3_23),
% 1.20/0.53    inference(avatar_component_clause,[],[f399])).
% 1.20/0.53  fof(f1238,plain,(
% 1.20/0.53    ~spl3_21 | ~spl3_8),
% 1.20/0.53    inference(avatar_split_clause,[],[f1235,f166,f373])).
% 1.20/0.53  fof(f166,plain,(
% 1.20/0.53    spl3_8 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.20/0.53  fof(f1235,plain,(
% 1.20/0.53    ~r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl3_8),
% 1.20/0.53    inference(resolution,[],[f167,f61])).
% 1.20/0.53  fof(f167,plain,(
% 1.20/0.53    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~spl3_8),
% 1.20/0.53    inference(avatar_component_clause,[],[f166])).
% 1.20/0.53  fof(f1229,plain,(
% 1.20/0.53    spl3_23 | ~spl3_3 | ~spl3_4 | spl3_7),
% 1.20/0.53    inference(avatar_split_clause,[],[f1228,f161,f112,f107,f399])).
% 1.20/0.53  fof(f161,plain,(
% 1.20/0.53    spl3_7 <=> r1_ordinal1(sK1,sK0)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.20/0.53  fof(f1228,plain,(
% 1.20/0.53    r1_ordinal1(sK0,sK1) | (~spl3_3 | ~spl3_4 | spl3_7)),
% 1.20/0.53    inference(subsumption_resolution,[],[f1227,f114])).
% 1.20/0.53  fof(f1227,plain,(
% 1.20/0.53    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0) | (~spl3_3 | spl3_7)),
% 1.20/0.53    inference(subsumption_resolution,[],[f1216,f109])).
% 1.20/0.53  fof(f1216,plain,(
% 1.20/0.53    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl3_7),
% 1.20/0.53    inference(resolution,[],[f162,f56])).
% 1.20/0.53  fof(f56,plain,(
% 1.20/0.53    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f28])).
% 1.20/0.53  fof(f28,plain,(
% 1.20/0.53    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.20/0.53    inference(flattening,[],[f27])).
% 1.20/0.53  fof(f27,plain,(
% 1.20/0.53    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.20/0.53    inference(ennf_transformation,[],[f11])).
% 1.20/0.53  fof(f11,axiom,(
% 1.20/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 1.20/0.53  fof(f162,plain,(
% 1.20/0.53    ~r1_ordinal1(sK1,sK0) | spl3_7),
% 1.20/0.53    inference(avatar_component_clause,[],[f161])).
% 1.20/0.53  fof(f1209,plain,(
% 1.20/0.53    spl3_18 | spl3_2 | ~spl3_3 | ~spl3_6),
% 1.20/0.53    inference(avatar_split_clause,[],[f1208,f146,f107,f101,f333])).
% 1.20/0.53  fof(f101,plain,(
% 1.20/0.53    spl3_2 <=> r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.20/0.53  % (10841)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.20/0.53  fof(f146,plain,(
% 1.20/0.53    spl3_6 <=> v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.20/0.53  fof(f1208,plain,(
% 1.20/0.53    r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (spl3_2 | ~spl3_3 | ~spl3_6)),
% 1.20/0.53    inference(subsumption_resolution,[],[f1207,f148])).
% 1.20/0.53  fof(f148,plain,(
% 1.20/0.53    v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl3_6),
% 1.20/0.53    inference(avatar_component_clause,[],[f146])).
% 1.20/0.53  fof(f1207,plain,(
% 1.20/0.53    r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (spl3_2 | ~spl3_3)),
% 1.20/0.53    inference(subsumption_resolution,[],[f1186,f109])).
% 1.20/0.53  fof(f1186,plain,(
% 1.20/0.53    r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | spl3_2),
% 1.20/0.53    inference(resolution,[],[f103,f52])).
% 1.20/0.53  fof(f52,plain,(
% 1.20/0.53    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f24])).
% 1.20/0.53  fof(f24,plain,(
% 1.20/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.20/0.53    inference(flattening,[],[f23])).
% 1.20/0.53  fof(f23,plain,(
% 1.20/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.20/0.53    inference(ennf_transformation,[],[f16])).
% 1.20/0.53  fof(f16,axiom,(
% 1.20/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.20/0.53  fof(f103,plain,(
% 1.20/0.53    ~r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | spl3_2),
% 1.20/0.53    inference(avatar_component_clause,[],[f101])).
% 1.20/0.53  fof(f1178,plain,(
% 1.20/0.53    ~spl3_10 | ~spl3_1),
% 1.20/0.53    inference(avatar_split_clause,[],[f1171,f97,f179])).
% 1.20/0.53  fof(f179,plain,(
% 1.20/0.53    spl3_10 <=> r1_tarski(sK1,sK0)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.20/0.53  fof(f97,plain,(
% 1.20/0.53    spl3_1 <=> r2_hidden(sK0,sK1)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.20/0.53  fof(f1171,plain,(
% 1.20/0.53    ~r1_tarski(sK1,sK0) | ~spl3_1),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f98,f61])).
% 1.20/0.53  fof(f98,plain,(
% 1.20/0.53    r2_hidden(sK0,sK1) | ~spl3_1),
% 1.20/0.53    inference(avatar_component_clause,[],[f97])).
% 1.20/0.53  fof(f1177,plain,(
% 1.20/0.53    spl3_8 | ~spl3_1),
% 1.20/0.53    inference(avatar_split_clause,[],[f1172,f97,f166])).
% 1.20/0.53  fof(f1172,plain,(
% 1.20/0.53    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~spl3_1),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f98,f85])).
% 1.20/0.53  fof(f85,plain,(
% 1.20/0.53    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.20/0.53    inference(definition_unfolding,[],[f60,f79])).
% 1.20/0.53  fof(f79,plain,(
% 1.20/0.53    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.20/0.53    inference(definition_unfolding,[],[f49,f77])).
% 1.20/0.53  fof(f49,plain,(
% 1.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f2])).
% 1.20/0.53  fof(f2,axiom,(
% 1.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.20/0.53  fof(f60,plain,(
% 1.20/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f38])).
% 1.20/0.53  fof(f38,plain,(
% 1.20/0.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.20/0.53    inference(nnf_transformation,[],[f9])).
% 1.20/0.53  fof(f9,axiom,(
% 1.20/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.20/0.53  fof(f1130,plain,(
% 1.20/0.53    ~spl3_3 | spl3_24 | spl3_1 | ~spl3_4 | spl3_22),
% 1.20/0.53    inference(avatar_split_clause,[],[f1129,f378,f112,f97,f404,f107])).
% 1.20/0.53  fof(f404,plain,(
% 1.20/0.53    spl3_24 <=> sK0 = sK1),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.20/0.53  fof(f1129,plain,(
% 1.20/0.53    r2_hidden(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK1) | (~spl3_4 | spl3_22)),
% 1.20/0.53    inference(subsumption_resolution,[],[f955,f114])).
% 1.20/0.53  fof(f955,plain,(
% 1.20/0.53    r2_hidden(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | spl3_22),
% 1.20/0.53    inference(resolution,[],[f380,f53])).
% 1.20/0.53  fof(f53,plain,(
% 1.20/0.53    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f26])).
% 1.20/0.53  fof(f26,plain,(
% 1.20/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.20/0.53    inference(flattening,[],[f25])).
% 1.20/0.53  fof(f25,plain,(
% 1.20/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.20/0.53    inference(ennf_transformation,[],[f15])).
% 1.20/0.53  fof(f15,axiom,(
% 1.20/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 1.20/0.53  fof(f1124,plain,(
% 1.20/0.53    spl3_18 | ~spl3_24),
% 1.20/0.53    inference(avatar_contradiction_clause,[],[f1123])).
% 1.20/0.53  fof(f1123,plain,(
% 1.20/0.53    $false | (spl3_18 | ~spl3_24)),
% 1.20/0.53    inference(subsumption_resolution,[],[f1075,f83])).
% 1.20/0.53  fof(f83,plain,(
% 1.20/0.53    ( ! [X0] : (r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 1.20/0.53    inference(definition_unfolding,[],[f48,f80])).
% 1.20/0.53  fof(f80,plain,(
% 1.20/0.53    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 1.20/0.53    inference(definition_unfolding,[],[f50,f78,f79])).
% 1.20/0.53  fof(f50,plain,(
% 1.20/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f12])).
% 1.20/0.53  fof(f12,axiom,(
% 1.20/0.53    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.20/0.53  fof(f48,plain,(
% 1.20/0.53    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f14])).
% 1.20/0.53  fof(f14,axiom,(
% 1.20/0.53    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.20/0.53  fof(f1075,plain,(
% 1.20/0.53    ~r2_hidden(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (spl3_18 | ~spl3_24)),
% 1.20/0.53    inference(backward_demodulation,[],[f335,f406])).
% 1.20/0.53  fof(f406,plain,(
% 1.20/0.53    sK0 = sK1 | ~spl3_24),
% 1.20/0.53    inference(avatar_component_clause,[],[f404])).
% 1.20/0.53  fof(f335,plain,(
% 1.20/0.53    ~r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | spl3_18),
% 1.20/0.53    inference(avatar_component_clause,[],[f333])).
% 1.20/0.53  fof(f945,plain,(
% 1.20/0.53    ~spl3_18 | ~spl3_11),
% 1.20/0.53    inference(avatar_split_clause,[],[f939,f233,f333])).
% 1.20/0.53  fof(f233,plain,(
% 1.20/0.53    spl3_11 <=> r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.20/0.53  fof(f939,plain,(
% 1.20/0.53    ~r2_hidden(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl3_11),
% 1.20/0.53    inference(resolution,[],[f235,f61])).
% 1.20/0.53  fof(f235,plain,(
% 1.20/0.53    r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | ~spl3_11),
% 1.20/0.53    inference(avatar_component_clause,[],[f233])).
% 1.20/0.53  fof(f906,plain,(
% 1.20/0.53    spl3_10 | ~spl3_3 | ~spl3_4 | ~spl3_7),
% 1.20/0.53    inference(avatar_split_clause,[],[f905,f161,f112,f107,f179])).
% 1.20/0.53  fof(f905,plain,(
% 1.20/0.53    r1_tarski(sK1,sK0) | (~spl3_3 | ~spl3_4 | ~spl3_7)),
% 1.20/0.53    inference(subsumption_resolution,[],[f904,f109])).
% 1.20/0.53  fof(f904,plain,(
% 1.20/0.53    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1) | (~spl3_4 | ~spl3_7)),
% 1.20/0.53    inference(subsumption_resolution,[],[f902,f114])).
% 1.20/0.53  fof(f902,plain,(
% 1.20/0.53    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | ~spl3_7),
% 1.20/0.53    inference(resolution,[],[f163,f57])).
% 1.20/0.53  fof(f163,plain,(
% 1.20/0.53    r1_ordinal1(sK1,sK0) | ~spl3_7),
% 1.20/0.53    inference(avatar_component_clause,[],[f161])).
% 1.20/0.53  fof(f900,plain,(
% 1.20/0.53    spl3_11 | ~spl3_2 | ~spl3_3 | ~spl3_6),
% 1.20/0.53    inference(avatar_split_clause,[],[f899,f146,f107,f101,f233])).
% 1.20/0.53  fof(f899,plain,(
% 1.20/0.53    r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | (~spl3_2 | ~spl3_3 | ~spl3_6)),
% 1.20/0.53    inference(subsumption_resolution,[],[f898,f148])).
% 1.20/0.53  fof(f898,plain,(
% 1.20/0.53    r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | ~v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (~spl3_2 | ~spl3_3)),
% 1.20/0.53    inference(subsumption_resolution,[],[f893,f109])).
% 1.20/0.53  fof(f893,plain,(
% 1.20/0.53    r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl3_2),
% 1.20/0.53    inference(resolution,[],[f102,f57])).
% 1.20/0.53  fof(f102,plain,(
% 1.20/0.53    r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | ~spl3_2),
% 1.20/0.53    inference(avatar_component_clause,[],[f101])).
% 1.20/0.53  fof(f737,plain,(
% 1.20/0.53    ~spl3_22 | spl3_18),
% 1.20/0.53    inference(avatar_split_clause,[],[f344,f333,f378])).
% 1.20/0.53  fof(f344,plain,(
% 1.20/0.53    ~r2_hidden(sK1,sK0) | spl3_18),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f335,f94])).
% 1.20/0.53  fof(f94,plain,(
% 1.20/0.53    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 1.20/0.53    inference(equality_resolution,[],[f91])).
% 1.20/0.53  fof(f91,plain,(
% 1.20/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.20/0.53    inference(definition_unfolding,[],[f64,f78])).
% 1.20/0.53  fof(f64,plain,(
% 1.20/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 1.20/0.53    inference(cnf_transformation,[],[f43])).
% 1.20/0.53  fof(f149,plain,(
% 1.20/0.53    spl3_6 | ~spl3_4),
% 1.20/0.53    inference(avatar_split_clause,[],[f133,f112,f146])).
% 1.20/0.53  fof(f133,plain,(
% 1.20/0.53    v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl3_4),
% 1.20/0.53    inference(unit_resulting_resolution,[],[f114,f84])).
% 1.20/0.53  fof(f84,plain,(
% 1.20/0.53    ( ! [X0] : (v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) | ~v3_ordinal1(X0)) )),
% 1.20/0.53    inference(definition_unfolding,[],[f51,f80])).
% 1.20/0.53  fof(f51,plain,(
% 1.20/0.53    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f22])).
% 1.20/0.53  fof(f22,plain,(
% 1.20/0.53    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.20/0.53    inference(ennf_transformation,[],[f17])).
% 1.20/0.53  fof(f17,axiom,(
% 1.20/0.53    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 1.20/0.53  fof(f115,plain,(
% 1.20/0.53    spl3_4),
% 1.20/0.53    inference(avatar_split_clause,[],[f44,f112])).
% 1.20/0.53  fof(f44,plain,(
% 1.20/0.53    v3_ordinal1(sK0)),
% 1.20/0.53    inference(cnf_transformation,[],[f36])).
% 1.20/0.53  fof(f36,plain,(
% 1.20/0.53    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 1.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).
% 1.20/0.53  fof(f34,plain,(
% 1.20/0.53    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 1.20/0.53    introduced(choice_axiom,[])).
% 1.20/0.53  fof(f35,plain,(
% 1.20/0.53    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 1.20/0.53    introduced(choice_axiom,[])).
% 1.20/0.53  fof(f33,plain,(
% 1.20/0.53    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.20/0.53    inference(flattening,[],[f32])).
% 1.20/0.53  fof(f32,plain,(
% 1.20/0.53    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.20/0.53    inference(nnf_transformation,[],[f21])).
% 1.20/0.53  fof(f21,plain,(
% 1.20/0.53    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.20/0.53    inference(ennf_transformation,[],[f20])).
% 1.20/0.53  fof(f20,negated_conjecture,(
% 1.20/0.53    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 1.20/0.53    inference(negated_conjecture,[],[f19])).
% 1.20/0.53  fof(f19,conjecture,(
% 1.20/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 1.20/0.53  fof(f110,plain,(
% 1.20/0.53    spl3_3),
% 1.20/0.53    inference(avatar_split_clause,[],[f45,f107])).
% 1.20/0.53  fof(f45,plain,(
% 1.20/0.53    v3_ordinal1(sK1)),
% 1.20/0.53    inference(cnf_transformation,[],[f36])).
% 1.20/0.53  fof(f105,plain,(
% 1.20/0.53    spl3_1 | spl3_2),
% 1.20/0.53    inference(avatar_split_clause,[],[f82,f101,f97])).
% 1.20/0.53  fof(f82,plain,(
% 1.20/0.53    r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | r2_hidden(sK0,sK1)),
% 1.20/0.53    inference(definition_unfolding,[],[f46,f80])).
% 1.20/0.53  fof(f46,plain,(
% 1.20/0.53    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 1.20/0.53    inference(cnf_transformation,[],[f36])).
% 1.20/0.53  fof(f104,plain,(
% 1.20/0.53    ~spl3_1 | ~spl3_2),
% 1.20/0.53    inference(avatar_split_clause,[],[f81,f101,f97])).
% 1.20/0.53  fof(f81,plain,(
% 1.20/0.53    ~r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | ~r2_hidden(sK0,sK1)),
% 1.20/0.53    inference(definition_unfolding,[],[f47,f80])).
% 1.20/0.53  fof(f47,plain,(
% 1.20/0.53    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 1.20/0.53    inference(cnf_transformation,[],[f36])).
% 1.20/0.53  % SZS output end Proof for theBenchmark
% 1.20/0.53  % (10861)------------------------------
% 1.20/0.53  % (10861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (10861)Termination reason: Refutation
% 1.20/0.53  
% 1.20/0.53  % (10861)Memory used [KB]: 7036
% 1.20/0.53  % (10861)Time elapsed: 0.137 s
% 1.20/0.53  % (10861)------------------------------
% 1.20/0.53  % (10861)------------------------------
% 1.35/0.53  % (10832)Success in time 0.169 s
%------------------------------------------------------------------------------
