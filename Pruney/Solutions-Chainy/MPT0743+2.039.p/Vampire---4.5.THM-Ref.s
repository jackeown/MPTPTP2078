%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 224 expanded)
%              Number of leaves         :   29 (  94 expanded)
%              Depth                    :    9
%              Number of atoms          :  414 ( 746 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f491,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f78,f83,f88,f118,f195,f204,f210,f223,f225,f272,f299,f309,f353,f363,f484])).

fof(f484,plain,
    ( ~ spl4_13
    | spl4_17
    | spl4_21 ),
    inference(avatar_split_clause,[],[f460,f360,f296,f245])).

fof(f245,plain,
    ( spl4_13
  <=> r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f296,plain,
    ( spl4_17
  <=> r2_hidden(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f360,plain,
    ( spl4_21
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f460,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | spl4_17
    | spl4_21 ),
    inference(unit_resulting_resolution,[],[f362,f298,f68])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f298,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f296])).

fof(f362,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f360])).

fof(f363,plain,
    ( ~ spl4_21
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f354,f303,f360])).

fof(f303,plain,
    ( spl4_18
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f354,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f305,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f305,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f303])).

fof(f353,plain,
    ( spl4_13
    | spl4_2
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f328,f115,f80,f74,f245])).

fof(f74,plain,
    ( spl4_2
  <=> r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f80,plain,
    ( spl4_3
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f115,plain,
    ( spl4_6
  <=> v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f328,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f82,f76,f117,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f117,plain,
    ( v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f76,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f82,plain,
    ( v3_ordinal1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f309,plain,
    ( spl4_18
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f308,f258,f85,f80,f303])).

fof(f85,plain,
    ( spl4_4
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f258,plain,
    ( spl4_14
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f308,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f307,f87])).

fof(f87,plain,
    ( v3_ordinal1(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f307,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f301,f82])).

fof(f301,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_14 ),
    inference(resolution,[],[f260,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f260,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f258])).

fof(f299,plain,
    ( ~ spl4_17
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f290,f140,f296])).

fof(f140,plain,
    ( spl4_9
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f290,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f141,f55])).

fof(f141,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f140])).

fof(f272,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_4
    | spl4_7 ),
    inference(avatar_split_clause,[],[f271,f130,f85,f80,f258])).

fof(f130,plain,
    ( spl4_7
  <=> r1_ordinal1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f271,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl4_3
    | ~ spl4_4
    | spl4_7 ),
    inference(subsumption_resolution,[],[f270,f87])).

fof(f270,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_3
    | spl4_7 ),
    inference(subsumption_resolution,[],[f255,f82])).

fof(f255,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl4_7 ),
    inference(resolution,[],[f131,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f131,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f225,plain,
    ( ~ spl4_11
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f220,f70,f153])).

fof(f153,plain,
    ( spl4_11
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f70,plain,
    ( spl4_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f220,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f71,f55])).

fof(f71,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f223,plain,
    ( spl4_9
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f217,f70,f140])).

fof(f217,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f71,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f210,plain,
    ( ~ spl4_6
    | spl4_8
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f209,f80,f74,f135,f115])).

fof(f135,plain,
    ( spl4_8
  <=> r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f209,plain,
    ( r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f205,f82])).

fof(f205,plain,
    ( r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f75,f48])).

fof(f75,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f204,plain,
    ( spl4_11
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f203,f130,f85,f80,f153])).

fof(f203,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f202,f82])).

fof(f202,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f200,f87])).

fof(f200,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f132,f48])).

fof(f132,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f195,plain,
    ( ~ spl4_8
    | spl4_1 ),
    inference(avatar_split_clause,[],[f187,f70,f135])).

fof(f187,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f64,f72,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f72,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f64,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f43,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f118,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f104,f85,f115])).

fof(f104,plain,
    ( v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f87,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f45,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f88,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f39,f85])).

fof(f39,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).

fof(f25,plain,
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

fof(f26,plain,
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

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f83,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f40,f80])).

fof(f40,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f63,f74,f70])).

fof(f63,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f41,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f62,f74,f70])).

fof(f62,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f42,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:47:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (18784)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.47  % (18792)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.48  % (18792)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f491,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f77,f78,f83,f88,f118,f195,f204,f210,f223,f225,f272,f299,f309,f353,f363,f484])).
% 0.21/0.48  fof(f484,plain,(
% 0.21/0.48    ~spl4_13 | spl4_17 | spl4_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f460,f360,f296,f245])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    spl4_13 <=> r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.48  fof(f296,plain,(
% 0.21/0.48    spl4_17 <=> r2_hidden(sK1,k1_tarski(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.48  fof(f360,plain,(
% 0.21/0.48    spl4_21 <=> r2_hidden(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.48  fof(f460,plain,(
% 0.21/0.48    ~r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | (spl4_17 | spl4_21)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f362,f298,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(equality_resolution,[],[f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.48    inference(rectify,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.48    inference(flattening,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.48    inference(nnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.48  fof(f298,plain,(
% 0.21/0.48    ~r2_hidden(sK1,k1_tarski(sK0)) | spl4_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f296])).
% 0.21/0.48  fof(f362,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK0) | spl4_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f360])).
% 0.21/0.48  fof(f363,plain,(
% 0.21/0.48    ~spl4_21 | ~spl4_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f354,f303,f360])).
% 0.21/0.48  fof(f303,plain,(
% 0.21/0.48    spl4_18 <=> r1_tarski(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.48  fof(f354,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK0) | ~spl4_18),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f305,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.48  fof(f305,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1) | ~spl4_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f303])).
% 0.21/0.48  fof(f353,plain,(
% 0.21/0.48    spl4_13 | spl4_2 | ~spl4_3 | ~spl4_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f328,f115,f80,f74,f245])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl4_2 <=> r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl4_3 <=> v3_ordinal1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    spl4_6 <=> v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f328,plain,(
% 0.21/0.48    r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | (spl4_2 | ~spl4_3 | ~spl4_6)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f82,f76,f117,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f115])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ~r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    v3_ordinal1(sK1) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f309,plain,(
% 0.21/0.48    spl4_18 | ~spl4_3 | ~spl4_4 | ~spl4_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f308,f258,f85,f80,f303])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl4_4 <=> v3_ordinal1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    spl4_14 <=> r1_ordinal1(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.48  fof(f308,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1) | (~spl4_3 | ~spl4_4 | ~spl4_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f307,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    v3_ordinal1(sK0) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f85])).
% 0.21/0.48  fof(f307,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | (~spl4_3 | ~spl4_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f301,f82])).
% 0.21/0.48  fof(f301,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~spl4_14),
% 0.21/0.48    inference(resolution,[],[f260,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.48  fof(f260,plain,(
% 0.21/0.48    r1_ordinal1(sK0,sK1) | ~spl4_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f258])).
% 0.21/0.48  fof(f299,plain,(
% 0.21/0.48    ~spl4_17 | ~spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f290,f140,f296])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    spl4_9 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f290,plain,(
% 0.21/0.48    ~r2_hidden(sK1,k1_tarski(sK0)) | ~spl4_9),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f141,f55])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    r1_tarski(k1_tarski(sK0),sK1) | ~spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f140])).
% 0.21/0.48  fof(f272,plain,(
% 0.21/0.48    spl4_14 | ~spl4_3 | ~spl4_4 | spl4_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f271,f130,f85,f80,f258])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    spl4_7 <=> r1_ordinal1(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f271,plain,(
% 0.21/0.48    r1_ordinal1(sK0,sK1) | (~spl4_3 | ~spl4_4 | spl4_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f270,f87])).
% 0.21/0.48  fof(f270,plain,(
% 0.21/0.48    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0) | (~spl4_3 | spl4_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f255,f82])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl4_7),
% 0.21/0.48    inference(resolution,[],[f131,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ~r1_ordinal1(sK1,sK0) | spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f130])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    ~spl4_11 | ~spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f220,f70,f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    spl4_11 <=> r1_tarski(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl4_1 <=> r2_hidden(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    ~r1_tarski(sK1,sK0) | ~spl4_1),
% 0.21/0.48    inference(resolution,[],[f71,f55])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    r2_hidden(sK0,sK1) | ~spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f70])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    spl4_9 | ~spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f217,f70,f140])).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    r1_tarski(k1_tarski(sK0),sK1) | ~spl4_1),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f71,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    ~spl4_6 | spl4_8 | ~spl4_2 | ~spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f209,f80,f74,f135,f115])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    spl4_8 <=> r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | (~spl4_2 | ~spl4_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f205,f82])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f75,f48])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    spl4_11 | ~spl4_3 | ~spl4_4 | ~spl4_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f203,f130,f85,f80,f153])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    r1_tarski(sK1,sK0) | (~spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f202,f82])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1) | (~spl4_4 | ~spl4_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f200,f87])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | ~spl4_7),
% 0.21/0.48    inference(resolution,[],[f132,f48])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    r1_ordinal1(sK1,sK0) | ~spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f130])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    ~spl4_8 | spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f187,f70,f135])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ~r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | spl4_1),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f64,f72,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ~r2_hidden(sK0,sK1) | spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f70])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f43,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    spl4_6 | ~spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f104,f85,f115])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | ~spl4_4),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f87,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f45,f44])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f39,f85])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    v3_ordinal1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f11])).
% 0.21/0.49  fof(f11,conjecture,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f40,f80])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    v3_ordinal1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl4_1 | spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f63,f74,f70])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | r2_hidden(sK0,sK1)),
% 0.21/0.49    inference(definition_unfolding,[],[f41,f44])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ~spl4_1 | ~spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f62,f74,f70])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ~r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.49    inference(definition_unfolding,[],[f42,f44])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (18792)------------------------------
% 0.21/0.49  % (18792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18792)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (18792)Memory used [KB]: 6396
% 0.21/0.49  % (18792)Time elapsed: 0.082 s
% 0.21/0.49  % (18792)------------------------------
% 0.21/0.49  % (18792)------------------------------
% 0.21/0.49  % (18766)Success in time 0.132 s
%------------------------------------------------------------------------------
