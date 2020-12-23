%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0718+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:31 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 170 expanded)
%              Number of leaves         :   22 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  433 ( 932 expanded)
%              Number of equality atoms :   12 (  68 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f62,f67,f72,f76,f80,f96,f100,f114,f144,f150,f165])).

fof(f165,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_16
    | ~ spl4_21 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_16
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f163,f41])).

fof(f41,plain,
    ( ~ v2_relat_1(sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_1
  <=> v2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f163,plain,
    ( v2_relat_1(sK1)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_16
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f162,f51])).

fof(f51,plain,
    ( v5_funct_1(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_3
  <=> v5_funct_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f162,plain,
    ( ~ v5_funct_1(sK0,sK1)
    | v2_relat_1(sK1)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_16
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f161,f61])).

fof(f61,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f161,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v5_funct_1(sK0,sK1)
    | v2_relat_1(sK1)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_16
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f160,f56])).

fof(f56,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl4_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f160,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v5_funct_1(sK0,sK1)
    | v2_relat_1(sK1)
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_16
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f159,f71])).

fof(f71,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_7
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f159,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v5_funct_1(sK0,sK1)
    | v2_relat_1(sK1)
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f152,f66])).

fof(f66,plain,
    ( v1_funct_1(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_6
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f152,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v5_funct_1(sK0,sK1)
    | v2_relat_1(sK1)
    | ~ spl4_16
    | ~ spl4_21 ),
    inference(resolution,[],[f149,f113])).

fof(f113,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_16
  <=> r2_hidden(sK2(sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(X1),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v5_funct_1(X0,X1)
        | v2_relat_1(X1) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_21
  <=> ! [X1,X0] :
        ( ~ v5_funct_1(X0,X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(sK2(X1),k1_relat_1(X0))
        | v2_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f150,plain,
    ( spl4_21
    | ~ spl4_8
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f146,f142,f74,f148])).

fof(f74,plain,
    ( spl4_8
  <=> ! [X0] :
        ( v2_relat_1(X0)
        | v1_xboole_0(k1_funct_1(X0,sK2(X0)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f142,plain,
    ( spl4_20
  <=> ! [X3,X2,X4] :
        ( ~ r2_hidden(X2,k1_relat_1(X3))
        | ~ v5_funct_1(X3,X4)
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_xboole_0(k1_funct_1(X4,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ v5_funct_1(X0,X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(sK2(X1),k1_relat_1(X0))
        | v2_relat_1(X1) )
    | ~ spl4_8
    | ~ spl4_20 ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ v5_funct_1(X0,X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(sK2(X1),k1_relat_1(X0))
        | v2_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_8
    | ~ spl4_20 ),
    inference(resolution,[],[f143,f75])).

fof(f75,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_funct_1(X0,sK2(X0)))
        | v2_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f143,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_xboole_0(k1_funct_1(X4,X2))
        | ~ v5_funct_1(X3,X4)
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ r2_hidden(X2,k1_relat_1(X3)) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f142])).

fof(f144,plain,
    ( spl4_20
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f139,f98,f94,f142])).

fof(f94,plain,
    ( spl4_13
  <=> ! [X1,X3,X0] :
        ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
        | ~ r2_hidden(X3,k1_relat_1(X1))
        | ~ v5_funct_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f98,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f139,plain,
    ( ! [X4,X2,X3] :
        ( ~ r2_hidden(X2,k1_relat_1(X3))
        | ~ v5_funct_1(X3,X4)
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_xboole_0(k1_funct_1(X4,X2)) )
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(resolution,[],[f95,f99])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ v1_xboole_0(X1) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f98])).

fof(f95,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
        | ~ r2_hidden(X3,k1_relat_1(X1))
        | ~ v5_funct_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f94])).

fof(f114,plain,
    ( spl4_16
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f109,f78,f59,f54,f44,f39,f111])).

fof(f44,plain,
    ( spl4_2
  <=> k1_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f78,plain,
    ( spl4_9
  <=> ! [X0] :
        ( v2_relat_1(X0)
        | r2_hidden(sK2(X0),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f109,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f108,f61])).

fof(f108,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f107,f56])).

fof(f107,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f102,f41])).

fof(f102,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | v2_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(superposition,[],[f79,f46])).

fof(f46,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f79,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),k1_relat_1(X0))
        | v2_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f100,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f37,f98])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f96,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f34,f94])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
      | ~ r2_hidden(X3,k1_relat_1(X1))
      | ~ v5_funct_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1)))
                & r2_hidden(sK3(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

% (24748)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1)))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(f80,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f32,f78])).

fof(f32,plain,(
    ! [X0] :
      ( v2_relat_1(X0)
      | r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ( v1_xboole_0(k1_funct_1(X0,sK2(X0)))
            & r2_hidden(sK2(X0),k1_relat_1(X0)) ) )
        & ( ! [X2] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X2))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(k1_funct_1(X0,X1))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( v1_xboole_0(k1_funct_1(X0,sK2(X0)))
        & r2_hidden(sK2(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ? [X1] :
              ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X2] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X2))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ? [X1] :
              ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X1))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_relat_1(X0)
      <=> ! [X1] :
            ~ ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_funct_1)).

fof(f76,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f33,f74])).

fof(f33,plain,(
    ! [X0] :
      ( v2_relat_1(X0)
      | v1_xboole_0(k1_funct_1(X0,sK2(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f24,f69])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ v2_relat_1(sK1)
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v5_funct_1(sK0,sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_relat_1(X1)
            & k1_relat_1(X0) = k1_relat_1(X1)
            & v5_funct_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(sK0)
          & v5_funct_1(sK0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ~ v2_relat_1(X1)
        & k1_relat_1(X1) = k1_relat_1(sK0)
        & v5_funct_1(sK0,X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_relat_1(sK1)
      & k1_relat_1(sK0) = k1_relat_1(sK1)
      & v5_funct_1(sK0,sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k1_relat_1(X0) = k1_relat_1(X1)
                & v5_funct_1(X0,X1) )
             => v2_relat_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k1_relat_1(X1)
              & v5_funct_1(X0,X1) )
           => v2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_1)).

fof(f67,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f25,f64])).

fof(f25,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f27,f54])).

fof(f27,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f28,f49])).

fof(f28,plain,(
    v5_funct_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f29,f44])).

fof(f29,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f30,f39])).

fof(f30,plain,(
    ~ v2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

%------------------------------------------------------------------------------
