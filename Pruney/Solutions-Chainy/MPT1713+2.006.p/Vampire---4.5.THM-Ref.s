%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 280 expanded)
%              Number of leaves         :   39 ( 122 expanded)
%              Depth                    :    8
%              Number of atoms          :  490 (1221 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1439,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f121,f126,f136,f141,f146,f210,f214,f226,f243,f262,f267,f272,f284,f332,f428,f512,f738,f822,f1102,f1436])).

fof(f1436,plain,
    ( spl8_64
    | ~ spl8_28
    | ~ spl8_76 ),
    inference(avatar_split_clause,[],[f1424,f818,f329,f728])).

fof(f728,plain,
    ( spl8_64
  <=> r2_hidden(sK3(u1_struct_0(sK1)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f329,plain,
    ( spl8_28
  <=> r2_hidden(sK3(u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f818,plain,
    ( spl8_76
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).

fof(f1424,plain,
    ( r2_hidden(sK3(u1_struct_0(sK1)),u1_struct_0(sK2))
    | ~ spl8_28
    | ~ spl8_76 ),
    inference(unit_resulting_resolution,[],[f331,f820,f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f820,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl8_76 ),
    inference(avatar_component_clause,[],[f818])).

fof(f331,plain,
    ( r2_hidden(sK3(u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f329])).

fof(f1102,plain,
    ( ~ spl8_64
    | ~ spl8_20
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f1090,f329,f264,f728])).

fof(f264,plain,
    ( spl8_20
  <=> r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f1090,plain,
    ( ~ r2_hidden(sK3(u1_struct_0(sK1)),u1_struct_0(sK2))
    | ~ spl8_20
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f331,f342])).

fof(f342,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ r2_hidden(X0,u1_struct_0(sK1)) )
    | ~ spl8_20 ),
    inference(resolution,[],[f266,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f266,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f264])).

fof(f822,plain,
    ( spl8_76
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f783,f361,f818])).

fof(f361,plain,
    ( spl8_30
  <=> r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f783,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl8_30 ),
    inference(resolution,[],[f363,f107])).

fof(f107,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK7(X0,X1),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r1_tarski(sK7(X0,X1),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f61,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK7(X0,X1),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( r1_tarski(sK7(X0,X1),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f363,plain,
    ( r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f361])).

fof(f738,plain,
    ( ~ spl8_64
    | ~ spl8_21
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f711,f329,f269,f728])).

fof(f269,plain,
    ( spl8_21
  <=> r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f711,plain,
    ( ~ r2_hidden(sK3(u1_struct_0(sK1)),u1_struct_0(sK2))
    | ~ spl8_21
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f271,f331,f87])).

fof(f271,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f269])).

fof(f512,plain,
    ( spl8_30
    | ~ spl8_22
    | spl8_29 ),
    inference(avatar_split_clause,[],[f501,f357,f281,f361])).

fof(f281,plain,
    ( spl8_22
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f357,plain,
    ( spl8_29
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f501,plain,
    ( r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_22
    | spl8_29 ),
    inference(unit_resulting_resolution,[],[f283,f358,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f358,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)))
    | spl8_29 ),
    inference(avatar_component_clause,[],[f357])).

fof(f283,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f281])).

fof(f428,plain,(
    ~ spl8_29 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f73,f365,f106])).

fof(f106,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f365,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f359,f81])).

fof(f81,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f359,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f357])).

fof(f73,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f332,plain,
    ( spl8_28
    | spl8_19 ),
    inference(avatar_split_clause,[],[f325,f259,f329])).

fof(f259,plain,
    ( spl8_19
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f325,plain,
    ( r2_hidden(sK3(u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl8_19 ),
    inference(unit_resulting_resolution,[],[f261,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f261,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl8_19 ),
    inference(avatar_component_clause,[],[f259])).

fof(f284,plain,
    ( spl8_22
    | ~ spl8_3
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f273,f178,f118,f281])).

fof(f118,plain,
    ( spl8_3
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f178,plain,
    ( spl8_13
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f273,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_3
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f120,f179,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f179,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f178])).

fof(f120,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f272,plain,
    ( spl8_21
    | ~ spl8_1
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f246,f171,f167,f109,f269])).

fof(f109,plain,
    ( spl8_1
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f167,plain,
    ( spl8_11
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f171,plain,
    ( spl8_12
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f246,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f168,f111,f172,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f172,plain,
    ( l1_struct_0(sK1)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f111,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f168,plain,
    ( l1_struct_0(sK2)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f167])).

fof(f267,plain,
    ( spl8_20
    | ~ spl8_2
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f247,f171,f167,f113,f264])).

fof(f113,plain,
    ( spl8_2
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f247,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl8_2
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f168,f115,f172,f75])).

fof(f115,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f262,plain,
    ( ~ spl8_19
    | spl8_7
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f248,f171,f138,f259])).

fof(f138,plain,
    ( spl8_7
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f248,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl8_7
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f140,f172,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f140,plain,
    ( ~ v2_struct_0(sK1)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f243,plain,
    ( ~ spl8_14
    | spl8_12 ),
    inference(avatar_split_clause,[],[f241,f171,f182])).

fof(f182,plain,
    ( spl8_14
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f241,plain,
    ( ~ l1_pre_topc(sK1)
    | spl8_12 ),
    inference(resolution,[],[f173,f77])).

fof(f77,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f173,plain,
    ( ~ l1_struct_0(sK1)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f226,plain,
    ( spl8_14
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f225,f143,f133,f182])).

fof(f133,plain,
    ( spl8_6
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f143,plain,
    ( spl8_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f225,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f218,f145])).

fof(f145,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f218,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_6 ),
    inference(resolution,[],[f135,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f135,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f214,plain,
    ( ~ spl8_13
    | spl8_11 ),
    inference(avatar_split_clause,[],[f212,f167,f178])).

fof(f212,plain,
    ( ~ l1_pre_topc(sK2)
    | spl8_11 ),
    inference(resolution,[],[f169,f77])).

fof(f169,plain,
    ( ~ l1_struct_0(sK2)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f167])).

fof(f210,plain,
    ( spl8_13
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f209,f143,f123,f178])).

fof(f123,plain,
    ( spl8_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f209,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f202,f145])).

fof(f202,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_4 ),
    inference(resolution,[],[f125,f78])).

fof(f125,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f146,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f66,f143])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( r1_tsep_1(sK2,sK1)
      | r1_tsep_1(sK1,sK2) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( r1_tsep_1(X2,X1)
                  | r1_tsep_1(X1,X2) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( r1_tsep_1(X2,X1)
              | r1_tsep_1(X1,X2) )
            & m1_pre_topc(X1,X2)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( r1_tsep_1(X2,sK1)
            | r1_tsep_1(sK1,X2) )
          & m1_pre_topc(sK1,X2)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ( r1_tsep_1(X2,sK1)
          | r1_tsep_1(sK1,X2) )
        & m1_pre_topc(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ( r1_tsep_1(sK2,sK1)
        | r1_tsep_1(sK1,sK2) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f141,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f67,f138])).

fof(f67,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f136,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f68,f133])).

fof(f68,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f126,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f70,f123])).

fof(f70,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f121,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f71,f118])).

fof(f71,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f116,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f72,f113,f109])).

fof(f72,plain,
    ( r1_tsep_1(sK2,sK1)
    | r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:44:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (24153)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (24169)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (24149)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (24154)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (24154)Refutation not found, incomplete strategy% (24154)------------------------------
% 0.22/0.53  % (24154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (24154)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (24154)Memory used [KB]: 10746
% 0.22/0.53  % (24154)Time elapsed: 0.107 s
% 0.22/0.53  % (24154)------------------------------
% 0.22/0.53  % (24154)------------------------------
% 0.22/0.53  % (24145)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (24170)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (24168)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (24162)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (24157)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (24164)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (24147)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (24146)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (24148)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (24144)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (24151)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (24173)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (24158)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (24163)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (24156)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (24160)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (24165)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (24165)Refutation not found, incomplete strategy% (24165)------------------------------
% 0.22/0.56  % (24165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (24165)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (24165)Memory used [KB]: 1663
% 0.22/0.56  % (24165)Time elapsed: 0.110 s
% 0.22/0.56  % (24165)------------------------------
% 0.22/0.56  % (24165)------------------------------
% 0.22/0.56  % (24155)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (24169)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f1439,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f116,f121,f126,f136,f141,f146,f210,f214,f226,f243,f262,f267,f272,f284,f332,f428,f512,f738,f822,f1102,f1436])).
% 0.22/0.56  fof(f1436,plain,(
% 0.22/0.56    spl8_64 | ~spl8_28 | ~spl8_76),
% 0.22/0.56    inference(avatar_split_clause,[],[f1424,f818,f329,f728])).
% 0.22/0.56  fof(f728,plain,(
% 0.22/0.56    spl8_64 <=> r2_hidden(sK3(u1_struct_0(sK1)),u1_struct_0(sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).
% 0.22/0.56  fof(f329,plain,(
% 0.22/0.56    spl8_28 <=> r2_hidden(sK3(u1_struct_0(sK1)),u1_struct_0(sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.22/0.56  fof(f818,plain,(
% 0.22/0.56    spl8_76 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).
% 0.22/0.56  fof(f1424,plain,(
% 0.22/0.56    r2_hidden(sK3(u1_struct_0(sK1)),u1_struct_0(sK2)) | (~spl8_28 | ~spl8_76)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f331,f820,f95])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f57,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(rectify,[],[f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.56  fof(f820,plain,(
% 0.22/0.56    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl8_76),
% 0.22/0.56    inference(avatar_component_clause,[],[f818])).
% 0.22/0.56  fof(f331,plain,(
% 0.22/0.56    r2_hidden(sK3(u1_struct_0(sK1)),u1_struct_0(sK1)) | ~spl8_28),
% 0.22/0.56    inference(avatar_component_clause,[],[f329])).
% 0.22/0.56  fof(f1102,plain,(
% 0.22/0.56    ~spl8_64 | ~spl8_20 | ~spl8_28),
% 0.22/0.56    inference(avatar_split_clause,[],[f1090,f329,f264,f728])).
% 0.22/0.56  fof(f264,plain,(
% 0.22/0.56    spl8_20 <=> r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.22/0.56  fof(f1090,plain,(
% 0.22/0.56    ~r2_hidden(sK3(u1_struct_0(sK1)),u1_struct_0(sK2)) | (~spl8_20 | ~spl8_28)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f331,f342])).
% 0.22/0.56  fof(f342,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,u1_struct_0(sK1))) ) | ~spl8_20),
% 0.22/0.56    inference(resolution,[],[f266,f87])).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.56    inference(rectify,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.56  fof(f266,plain,(
% 0.22/0.56    r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl8_20),
% 0.22/0.56    inference(avatar_component_clause,[],[f264])).
% 0.22/0.56  fof(f822,plain,(
% 0.22/0.56    spl8_76 | ~spl8_30),
% 0.22/0.56    inference(avatar_split_clause,[],[f783,f361,f818])).
% 0.22/0.56  fof(f361,plain,(
% 0.22/0.56    spl8_30 <=> r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.22/0.56  fof(f783,plain,(
% 0.22/0.56    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl8_30),
% 0.22/0.56    inference(resolution,[],[f363,f107])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(equality_resolution,[],[f98])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK7(X0,X1),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r1_tarski(sK7(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f61,f62])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK7(X0,X1),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r1_tarski(sK7(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.56    inference(rectify,[],[f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.56  fof(f363,plain,(
% 0.22/0.56    r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl8_30),
% 0.22/0.56    inference(avatar_component_clause,[],[f361])).
% 0.22/0.56  fof(f738,plain,(
% 0.22/0.56    ~spl8_64 | ~spl8_21 | ~spl8_28),
% 0.22/0.56    inference(avatar_split_clause,[],[f711,f329,f269,f728])).
% 0.22/0.56  fof(f269,plain,(
% 0.22/0.56    spl8_21 <=> r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.22/0.56  fof(f711,plain,(
% 0.22/0.56    ~r2_hidden(sK3(u1_struct_0(sK1)),u1_struct_0(sK2)) | (~spl8_21 | ~spl8_28)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f271,f331,f87])).
% 0.22/0.56  fof(f271,plain,(
% 0.22/0.56    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl8_21),
% 0.22/0.56    inference(avatar_component_clause,[],[f269])).
% 0.22/0.56  fof(f512,plain,(
% 0.22/0.56    spl8_30 | ~spl8_22 | spl8_29),
% 0.22/0.56    inference(avatar_split_clause,[],[f501,f357,f281,f361])).
% 0.22/0.56  fof(f281,plain,(
% 0.22/0.56    spl8_22 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.22/0.56  fof(f357,plain,(
% 0.22/0.56    spl8_29 <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.22/0.56  fof(f501,plain,(
% 0.22/0.56    r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) | (~spl8_22 | spl8_29)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f283,f358,f88])).
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.56    inference(flattening,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.56  fof(f358,plain,(
% 0.22/0.56    ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) | spl8_29),
% 0.22/0.56    inference(avatar_component_clause,[],[f357])).
% 0.22/0.56  fof(f283,plain,(
% 0.22/0.56    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl8_22),
% 0.22/0.56    inference(avatar_component_clause,[],[f281])).
% 0.22/0.56  fof(f428,plain,(
% 0.22/0.56    ~spl8_29),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f407])).
% 0.22/0.56  fof(f407,plain,(
% 0.22/0.56    $false | ~spl8_29),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f73,f365,f106])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f99])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f63])).
% 0.22/0.56  fof(f365,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl8_29),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f359,f81])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.56    inference(rectify,[],[f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.56    inference(nnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.56  fof(f359,plain,(
% 0.22/0.56    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) | ~spl8_29),
% 0.22/0.56    inference(avatar_component_clause,[],[f357])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.56  fof(f332,plain,(
% 0.22/0.56    spl8_28 | spl8_19),
% 0.22/0.56    inference(avatar_split_clause,[],[f325,f259,f329])).
% 0.22/0.56  fof(f259,plain,(
% 0.22/0.56    spl8_19 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.22/0.56  fof(f325,plain,(
% 0.22/0.56    r2_hidden(sK3(u1_struct_0(sK1)),u1_struct_0(sK1)) | spl8_19),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f261,f82])).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f49])).
% 0.22/0.56  fof(f261,plain,(
% 0.22/0.56    ~v1_xboole_0(u1_struct_0(sK1)) | spl8_19),
% 0.22/0.56    inference(avatar_component_clause,[],[f259])).
% 0.22/0.56  fof(f284,plain,(
% 0.22/0.56    spl8_22 | ~spl8_3 | ~spl8_13),
% 0.22/0.56    inference(avatar_split_clause,[],[f273,f178,f118,f281])).
% 0.22/0.56  fof(f118,plain,(
% 0.22/0.56    spl8_3 <=> m1_pre_topc(sK1,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.56  fof(f178,plain,(
% 0.22/0.56    spl8_13 <=> l1_pre_topc(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.22/0.56  fof(f273,plain,(
% 0.22/0.56    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) | (~spl8_3 | ~spl8_13)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f120,f179,f79])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.56  fof(f179,plain,(
% 0.22/0.56    l1_pre_topc(sK2) | ~spl8_13),
% 0.22/0.56    inference(avatar_component_clause,[],[f178])).
% 0.22/0.56  fof(f120,plain,(
% 0.22/0.56    m1_pre_topc(sK1,sK2) | ~spl8_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f118])).
% 0.22/0.56  fof(f272,plain,(
% 0.22/0.56    spl8_21 | ~spl8_1 | ~spl8_11 | ~spl8_12),
% 0.22/0.56    inference(avatar_split_clause,[],[f246,f171,f167,f109,f269])).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    spl8_1 <=> r1_tsep_1(sK1,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.56  fof(f167,plain,(
% 0.22/0.56    spl8_11 <=> l1_struct_0(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.22/0.56  fof(f171,plain,(
% 0.22/0.56    spl8_12 <=> l1_struct_0(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.22/0.56  fof(f246,plain,(
% 0.22/0.56    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (~spl8_1 | ~spl8_11 | ~spl8_12)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f168,f111,f172,f75])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.56    inference(nnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,axiom,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.22/0.56  fof(f172,plain,(
% 0.22/0.56    l1_struct_0(sK1) | ~spl8_12),
% 0.22/0.56    inference(avatar_component_clause,[],[f171])).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    r1_tsep_1(sK1,sK2) | ~spl8_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f109])).
% 0.22/0.56  fof(f168,plain,(
% 0.22/0.56    l1_struct_0(sK2) | ~spl8_11),
% 0.22/0.56    inference(avatar_component_clause,[],[f167])).
% 0.22/0.56  fof(f267,plain,(
% 0.22/0.56    spl8_20 | ~spl8_2 | ~spl8_11 | ~spl8_12),
% 0.22/0.56    inference(avatar_split_clause,[],[f247,f171,f167,f113,f264])).
% 0.22/0.56  fof(f113,plain,(
% 0.22/0.56    spl8_2 <=> r1_tsep_1(sK2,sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.56  fof(f247,plain,(
% 0.22/0.56    r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | (~spl8_2 | ~spl8_11 | ~spl8_12)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f168,f115,f172,f75])).
% 0.22/0.56  fof(f115,plain,(
% 0.22/0.56    r1_tsep_1(sK2,sK1) | ~spl8_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f113])).
% 0.22/0.56  fof(f262,plain,(
% 0.22/0.56    ~spl8_19 | spl8_7 | ~spl8_12),
% 0.22/0.56    inference(avatar_split_clause,[],[f248,f171,f138,f259])).
% 0.22/0.56  fof(f138,plain,(
% 0.22/0.56    spl8_7 <=> v2_struct_0(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.56  fof(f248,plain,(
% 0.22/0.56    ~v1_xboole_0(u1_struct_0(sK1)) | (spl8_7 | ~spl8_12)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f140,f172,f80])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,axiom,(
% 0.22/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.56  fof(f140,plain,(
% 0.22/0.56    ~v2_struct_0(sK1) | spl8_7),
% 0.22/0.56    inference(avatar_component_clause,[],[f138])).
% 0.22/0.56  fof(f243,plain,(
% 0.22/0.56    ~spl8_14 | spl8_12),
% 0.22/0.56    inference(avatar_split_clause,[],[f241,f171,f182])).
% 0.22/0.56  fof(f182,plain,(
% 0.22/0.56    spl8_14 <=> l1_pre_topc(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.22/0.56  fof(f241,plain,(
% 0.22/0.56    ~l1_pre_topc(sK1) | spl8_12),
% 0.22/0.56    inference(resolution,[],[f173,f77])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.56  fof(f173,plain,(
% 0.22/0.56    ~l1_struct_0(sK1) | spl8_12),
% 0.22/0.56    inference(avatar_component_clause,[],[f171])).
% 0.22/0.56  fof(f226,plain,(
% 0.22/0.56    spl8_14 | ~spl8_6 | ~spl8_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f225,f143,f133,f182])).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    spl8_6 <=> m1_pre_topc(sK1,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.56  fof(f143,plain,(
% 0.22/0.56    spl8_8 <=> l1_pre_topc(sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.56  fof(f225,plain,(
% 0.22/0.56    l1_pre_topc(sK1) | (~spl8_6 | ~spl8_8)),
% 0.22/0.56    inference(subsumption_resolution,[],[f218,f145])).
% 0.22/0.56  fof(f145,plain,(
% 0.22/0.56    l1_pre_topc(sK0) | ~spl8_8),
% 0.22/0.56    inference(avatar_component_clause,[],[f143])).
% 0.22/0.56  fof(f218,plain,(
% 0.22/0.56    l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~spl8_6),
% 0.22/0.56    inference(resolution,[],[f135,f78])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.56  fof(f135,plain,(
% 0.22/0.56    m1_pre_topc(sK1,sK0) | ~spl8_6),
% 0.22/0.56    inference(avatar_component_clause,[],[f133])).
% 0.22/0.56  fof(f214,plain,(
% 0.22/0.56    ~spl8_13 | spl8_11),
% 0.22/0.56    inference(avatar_split_clause,[],[f212,f167,f178])).
% 0.22/0.56  fof(f212,plain,(
% 0.22/0.56    ~l1_pre_topc(sK2) | spl8_11),
% 0.22/0.56    inference(resolution,[],[f169,f77])).
% 0.22/0.56  fof(f169,plain,(
% 0.22/0.56    ~l1_struct_0(sK2) | spl8_11),
% 0.22/0.56    inference(avatar_component_clause,[],[f167])).
% 0.22/0.56  fof(f210,plain,(
% 0.22/0.56    spl8_13 | ~spl8_4 | ~spl8_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f209,f143,f123,f178])).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    spl8_4 <=> m1_pre_topc(sK2,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.56  fof(f209,plain,(
% 0.22/0.56    l1_pre_topc(sK2) | (~spl8_4 | ~spl8_8)),
% 0.22/0.56    inference(subsumption_resolution,[],[f202,f145])).
% 0.22/0.56  fof(f202,plain,(
% 0.22/0.56    l1_pre_topc(sK2) | ~l1_pre_topc(sK0) | ~spl8_4),
% 0.22/0.56    inference(resolution,[],[f125,f78])).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    m1_pre_topc(sK2,sK0) | ~spl8_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f123])).
% 0.22/0.56  fof(f146,plain,(
% 0.22/0.56    spl8_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f66,f143])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    l1_pre_topc(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    (((r1_tsep_1(sK2,sK1) | r1_tsep_1(sK1,sK2)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f43,f42,f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : ((r1_tsep_1(X2,sK1) | r1_tsep_1(sK1,X2)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ? [X2] : ((r1_tsep_1(X2,sK1) | r1_tsep_1(sK1,X2)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => ((r1_tsep_1(sK2,sK1) | r1_tsep_1(sK1,sK2)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.22/0.56    inference(pure_predicate_removal,[],[f20])).
% 0.22/0.56  fof(f20,negated_conjecture,(
% 0.22/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.22/0.56    inference(negated_conjecture,[],[f19])).
% 0.22/0.56  fof(f19,conjecture,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).
% 0.22/0.56  fof(f141,plain,(
% 0.22/0.56    ~spl8_7),
% 0.22/0.56    inference(avatar_split_clause,[],[f67,f138])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ~v2_struct_0(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f44])).
% 0.22/0.56  fof(f136,plain,(
% 0.22/0.56    spl8_6),
% 0.22/0.56    inference(avatar_split_clause,[],[f68,f133])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    m1_pre_topc(sK1,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f44])).
% 0.22/0.56  fof(f126,plain,(
% 0.22/0.56    spl8_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f70,f123])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    m1_pre_topc(sK2,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f44])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    spl8_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f71,f118])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    m1_pre_topc(sK1,sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f44])).
% 0.22/0.56  fof(f116,plain,(
% 0.22/0.56    spl8_1 | spl8_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f72,f113,f109])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    r1_tsep_1(sK2,sK1) | r1_tsep_1(sK1,sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f44])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (24169)------------------------------
% 0.22/0.56  % (24169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (24169)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (24169)Memory used [KB]: 7036
% 0.22/0.56  % (24169)Time elapsed: 0.136 s
% 0.22/0.56  % (24169)------------------------------
% 0.22/0.56  % (24169)------------------------------
% 0.22/0.57  % (24143)Success in time 0.198 s
%------------------------------------------------------------------------------
