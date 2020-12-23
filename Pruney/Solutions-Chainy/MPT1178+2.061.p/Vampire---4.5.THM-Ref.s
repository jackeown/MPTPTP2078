%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 226 expanded)
%              Number of leaves         :   29 ( 100 expanded)
%              Depth                    :   10
%              Number of atoms          :  475 (1022 expanded)
%              Number of equality atoms :   74 ( 184 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f65,f69,f73,f77,f81,f85,f89,f97,f120,f127,f138,f150,f161,f172,f177])).

fof(f177,plain,
    ( ~ spl5_15
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f176,f133,f125,f118,f63,f148])).

fof(f148,plain,
    ( spl5_15
  <=> r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f63,plain,
    ( spl5_2
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f118,plain,
    ( spl5_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,X1))
        | m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f125,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f133,plain,
    ( spl5_12
  <=> k1_xboole_0 = k1_funct_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f176,plain,
    ( ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(resolution,[],[f175,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f175,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | ~ r2_hidden(X1,k4_orders_2(sK0,sK1)) )
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(resolution,[],[f173,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f173,plain,
    ( ! [X0] :
        ( r2_hidden(k1_xboole_0,X0)
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(superposition,[],[f129,f134])).

fof(f134,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,u1_struct_0(sK0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f129,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0)
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(resolution,[],[f128,f121])).

fof(f121,plain,
    ( ! [X0] :
        ( m2_orders_2(X0,sK0,sK1)
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(resolution,[],[f119,f64])).

fof(f64,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(X0,sK0,X1)
        | ~ r2_hidden(X0,k4_orders_2(sK0,X1)) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0) )
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(resolution,[],[f126,f64])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0)
        | ~ m2_orders_2(X0,sK0,X1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f172,plain,
    ( spl5_7
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_3
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f164,f159,f87,f63,f67,f71,f75,f79,f83])).

fof(f83,plain,
    ( spl5_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f79,plain,
    ( spl5_6
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f75,plain,
    ( spl5_5
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f71,plain,
    ( spl5_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f67,plain,
    ( spl5_3
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f87,plain,
    ( spl5_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f159,plain,
    ( spl5_17
  <=> k1_xboole_0 = k4_orders_2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f164,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_17 ),
    inference(superposition,[],[f54,f160])).

fof(f160,plain,
    ( k1_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f159])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

fof(f161,plain,
    ( ~ spl5_1
    | spl5_17
    | spl5_15 ),
    inference(avatar_split_clause,[],[f156,f148,f159,f59])).

fof(f59,plain,
    ( spl5_1
  <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f156,plain,
    ( k1_xboole_0 = k4_orders_2(sK0,sK1)
    | k1_xboole_0 != k3_tarski(k4_orders_2(sK0,sK1))
    | spl5_15 ),
    inference(resolution,[],[f149,f102])).

fof(f102,plain,(
    ! [X1] :
      ( r2_hidden(k1_xboole_0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 != k3_tarski(X1) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X1] :
      ( r2_hidden(k1_xboole_0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 != k3_tarski(X1)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f51,f98])).

fof(f98,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK4(X0)
      | k1_xboole_0 != k3_tarski(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f43,f51])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 != k3_tarski(X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK2(X0),X0)
          & k1_xboole_0 != sK2(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK2(X0),X0)
        & k1_xboole_0 != sK2(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f149,plain,
    ( ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f148])).

fof(f150,plain,
    ( ~ spl5_15
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f141,f136,f95,f148])).

fof(f95,plain,
    ( spl5_9
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f136,plain,
    ( spl5_13
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | k1_xboole_0 != k3_tarski(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f141,plain,
    ( ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(trivial_inequality_removal,[],[f140])).

fof(f140,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(superposition,[],[f137,f96])).

fof(f96,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f137,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_tarski(X0)
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f136])).

fof(f138,plain,
    ( spl5_12
    | spl5_13
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f130,f125,f118,f63,f136,f133])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | k1_xboole_0 != k3_tarski(X0)
        | k1_xboole_0 = k1_funct_1(sK1,u1_struct_0(sK0)) )
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(resolution,[],[f129,f43])).

fof(f127,plain,
    ( spl5_7
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | spl5_11
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f123,f67,f125,f71,f75,f79,f83])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f46,f68])).

fof(f68,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

fof(f120,plain,
    ( spl5_7
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | spl5_10
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f112,f67,f118,f71,f75,f79,f83])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,X1))
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(X0,sK0,X1)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f57,f68])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(X4,X0,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,X2)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK3(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK3(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK3(X0,X1,X2),X0,X1)
                    | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK3(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( m2_orders_2(sK3(X0,X1,X2),X0,X1)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X3] :
                    ( ( r2_hidden(X3,X2)
                      | ~ m2_orders_2(X3,X0,X1) )
                    & ( m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

fof(f97,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f93,f95])).

fof(f93,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(resolution,[],[f92,f42])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2(X0))
      | k1_xboole_0 = k3_tarski(X0) ) ),
    inference(resolution,[],[f45,f55])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = k3_tarski(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f89,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f41,f87])).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f85,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f34,f83])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

% (3201)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f25,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1))
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

fof(f81,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f35,f79])).

fof(f35,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f36,f75])).

fof(f36,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f37,f71])).

fof(f37,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f38,f67])).

fof(f38,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f39,f63])).

fof(f39,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f40,f59])).

fof(f40,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:23:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (3195)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (3200)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (3192)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (3195)Refutation not found, incomplete strategy% (3195)------------------------------
% 0.22/0.49  % (3195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (3195)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (3195)Memory used [KB]: 10618
% 0.22/0.49  % (3195)Time elapsed: 0.062 s
% 0.22/0.49  % (3195)------------------------------
% 0.22/0.49  % (3195)------------------------------
% 0.22/0.49  % (3199)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (3192)Refutation not found, incomplete strategy% (3192)------------------------------
% 0.22/0.49  % (3192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (3192)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (3192)Memory used [KB]: 6140
% 0.22/0.49  % (3192)Time elapsed: 0.071 s
% 0.22/0.49  % (3192)------------------------------
% 0.22/0.49  % (3192)------------------------------
% 0.22/0.49  % (3198)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (3197)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (3196)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (3198)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f61,f65,f69,f73,f77,f81,f85,f89,f97,f120,f127,f138,f150,f161,f172,f177])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    ~spl5_15 | ~spl5_2 | ~spl5_10 | ~spl5_11 | ~spl5_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f176,f133,f125,f118,f63,f148])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    spl5_15 <=> r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl5_2 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    spl5_10 <=> ! [X1,X0] : (~r2_hidden(X0,k4_orders_2(sK0,X1)) | m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    spl5_11 <=> ! [X1,X0] : (~m2_orders_2(X0,sK0,X1) | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl5_12 <=> k1_xboole_0 = k1_funct_1(sK1,u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | (~spl5_2 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.50    inference(resolution,[],[f175,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | ~r2_hidden(X1,k4_orders_2(sK0,sK1))) ) | (~spl5_2 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.50    inference(resolution,[],[f173,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k1_xboole_0,X0) | ~r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (~spl5_2 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 0.22/0.50    inference(superposition,[],[f129,f134])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    k1_xboole_0 = k1_funct_1(sK1,u1_struct_0(sK0)) | ~spl5_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f133])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0) | ~r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (~spl5_2 | ~spl5_10 | ~spl5_11)),
% 0.22/0.50    inference(resolution,[],[f128,f121])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    ( ! [X0] : (m2_orders_2(X0,sK0,sK1) | ~r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (~spl5_2 | ~spl5_10)),
% 0.22/0.50    inference(resolution,[],[f119,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f63])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X0,sK0,X1) | ~r2_hidden(X0,k4_orders_2(sK0,X1))) ) | ~spl5_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f118])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0)) ) | (~spl5_2 | ~spl5_11)),
% 0.22/0.50    inference(resolution,[],[f126,f64])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0) | ~m2_orders_2(X0,sK0,X1)) ) | ~spl5_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f125])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    spl5_7 | ~spl5_6 | ~spl5_5 | ~spl5_4 | ~spl5_3 | ~spl5_2 | ~spl5_8 | ~spl5_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f164,f159,f87,f63,f67,f71,f75,f79,f83])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    spl5_7 <=> v2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    spl5_6 <=> v3_orders_2(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl5_5 <=> v4_orders_2(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    spl5_4 <=> v5_orders_2(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    spl5_3 <=> l1_orders_2(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    spl5_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    spl5_17 <=> k1_xboole_0 = k4_orders_2(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl5_17),
% 0.22/0.50    inference(superposition,[],[f54,f160])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    k1_xboole_0 = k4_orders_2(sK0,sK1) | ~spl5_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f159])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    ~spl5_1 | spl5_17 | spl5_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f156,f148,f159,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    spl5_1 <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    k1_xboole_0 = k4_orders_2(sK0,sK1) | k1_xboole_0 != k3_tarski(k4_orders_2(sK0,sK1)) | spl5_15),
% 0.22/0.50    inference(resolution,[],[f149,f102])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ( ! [X1] : (r2_hidden(k1_xboole_0,X1) | k1_xboole_0 = X1 | k1_xboole_0 != k3_tarski(X1)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f101])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ( ! [X1] : (r2_hidden(k1_xboole_0,X1) | k1_xboole_0 = X1 | k1_xboole_0 != k3_tarski(X1) | k1_xboole_0 = X1) )),
% 0.22/0.50    inference(superposition,[],[f51,f98])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = sK4(X0) | k1_xboole_0 != k3_tarski(X0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(resolution,[],[f43,f51])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | k1_xboole_0 != k3_tarski(X0) | k1_xboole_0 = X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (((r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.22/0.50    inference(rectify,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | spl5_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f148])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    ~spl5_15 | ~spl5_9 | ~spl5_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f141,f136,f95,f148])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl5_9 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    spl5_13 <=> ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | k1_xboole_0 != k3_tarski(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | (~spl5_9 | ~spl5_13)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f140])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | (~spl5_9 | ~spl5_13)),
% 0.22/0.50    inference(superposition,[],[f137,f96])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl5_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f95])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | ~spl5_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f136])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl5_12 | spl5_13 | ~spl5_2 | ~spl5_10 | ~spl5_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f130,f125,f118,f63,f136,f133])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | k1_xboole_0 != k3_tarski(X0) | k1_xboole_0 = k1_funct_1(sK1,u1_struct_0(sK0))) ) | (~spl5_2 | ~spl5_10 | ~spl5_11)),
% 0.22/0.50    inference(resolution,[],[f129,f43])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    spl5_7 | ~spl5_6 | ~spl5_5 | ~spl5_4 | spl5_11 | ~spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f123,f67,f125,f71,f75,f79,f83])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_3),
% 0.22/0.50    inference(resolution,[],[f46,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    l1_orders_2(sK0) | ~spl5_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f67])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    spl5_7 | ~spl5_6 | ~spl5_5 | ~spl5_4 | spl5_10 | ~spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f112,f67,f118,f71,f75,f79,f83])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k4_orders_2(sK0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X0,sK0,X1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_3),
% 0.22/0.50    inference(resolution,[],[f57,f68])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X4,X0,X1] : (~l1_orders_2(X0) | ~r2_hidden(X4,k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X4,X0,X1) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK3(X0,X1,X2),X0,X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (m2_orders_2(sK3(X0,X1,X2),X0,X1) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK3(X0,X1,X2),X0,X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (m2_orders_2(sK3(X0,X1,X2),X0,X1) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(rectify,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl5_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f93,f95])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.50    inference(resolution,[],[f92,f42])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,sK2(X0)) | k1_xboole_0 = k3_tarski(X0)) )),
% 0.22/0.50    inference(resolution,[],[f45,f55])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = k3_tarski(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl5_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f41,f87])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ~spl5_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f83])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  % (3201)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f24,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.22/0.50    inference(negated_conjecture,[],[f9])).
% 0.22/0.50  fof(f9,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl5_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f35,f79])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    v3_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    spl5_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f36,f75])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    v4_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f71])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    v5_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f38,f67])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    l1_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f39,f63])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl5_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f40,f59])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (3198)------------------------------
% 0.22/0.50  % (3198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3198)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (3198)Memory used [KB]: 10746
% 0.22/0.50  % (3198)Time elapsed: 0.075 s
% 0.22/0.50  % (3198)------------------------------
% 0.22/0.50  % (3198)------------------------------
% 0.22/0.50  % (3191)Success in time 0.134 s
%------------------------------------------------------------------------------
