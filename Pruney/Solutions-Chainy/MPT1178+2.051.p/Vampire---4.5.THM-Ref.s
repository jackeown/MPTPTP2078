%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 192 expanded)
%              Number of leaves         :   27 (  88 expanded)
%              Depth                    :   10
%              Number of atoms          :  474 ( 927 expanded)
%              Number of equality atoms :   63 ( 120 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f71,f75,f79,f83,f87,f91,f120,f128,f135,f145,f192,f217,f222])).

fof(f222,plain,(
    ~ spl6_21 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl6_21 ),
    inference(resolution,[],[f215,f92])).

fof(f92,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f52,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f215,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl6_21
  <=> r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f217,plain,
    ( spl6_21
    | ~ spl6_2
    | ~ spl6_13
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f210,f190,f143,f69,f214])).

fof(f69,plain,
    ( spl6_2
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f143,plain,
    ( spl6_13
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f190,plain,
    ( spl6_18
  <=> ! [X1,X0,X2] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ r1_xboole_0(X2,X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X2,sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f210,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_13
    | ~ spl6_18 ),
    inference(resolution,[],[f202,f144])).

fof(f144,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f202,plain,
    ( ! [X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | r2_hidden(sK4(X1,k1_xboole_0),k1_xboole_0) )
    | ~ spl6_2
    | ~ spl6_13
    | ~ spl6_18 ),
    inference(resolution,[],[f194,f144])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | r2_hidden(sK4(X1,X0),X0) )
    | ~ spl6_2
    | ~ spl6_18 ),
    inference(resolution,[],[f193,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f193,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ m2_orders_2(X0,sK0,sK1) )
    | ~ spl6_2
    | ~ spl6_18 ),
    inference(resolution,[],[f191,f70])).

fof(f70,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f191,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X2,X0)
        | ~ m2_orders_2(X0,sK0,X1)
        | ~ m2_orders_2(X2,sK0,X1) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f190])).

fof(f192,plain,
    ( spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | spl6_18
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f188,f73,f190,f77,f81,f85,f89])).

fof(f89,plain,
    ( spl6_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f85,plain,
    ( spl6_6
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f81,plain,
    ( spl6_5
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f77,plain,
    ( spl6_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f73,plain,
    ( spl6_3
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f188,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m2_orders_2(X2,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X2,X0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f47,f74])).

fof(f74,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ r1_xboole_0(X2,X3)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
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
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).

fof(f145,plain,
    ( spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | spl6_13
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f137,f132,f143,f69,f73,f77,f81,f85,f89])).

fof(f132,plain,
    ( spl6_11
  <=> k1_xboole_0 = sK5(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f137,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_11 ),
    inference(superposition,[],[f56,f133])).

fof(f133,plain,
    ( k1_xboole_0 = sK5(sK0,sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK5(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK5(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
     => m2_orders_2(sK5(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

fof(f135,plain,
    ( spl6_11
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f129,f126,f65,f132])).

fof(f65,plain,
    ( spl6_1
  <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f126,plain,
    ( spl6_10
  <=> r2_hidden(sK5(sK0,sK1),k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f129,plain,
    ( k1_xboole_0 != k3_tarski(k4_orders_2(sK0,sK1))
    | k1_xboole_0 = sK5(sK0,sK1)
    | ~ spl6_10 ),
    inference(resolution,[],[f127,f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 != k3_tarski(X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK2(X0),X0)
          & k1_xboole_0 != sK2(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
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

fof(f127,plain,
    ( r2_hidden(sK5(sK0,sK1),k4_orders_2(sK0,sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f128,plain,
    ( spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | spl6_10
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f122,f118,f69,f126,f69,f73,f77,f81,f85,f89])).

fof(f118,plain,
    ( spl6_9
  <=> ! [X1,X0] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | r2_hidden(X0,k4_orders_2(sK0,X1))
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f122,plain,
    ( r2_hidden(sK5(sK0,sK1),k4_orders_2(sK0,sK1))
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(resolution,[],[f121,f56])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(resolution,[],[f119,f70])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | r2_hidden(X0,k4_orders_2(sK0,X1))
        | ~ m2_orders_2(X0,sK0,X1) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f120,plain,
    ( spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | spl6_9
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f112,f73,f118,f77,f81,f85,f89])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | r2_hidden(X0,k4_orders_2(sK0,X1))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f60,f74])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m2_orders_2(X4,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ m2_orders_2(X4,X0,X1)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f91,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f37,f89])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f23,f22])).

fof(f22,plain,
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

fof(f23,plain,
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f87,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f38,f85])).

fof(f38,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f39,f81])).

fof(f39,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f40,f77])).

fof(f40,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f41,f73])).

fof(f41,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f42,f69])).

fof(f42,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f43,f65])).

fof(f43,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:28:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (3168)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (3178)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.47  % (3168)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (3169)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (3177)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f229,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f67,f71,f75,f79,f83,f87,f91,f120,f128,f135,f145,f192,f217,f222])).
% 0.22/0.47  fof(f222,plain,(
% 0.22/0.47    ~spl6_21),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f219])).
% 0.22/0.47  fof(f219,plain,(
% 0.22/0.47    $false | ~spl6_21),
% 0.22/0.47    inference(resolution,[],[f215,f92])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.47    inference(superposition,[],[f52,f62])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.47    inference(equality_resolution,[],[f59])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.22/0.47    inference(cnf_transformation,[],[f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.47    inference(flattening,[],[f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.47    inference(nnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.47  fof(f215,plain,(
% 0.22/0.47    r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl6_21),
% 0.22/0.47    inference(avatar_component_clause,[],[f214])).
% 0.22/0.47  fof(f214,plain,(
% 0.22/0.47    spl6_21 <=> r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.22/0.47  fof(f217,plain,(
% 0.22/0.47    spl6_21 | ~spl6_2 | ~spl6_13 | ~spl6_18),
% 0.22/0.47    inference(avatar_split_clause,[],[f210,f190,f143,f69,f214])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    spl6_2 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.47  fof(f143,plain,(
% 0.22/0.47    spl6_13 <=> m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.47  fof(f190,plain,(
% 0.22/0.47    spl6_18 <=> ! [X1,X0,X2] : (~m2_orders_2(X0,sK0,X1) | ~r1_xboole_0(X2,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X2,sK0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.47  fof(f210,plain,(
% 0.22/0.47    r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl6_2 | ~spl6_13 | ~spl6_18)),
% 0.22/0.47    inference(resolution,[],[f202,f144])).
% 0.22/0.47  fof(f144,plain,(
% 0.22/0.47    m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl6_13),
% 0.22/0.47    inference(avatar_component_clause,[],[f143])).
% 0.22/0.47  fof(f202,plain,(
% 0.22/0.47    ( ! [X1] : (~m2_orders_2(X1,sK0,sK1) | r2_hidden(sK4(X1,k1_xboole_0),k1_xboole_0)) ) | (~spl6_2 | ~spl6_13 | ~spl6_18)),
% 0.22/0.47    inference(resolution,[],[f194,f144])).
% 0.22/0.47  fof(f194,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | r2_hidden(sK4(X1,X0),X0)) ) | (~spl6_2 | ~spl6_18)),
% 0.22/0.47    inference(resolution,[],[f193,f54])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(rectify,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.48  fof(f193,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | ~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1)) ) | (~spl6_2 | ~spl6_18)),
% 0.22/0.48    inference(resolution,[],[f191,f70])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl6_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f69])).
% 0.22/0.48  fof(f191,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~r1_xboole_0(X2,X0) | ~m2_orders_2(X0,sK0,X1) | ~m2_orders_2(X2,sK0,X1)) ) | ~spl6_18),
% 0.22/0.48    inference(avatar_component_clause,[],[f190])).
% 0.22/0.48  fof(f192,plain,(
% 0.22/0.48    spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_4 | spl6_18 | ~spl6_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f188,f73,f190,f77,f81,f85,f89])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    spl6_7 <=> v2_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    spl6_6 <=> v3_orders_2(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    spl6_5 <=> v4_orders_2(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    spl6_4 <=> v5_orders_2(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    spl6_3 <=> l1_orders_2(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.48  fof(f188,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m2_orders_2(X2,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~r1_xboole_0(X2,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_3),
% 0.22/0.48    inference(resolution,[],[f47,f74])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    l1_orders_2(sK0) | ~spl6_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f73])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~r1_xboole_0(X2,X3) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_4 | ~spl6_3 | ~spl6_2 | spl6_13 | ~spl6_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f137,f132,f143,f69,f73,f77,f81,f85,f89])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    spl6_11 <=> k1_xboole_0 = sK5(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    m2_orders_2(k1_xboole_0,sK0,sK1) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl6_11),
% 0.22/0.48    inference(superposition,[],[f56,f133])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    k1_xboole_0 = sK5(sK0,sK1) | ~spl6_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f132])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m2_orders_2(sK5(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0,X1] : (m2_orders_2(sK5(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2] : m2_orders_2(X2,X0,X1) => m2_orders_2(sK5(X0,X1),X0,X1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    spl6_11 | ~spl6_1 | ~spl6_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f129,f126,f65,f132])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    spl6_1 <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    spl6_10 <=> r2_hidden(sK5(sK0,sK1),k4_orders_2(sK0,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    k1_xboole_0 != k3_tarski(k4_orders_2(sK0,sK1)) | k1_xboole_0 = sK5(sK0,sK1) | ~spl6_10),
% 0.22/0.48    inference(resolution,[],[f127,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | k1_xboole_0 != k3_tarski(X0) | k1_xboole_0 = X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0] : (((r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.22/0.48    inference(rectify,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    r2_hidden(sK5(sK0,sK1),k4_orders_2(sK0,sK1)) | ~spl6_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f126])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_4 | ~spl6_3 | ~spl6_2 | spl6_10 | ~spl6_2 | ~spl6_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f122,f118,f69,f126,f69,f73,f77,f81,f85,f89])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    spl6_9 <=> ! [X1,X0] : (~m2_orders_2(X0,sK0,X1) | r2_hidden(X0,k4_orders_2(sK0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    r2_hidden(sK5(sK0,sK1),k4_orders_2(sK0,sK1)) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_9)),
% 0.22/0.48    inference(resolution,[],[f121,f56])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_9)),
% 0.22/0.48    inference(resolution,[],[f119,f70])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(X0,k4_orders_2(sK0,X1)) | ~m2_orders_2(X0,sK0,X1)) ) | ~spl6_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f118])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_4 | spl6_9 | ~spl6_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f112,f73,f118,f77,f81,f85,f89])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(X0,k4_orders_2(sK0,X1)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_3),
% 0.22/0.48    inference(resolution,[],[f60,f74])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X4,X0,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X4,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | r2_hidden(X4,k4_orders_2(X0,X1)) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK3(X0,X1,X2),X0,X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (m2_orders_2(sK3(X0,X1,X2),X0,X1) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK3(X0,X1,X2),X0,X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (m2_orders_2(sK3(X0,X1,X2),X0,X1) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(rectify,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ~spl6_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f37,f89])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ~v2_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f23,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.22/0.48    inference(negated_conjecture,[],[f8])).
% 0.22/0.48  fof(f8,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    spl6_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f38,f85])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    v3_orders_2(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    spl6_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f39,f81])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    v4_orders_2(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    spl6_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f40,f77])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    v5_orders_2(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    spl6_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f41,f73])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    l1_orders_2(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl6_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f42,f69])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl6_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f43,f65])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (3168)------------------------------
% 0.22/0.48  % (3168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (3168)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (3168)Memory used [KB]: 10746
% 0.22/0.48  % (3168)Time elapsed: 0.058 s
% 0.22/0.48  % (3168)------------------------------
% 0.22/0.48  % (3168)------------------------------
% 0.22/0.48  % (3164)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (3178)Refutation not found, incomplete strategy% (3178)------------------------------
% 0.22/0.48  % (3178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (3178)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (3178)Memory used [KB]: 6268
% 0.22/0.48  % (3178)Time elapsed: 0.016 s
% 0.22/0.48  % (3178)------------------------------
% 0.22/0.48  % (3178)------------------------------
% 0.22/0.48  % (3167)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (3165)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (3174)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (3159)Success in time 0.135 s
%------------------------------------------------------------------------------
