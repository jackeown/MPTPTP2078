%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 238 expanded)
%              Number of leaves         :   28 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  485 (1015 expanded)
%              Number of equality atoms :   45 ( 108 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f472,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f85,f90,f95,f100,f134,f261,f269,f381,f400,f471])).

fof(f471,plain,
    ( ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_25 ),
    inference(avatar_contradiction_clause,[],[f470])).

fof(f470,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_8
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f442,f101])).

fof(f101,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f99,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
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

fof(f99,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl8_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f442,plain,
    ( r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),k1_xboole_0)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f94,f89,f84,f79,f74,f399,f69,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
              ( m2_orders_2(X2,X0,X1)
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

fof(f69,plain,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl8_2
  <=> m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f399,plain,
    ( m2_orders_2(k1_xboole_0,sK2,sK3)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f397])).

fof(f397,plain,
    ( spl8_25
  <=> m2_orders_2(k1_xboole_0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f74,plain,
    ( l1_orders_2(sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl8_3
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f79,plain,
    ( v5_orders_2(sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl8_4
  <=> v5_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f84,plain,
    ( v4_orders_2(sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl8_5
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f89,plain,
    ( v3_orders_2(sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl8_6
  <=> v3_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f94,plain,
    ( ~ v2_struct_0(sK2)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl8_7
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f400,plain,
    ( spl8_25
    | spl8_10
    | ~ spl8_11
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f395,f159,f131,f127,f397])).

fof(f127,plain,
    ( spl8_10
  <=> v1_xboole_0(k4_orders_2(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f131,plain,
    ( spl8_11
  <=> k1_xboole_0 = sK6(k4_orders_2(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f159,plain,
    ( spl8_13
  <=> sP1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f395,plain,
    ( m2_orders_2(k1_xboole_0,sK2,sK3)
    | spl8_10
    | ~ spl8_11
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f391,f133])).

fof(f133,plain,
    ( k1_xboole_0 = sK6(k4_orders_2(sK2,sK3))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f391,plain,
    ( m2_orders_2(sK6(k4_orders_2(sK2,sK3)),sK2,sK3)
    | spl8_10
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f160,f128,f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK6(k4_orders_2(X0,X1)),X0,X1)
      | ~ sP1(X0,X1)
      | v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    inference(resolution,[],[f123,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_orders_2(X1,X2))
      | m2_orders_2(X0,X1,X2)
      | ~ sP1(X1,X2) ) ),
    inference(resolution,[],[f52,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0,k4_orders_2(X0,X1))
      | ~ sP1(X0,X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_orders_2(X0,X1) != X2
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k4_orders_2(X0,X1) = X2
            | ~ sP0(X1,X0,X2) )
          & ( sP0(X1,X0,X2)
            | k4_orders_2(X0,X1) != X2 ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k4_orders_2(X0,X1) = X2
        <=> sP0(X1,X0,X2) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | m2_orders_2(X4,X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ m2_orders_2(sK5(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( m2_orders_2(sK5(X0,X1,X2),X1,X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ m2_orders_2(X4,X1,X0) )
            & ( m2_orders_2(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK5(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( m2_orders_2(sK5(X0,X1,X2),X1,X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ m2_orders_2(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( m2_orders_2(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ m2_orders_2(X4,X1,X0) )
            & ( m2_orders_2(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> m2_orders_2(X3,X0,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f128,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK2,sK3))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f160,plain,
    ( sP1(sK2,sK3)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f381,plain,
    ( ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_19 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f379,f94])).

fof(f379,plain,
    ( v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f378,f89])).

fof(f378,plain,
    ( ~ v3_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f377,f84])).

fof(f377,plain,
    ( ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f376,f79])).

fof(f376,plain,
    ( ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f375,f74])).

fof(f375,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f358,f69])).

fof(f358,plain,
    ( ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    | ~ l1_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_19 ),
    inference(resolution,[],[f59,f268])).

fof(f268,plain,
    ( ! [X0] : ~ m2_orders_2(X0,sK2,sK3)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl8_19
  <=> ! [X0] : ~ m2_orders_2(X0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK7(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK7(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f18,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
     => m2_orders_2(sK7(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

fof(f269,plain,
    ( ~ spl8_13
    | spl8_19
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f182,f127,f267,f159])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK2,sK3)
        | ~ sP1(sK2,sK3) )
    | ~ spl8_10 ),
    inference(resolution,[],[f149,f143])).

fof(f143,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_orders_2(sK2,sK3))
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f129,f57])).

fof(f129,plain,
    ( v1_xboole_0(k4_orders_2(sK2,sK3))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_orders_2(X1,X2))
      | ~ m2_orders_2(X0,X1,X2)
      | ~ sP1(X1,X2) ) ),
    inference(resolution,[],[f53,f60])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ m2_orders_2(X4,X1,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f261,plain,
    ( spl8_13
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f225,f92,f87,f82,f77,f72,f67,f159])).

fof(f225,plain,
    ( sP1(sK2,sK3)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f94,f89,f84,f79,f74,f69,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | sP1(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f16,f20,f19])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f134,plain,
    ( spl8_10
    | spl8_11
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f124,f62,f131,f127])).

fof(f62,plain,
    ( spl8_1
  <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f124,plain,
    ( k1_xboole_0 = sK6(k4_orders_2(sK2,sK3))
    | v1_xboole_0(k4_orders_2(sK2,sK3))
    | ~ spl8_1 ),
    inference(resolution,[],[f122,f58])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_orders_2(sK2,sK3))
        | k1_xboole_0 = X0 )
    | ~ spl8_1 ),
    inference(trivial_inequality_removal,[],[f115])).

fof(f115,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ r2_hidden(X0,k4_orders_2(sK2,sK3))
        | k1_xboole_0 = X0 )
    | ~ spl8_1 ),
    inference(superposition,[],[f46,f64])).

fof(f64,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f46,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK4(X0),X0)
          & k1_xboole_0 != sK4(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK4(X0),X0)
        & k1_xboole_0 != sK4(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
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

fof(f100,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f45,f97])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f95,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f38,f92])).

fof(f38,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3))
    & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f11,f23,f22])).

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
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2))) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,X1))
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2))) )
   => ( k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3))
      & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f90,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f39,f87])).

fof(f39,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f40,f82])).

fof(f40,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f41,f77])).

fof(f41,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f42,f72])).

fof(f42,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f43,f67])).

fof(f43,plain,(
    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f44,f62])).

fof(f44,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (15538)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (15525)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (15525)Refutation not found, incomplete strategy% (15525)------------------------------
% 0.20/0.47  % (15525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (15525)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (15525)Memory used [KB]: 10618
% 0.20/0.47  % (15525)Time elapsed: 0.061 s
% 0.20/0.47  % (15525)------------------------------
% 0.20/0.47  % (15525)------------------------------
% 0.20/0.47  % (15529)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (15538)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (15527)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f472,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f85,f90,f95,f100,f134,f261,f269,f381,f400,f471])).
% 0.20/0.48  fof(f471,plain,(
% 0.20/0.48    ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_25),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f470])).
% 0.20/0.48  fof(f470,plain,(
% 0.20/0.48    $false | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_8 | ~spl8_25)),
% 0.20/0.48    inference(subsumption_resolution,[],[f442,f101])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl8_8),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f99,f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.48    inference(rectify,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0) | ~spl8_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f97])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    spl8_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.48  fof(f442,plain,(
% 0.20/0.48    r2_hidden(k1_funct_1(sK3,u1_struct_0(sK2)),k1_xboole_0) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_25)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f94,f89,f84,f79,f74,f399,f69,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) | ~spl8_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    spl8_2 <=> m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.48  fof(f399,plain,(
% 0.20/0.48    m2_orders_2(k1_xboole_0,sK2,sK3) | ~spl8_25),
% 0.20/0.48    inference(avatar_component_clause,[],[f397])).
% 0.20/0.48  fof(f397,plain,(
% 0.20/0.48    spl8_25 <=> m2_orders_2(k1_xboole_0,sK2,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    l1_orders_2(sK2) | ~spl8_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f72])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    spl8_3 <=> l1_orders_2(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    v5_orders_2(sK2) | ~spl8_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f77])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    spl8_4 <=> v5_orders_2(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    v4_orders_2(sK2) | ~spl8_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f82])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    spl8_5 <=> v4_orders_2(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    v3_orders_2(sK2) | ~spl8_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f87])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    spl8_6 <=> v3_orders_2(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ~v2_struct_0(sK2) | spl8_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f92])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    spl8_7 <=> v2_struct_0(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.48  fof(f400,plain,(
% 0.20/0.48    spl8_25 | spl8_10 | ~spl8_11 | ~spl8_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f395,f159,f131,f127,f397])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    spl8_10 <=> v1_xboole_0(k4_orders_2(sK2,sK3))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    spl8_11 <=> k1_xboole_0 = sK6(k4_orders_2(sK2,sK3))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    spl8_13 <=> sP1(sK2,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.48  fof(f395,plain,(
% 0.20/0.48    m2_orders_2(k1_xboole_0,sK2,sK3) | (spl8_10 | ~spl8_11 | ~spl8_13)),
% 0.20/0.48    inference(forward_demodulation,[],[f391,f133])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    k1_xboole_0 = sK6(k4_orders_2(sK2,sK3)) | ~spl8_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f131])).
% 0.20/0.48  fof(f391,plain,(
% 0.20/0.48    m2_orders_2(sK6(k4_orders_2(sK2,sK3)),sK2,sK3) | (spl8_10 | ~spl8_13)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f160,f128,f178])).
% 0.20/0.48  fof(f178,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m2_orders_2(sK6(k4_orders_2(X0,X1)),X0,X1) | ~sP1(X0,X1) | v1_xboole_0(k4_orders_2(X0,X1))) )),
% 0.20/0.48    inference(resolution,[],[f123,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f35])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_orders_2(X1,X2)) | m2_orders_2(X0,X1,X2) | ~sP1(X1,X2)) )),
% 0.20/0.48    inference(resolution,[],[f52,f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP0(X1,X0,k4_orders_2(X0,X1)) | ~sP1(X0,X1)) )),
% 0.20/0.48    inference(equality_resolution,[],[f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_orders_2(X0,X1) != X2 | ~sP1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_orders_2(X0,X1) != X2)) | ~sP1(X0,X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X0,X1))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | m2_orders_2(X4,X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~m2_orders_2(sK5(X0,X1,X2),X1,X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (m2_orders_2(sK5(X0,X1,X2),X1,X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X1,X0)) & (m2_orders_2(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X1,X0) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X1,X0) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK5(X0,X1,X2),X1,X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (m2_orders_2(sK5(X0,X1,X2),X1,X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~m2_orders_2(X3,X1,X0) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X1,X0)) & (m2_orders_2(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.48    inference(rectify,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.48    inference(nnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ~v1_xboole_0(k4_orders_2(sK2,sK3)) | spl8_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f127])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    sP1(sK2,sK3) | ~spl8_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f159])).
% 0.20/0.48  fof(f381,plain,(
% 0.20/0.48    ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_19),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f380])).
% 0.20/0.48  fof(f380,plain,(
% 0.20/0.48    $false | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f379,f94])).
% 0.20/0.48  fof(f379,plain,(
% 0.20/0.48    v2_struct_0(sK2) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f378,f89])).
% 0.20/0.48  fof(f378,plain,(
% 0.20/0.48    ~v3_orders_2(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f377,f84])).
% 0.20/0.48  fof(f377,plain,(
% 0.20/0.48    ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f376,f79])).
% 0.20/0.48  fof(f376,plain,(
% 0.20/0.48    ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_3 | ~spl8_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f375,f74])).
% 0.20/0.48  fof(f375,plain,(
% 0.20/0.48    ~l1_orders_2(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2) | (~spl8_2 | ~spl8_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f358,f69])).
% 0.20/0.48  fof(f358,plain,(
% 0.20/0.48    ~m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2) | ~spl8_19),
% 0.20/0.48    inference(resolution,[],[f59,f268])).
% 0.20/0.48  fof(f268,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK2,sK3)) ) | ~spl8_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f267])).
% 0.20/0.48  fof(f267,plain,(
% 0.20/0.48    spl8_19 <=> ! [X0] : ~m2_orders_2(X0,sK2,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m2_orders_2(sK7(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ! [X0,X1] : (m2_orders_2(sK7(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f18,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : m2_orders_2(X2,X0,X1) => m2_orders_2(sK7(X0,X1),X0,X1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).
% 0.20/0.48  fof(f269,plain,(
% 0.20/0.48    ~spl8_13 | spl8_19 | ~spl8_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f182,f127,f267,f159])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK2,sK3) | ~sP1(sK2,sK3)) ) | ~spl8_10),
% 0.20/0.48    inference(resolution,[],[f149,f143])).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK2,sK3))) ) | ~spl8_10),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f129,f57])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    v1_xboole_0(k4_orders_2(sK2,sK3)) | ~spl8_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f127])).
% 0.20/0.48  fof(f149,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_orders_2(X1,X2)) | ~m2_orders_2(X0,X1,X2) | ~sP1(X1,X2)) )),
% 0.20/0.48    inference(resolution,[],[f53,f60])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~m2_orders_2(X4,X1,X0) | r2_hidden(X4,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f261,plain,(
% 0.20/0.48    spl8_13 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f225,f92,f87,f82,f77,f72,f67,f159])).
% 0.20/0.48  fof(f225,plain,(
% 0.20/0.48    sP1(sK2,sK3) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_7)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f94,f89,f84,f79,f74,f69,f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | sP1(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(definition_folding,[],[f16,f20,f19])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    spl8_10 | spl8_11 | ~spl8_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f124,f62,f131,f127])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    spl8_1 <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    k1_xboole_0 = sK6(k4_orders_2(sK2,sK3)) | v1_xboole_0(k4_orders_2(sK2,sK3)) | ~spl8_1),
% 0.20/0.48    inference(resolution,[],[f122,f58])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK2,sK3)) | k1_xboole_0 = X0) ) | ~spl8_1),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f115])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k4_orders_2(sK2,sK3)) | k1_xboole_0 = X0) ) | ~spl8_1),
% 0.20/0.48    inference(superposition,[],[f46,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) | ~spl8_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f62])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0] : (((r2_hidden(sK4(X0),X0) & k1_xboole_0 != sK4(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK4(X0),X0) & k1_xboole_0 != sK4(X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.20/0.48    inference(rectify,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    spl8_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f45,f97])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ~spl8_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f38,f92])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ~v2_struct_0(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    (k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f11,f23,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK2,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK2,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3)) & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.20/0.48    inference(negated_conjecture,[],[f7])).
% 0.20/0.48  fof(f7,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    spl8_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f39,f87])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    v3_orders_2(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    spl8_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f40,f82])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    v4_orders_2(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    spl8_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f41,f77])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    v5_orders_2(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    spl8_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f42,f72])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    l1_orders_2(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl8_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f43,f67])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl8_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f44,f62])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    k1_xboole_0 = k3_tarski(k4_orders_2(sK2,sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (15538)------------------------------
% 0.20/0.48  % (15538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (15538)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (15538)Memory used [KB]: 10874
% 0.20/0.48  % (15538)Time elapsed: 0.015 s
% 0.20/0.48  % (15538)------------------------------
% 0.20/0.48  % (15538)------------------------------
% 0.20/0.49  % (15521)Success in time 0.127 s
%------------------------------------------------------------------------------
