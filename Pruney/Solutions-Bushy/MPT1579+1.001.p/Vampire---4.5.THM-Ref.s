%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1579+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:08 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 148 expanded)
%              Number of leaves         :   18 (  70 expanded)
%              Depth                    :    7
%              Number of atoms          :  223 ( 713 expanded)
%              Number of equality atoms :   54 ( 206 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f45,f50,f55,f63,f69,f74,f83,f89,f95,f98])).

fof(f98,plain,
    ( spl3_10
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl3_10
    | ~ spl3_14 ),
    inference(trivial_inequality_removal,[],[f96])).

fof(f96,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | spl3_10
    | ~ spl3_14 ),
    inference(superposition,[],[f68,f94])).

fof(f94,plain,
    ( u1_orders_2(sK1) = u1_orders_2(sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_14
  <=> u1_orders_2(sK1) = u1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f68,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK2))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_10
  <=> g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f95,plain,
    ( spl3_14
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f90,f86,f80,f92])).

fof(f80,plain,
    ( spl3_12
  <=> u1_orders_2(sK2) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f86,plain,
    ( spl3_13
  <=> u1_orders_2(sK1) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f90,plain,
    ( u1_orders_2(sK1) = u1_orders_2(sK2)
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f82,f88])).

fof(f88,plain,
    ( u1_orders_2(sK1) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f82,plain,
    ( u1_orders_2(sK2) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f89,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f84,f72,f47,f42,f86])).

fof(f42,plain,
    ( spl3_5
  <=> m1_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f47,plain,
    ( spl3_6
  <=> v4_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f72,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ v4_yellow_0(X0,sK0)
        | ~ m1_yellow_0(X0,sK0)
        | u1_orders_2(X0) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f84,plain,
    ( u1_orders_2(sK1) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f76,f49])).

fof(f49,plain,
    ( v4_yellow_0(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f76,plain,
    ( ~ v4_yellow_0(sK1,sK0)
    | u1_orders_2(sK1) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(resolution,[],[f73,f44])).

fof(f44,plain,
    ( m1_yellow_0(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ m1_yellow_0(X0,sK0)
        | ~ v4_yellow_0(X0,sK0)
        | u1_orders_2(X0) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(X0)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f83,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f78,f72,f37,f32,f27,f80])).

fof(f27,plain,
    ( spl3_2
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f32,plain,
    ( spl3_3
  <=> m1_yellow_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f37,plain,
    ( spl3_4
  <=> v4_yellow_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f78,plain,
    ( u1_orders_2(sK2) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f77,f29])).

fof(f29,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f77,plain,
    ( u1_orders_2(sK2) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f75,f39])).

fof(f39,plain,
    ( v4_yellow_0(sK2,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f75,plain,
    ( ~ v4_yellow_0(sK2,sK0)
    | u1_orders_2(sK2) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK2))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(resolution,[],[f73,f34])).

fof(f34,plain,
    ( m1_yellow_0(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f74,plain,
    ( spl3_11
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f70,f61,f52,f72])).

fof(f52,plain,
    ( spl3_7
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f61,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
        | ~ v4_yellow_0(X1,X0)
        | ~ m1_yellow_0(X1,X0)
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ v4_yellow_0(X0,sK0)
        | ~ m1_yellow_0(X0,sK0)
        | u1_orders_2(X0) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(X0)) )
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(resolution,[],[f62,f54])).

fof(f54,plain,
    ( l1_orders_2(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v4_yellow_0(X1,X0)
        | ~ m1_yellow_0(X1,X0)
        | u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f69,plain,
    ( ~ spl3_10
    | spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f64,f27,f22,f66])).

fof(f22,plain,
    ( spl3_1
  <=> g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f64,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK2))
    | spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f24,f29])).

fof(f24,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f63,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f19,f61])).

fof(f19,plain,(
    ! [X0,X1] :
      ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_yellow_0(X1,X0)
              | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
            & ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
              | ~ v4_yellow_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_yellow_0)).

fof(f55,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f12,f52])).

fof(f12,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    & u1_struct_0(sK1) = u1_struct_0(sK2)
    & m1_yellow_0(sK2,sK0)
    & v4_yellow_0(sK2,sK0)
    & m1_yellow_0(sK1,sK0)
    & v4_yellow_0(sK1,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f9,f8,f7])).

fof(f7,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                & u1_struct_0(X1) = u1_struct_0(X2)
                & m1_yellow_0(X2,X0)
                & v4_yellow_0(X2,X0) )
            & m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_yellow_0(X2,sK0)
              & v4_yellow_0(X2,sK0) )
          & m1_yellow_0(X1,sK0)
          & v4_yellow_0(X1,sK0) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
            & u1_struct_0(X1) = u1_struct_0(X2)
            & m1_yellow_0(X2,sK0)
            & v4_yellow_0(X2,sK0) )
        & m1_yellow_0(X1,sK0)
        & v4_yellow_0(X1,sK0) )
   => ( ? [X2] :
          ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
          & u1_struct_0(X2) = u1_struct_0(sK1)
          & m1_yellow_0(X2,sK0)
          & v4_yellow_0(X2,sK0) )
      & m1_yellow_0(sK1,sK0)
      & v4_yellow_0(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ? [X2] :
        ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        & u1_struct_0(X2) = u1_struct_0(sK1)
        & m1_yellow_0(X2,sK0)
        & v4_yellow_0(X2,sK0) )
   => ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      & u1_struct_0(sK1) = u1_struct_0(sK2)
      & m1_yellow_0(sK2,sK0)
      & v4_yellow_0(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_yellow_0(X2,X0)
              & v4_yellow_0(X2,X0) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_yellow_0(X2,X0)
              & v4_yellow_0(X2,X0) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0) )
           => ! [X2] :
                ( ( m1_yellow_0(X2,X0)
                  & v4_yellow_0(X2,X0) )
               => ( u1_struct_0(X1) = u1_struct_0(X2)
                 => g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
         => ! [X2] :
              ( ( m1_yellow_0(X2,X0)
                & v4_yellow_0(X2,X0) )
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_yellow_0)).

fof(f50,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f13,f47])).

fof(f13,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f45,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f14,f42])).

fof(f14,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f37])).

fof(f15,plain,(
    v4_yellow_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    m1_yellow_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f27])).

fof(f17,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f22])).

fof(f18,plain,(
    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
