%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1579+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:25 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 119 expanded)
%              Number of leaves         :   15 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  170 ( 636 expanded)
%              Number of equality atoms :   44 ( 184 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3123,f3127,f3131,f3135,f3139,f3143,f3147,f3238,f3244,f3251])).

fof(f3251,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK2)
    | u1_orders_2(sK1) != k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1))
    | u1_orders_2(sK2) != k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1))
    | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3244,plain,
    ( spl6_22
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f3240,f3145,f3133,f3129,f3125,f3242])).

fof(f3242,plain,
    ( spl6_22
  <=> u1_orders_2(sK2) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f3125,plain,
    ( spl6_2
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f3129,plain,
    ( spl6_3
  <=> m1_yellow_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f3133,plain,
    ( spl6_4
  <=> v4_yellow_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f3145,plain,
    ( spl6_7
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f3240,plain,
    ( u1_orders_2(sK2) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f3239,f3126])).

fof(f3126,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f3125])).

fof(f3239,plain,
    ( u1_orders_2(sK2) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK2))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f3231,f3130])).

fof(f3130,plain,
    ( m1_yellow_0(sK2,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f3129])).

fof(f3231,plain,
    ( ~ m1_yellow_0(sK2,sK0)
    | u1_orders_2(sK2) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK2))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(resolution,[],[f3226,f3134])).

fof(f3134,plain,
    ( v4_yellow_0(sK2,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f3133])).

fof(f3226,plain,
    ( ! [X0] :
        ( ~ v4_yellow_0(X0,sK0)
        | ~ m1_yellow_0(X0,sK0)
        | u1_orders_2(X0) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(X0)) )
    | ~ spl6_7 ),
    inference(resolution,[],[f3111,f3146])).

fof(f3146,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f3145])).

fof(f3111,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f3083])).

fof(f3083,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_yellow_0(X1,X0)
              | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
            & ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
              | ~ v4_yellow_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3071])).

fof(f3071,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2972])).

fof(f2972,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_yellow_0)).

fof(f3238,plain,
    ( spl6_21
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f3234,f3145,f3141,f3137,f3236])).

fof(f3236,plain,
    ( spl6_21
  <=> u1_orders_2(sK1) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f3137,plain,
    ( spl6_5
  <=> m1_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f3141,plain,
    ( spl6_6
  <=> v4_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f3234,plain,
    ( u1_orders_2(sK1) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1))
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f3230,f3138])).

fof(f3138,plain,
    ( m1_yellow_0(sK1,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f3137])).

fof(f3230,plain,
    ( ~ m1_yellow_0(sK1,sK0)
    | u1_orders_2(sK1) = k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1))
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(resolution,[],[f3226,f3142])).

fof(f3142,plain,
    ( v4_yellow_0(sK1,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f3141])).

fof(f3147,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f3086,f3145])).

fof(f3086,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3075])).

fof(f3075,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    & u1_struct_0(sK1) = u1_struct_0(sK2)
    & m1_yellow_0(sK2,sK0)
    & v4_yellow_0(sK2,sK0)
    & m1_yellow_0(sK1,sK0)
    & v4_yellow_0(sK1,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f3058,f3074,f3073,f3072])).

fof(f3072,plain,
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

fof(f3073,plain,
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

fof(f3074,plain,
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

fof(f3058,plain,(
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
    inference(flattening,[],[f3057])).

fof(f3057,plain,(
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
    inference(ennf_transformation,[],[f3049])).

fof(f3049,negated_conjecture,(
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
    inference(negated_conjecture,[],[f3048])).

fof(f3048,conjecture,(
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

fof(f3143,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f3087,f3141])).

fof(f3087,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f3075])).

fof(f3139,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f3088,f3137])).

fof(f3088,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f3075])).

fof(f3135,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f3089,f3133])).

fof(f3089,plain,(
    v4_yellow_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f3075])).

fof(f3131,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f3090,f3129])).

fof(f3090,plain,(
    m1_yellow_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f3075])).

fof(f3127,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f3091,f3125])).

fof(f3091,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3075])).

fof(f3123,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f3092,f3121])).

fof(f3121,plain,
    ( spl6_1
  <=> g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f3092,plain,(
    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(cnf_transformation,[],[f3075])).
%------------------------------------------------------------------------------
