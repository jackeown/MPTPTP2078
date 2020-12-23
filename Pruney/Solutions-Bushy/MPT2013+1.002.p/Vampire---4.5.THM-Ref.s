%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2013+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 285 expanded)
%              Number of leaves         :   32 ( 150 expanded)
%              Depth                    :    8
%              Number of atoms          :  591 (1197 expanded)
%              Number of equality atoms :   43 ( 105 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f406,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f78,f112,f118,f123,f129,f189,f196,f209,f222,f242,f244,f258,f259,f260,f371,f372,f378,f379,f380,f381,f399,f405])).

fof(f405,plain,
    ( sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) != sK7(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2)
    | r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ r2_hidden(sK7(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f399,plain,
    ( ~ spl8_18
    | spl8_49
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f393,f240,f231,f396,f153])).

fof(f153,plain,
    ( spl8_18
  <=> m1_subset_1(sK7(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f396,plain,
    ( spl8_49
  <=> r2_hidden(sK7(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f231,plain,
    ( spl8_29
  <=> r1_orders_2(sK1,sK2,sK7(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f240,plain,
    ( spl8_30
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | ~ r1_orders_2(sK1,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f393,plain,
    ( r2_hidden(sK7(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK7(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2),u1_struct_0(sK1))
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(resolution,[],[f233,f241])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK1,sK2,X0)
        | r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f240])).

fof(f233,plain,
    ( r1_orders_2(sK1,sK2,sK7(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2))
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f231])).

fof(f381,plain,
    ( spl8_2
    | spl8_19
    | ~ spl8_6
    | ~ spl8_3
    | spl8_4
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f377,f87,f50,f65,f60,f75,f158,f55])).

fof(f55,plain,
    ( spl8_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f158,plain,
    ( spl8_19
  <=> sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) = sK7(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f75,plain,
    ( spl8_6
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f60,plain,
    ( spl8_3
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f65,plain,
    ( spl8_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f50,plain,
    ( spl8_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f87,plain,
    ( spl8_8
  <=> r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f377,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) = sK7(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f89,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | sK7(X0,X2,X3) = X0
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X2))
        & l1_waybel_0(X2,X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

fof(f89,plain,
    ( r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f380,plain,
    ( spl8_2
    | spl8_18
    | ~ spl8_6
    | ~ spl8_3
    | spl8_4
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f376,f87,f50,f65,f60,f75,f153,f55])).

fof(f376,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK7(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f89,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | m1_subset_1(sK7(X0,X2,X3),u1_struct_0(X2))
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f379,plain,
    ( spl8_2
    | spl8_29
    | ~ spl8_6
    | ~ spl8_3
    | spl8_4
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f375,f87,f50,f65,f60,f75,f231,f55])).

fof(f375,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK7(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f89,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r1_orders_2(X2,X3,sK7(X0,X2,X3))
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f378,plain,
    ( spl8_5
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f374,f87,f83,f70])).

fof(f70,plain,
    ( spl8_5
  <=> u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f83,plain,
    ( spl8_7
  <=> r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f374,plain,
    ( ~ r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)
    | ~ spl8_8 ),
    inference(resolution,[],[f89,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | ~ r2_hidden(sK6(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f372,plain,
    ( sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) != sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ r2_hidden(sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))),a_3_0_waybel_9(sK0,sK1,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f371,plain,
    ( ~ spl8_32
    | ~ spl8_6
    | spl8_47
    | ~ spl8_23
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f361,f214,f187,f368,f75,f255])).

fof(f255,plain,
    ( spl8_32
  <=> m1_subset_1(sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f368,plain,
    ( spl8_47
  <=> r2_hidden(sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))),a_3_0_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f187,plain,
    ( spl8_23
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_hidden(X1,a_3_0_waybel_9(sK0,sK1,X0))
        | ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f214,plain,
    ( spl8_27
  <=> r1_orders_2(sK1,sK2,sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f361,plain,
    ( r2_hidden(sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | ~ spl8_23
    | ~ spl8_27 ),
    inference(resolution,[],[f216,f188])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,X0,X1)
        | r2_hidden(X1,a_3_0_waybel_9(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f187])).

fof(f216,plain,
    ( r1_orders_2(sK1,sK2,sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f214])).

fof(f260,plain,
    ( spl8_25
    | ~ spl8_7
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f253,f194,f83,f201])).

fof(f201,plain,
    ( spl8_25
  <=> sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) = sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f194,plain,
    ( spl8_24
  <=> ! [X0] :
        ( sK5(sK1,sK2,X0) = X0
        | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f253,plain,
    ( sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) = sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)))
    | ~ spl8_7
    | ~ spl8_24 ),
    inference(resolution,[],[f85,f195])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | sK5(sK1,sK2,X0) = X0 )
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f194])).

fof(f85,plain,
    ( r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f259,plain,
    ( spl8_27
    | ~ spl8_7
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f252,f207,f83,f214])).

fof(f207,plain,
    ( spl8_26
  <=> ! [X0] :
        ( r1_orders_2(sK1,sK2,sK5(sK1,sK2,X0))
        | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f252,plain,
    ( r1_orders_2(sK1,sK2,sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))))
    | ~ spl8_7
    | ~ spl8_26 ),
    inference(resolution,[],[f85,f208])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | r1_orders_2(sK1,sK2,sK5(sK1,sK2,X0)) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f207])).

fof(f258,plain,
    ( spl8_32
    | ~ spl8_7
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f251,f220,f83,f255])).

fof(f220,plain,
    ( spl8_28
  <=> ! [X0] :
        ( m1_subset_1(sK5(sK1,sK2,X0),u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f251,plain,
    ( m1_subset_1(sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | ~ spl8_7
    | ~ spl8_28 ),
    inference(resolution,[],[f85,f221])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | m1_subset_1(sK5(sK1,sK2,X0),u1_struct_0(sK1)) )
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f220])).

fof(f244,plain,
    ( spl8_5
    | spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f243,f87,f83,f70])).

fof(f243,plain,
    ( r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)
    | spl8_8 ),
    inference(resolution,[],[f88,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r2_hidden(sK6(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f88,plain,
    ( ~ r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f242,plain,
    ( spl8_30
    | ~ spl8_14
    | spl8_2
    | ~ spl8_6
    | ~ spl8_3
    | spl8_4
    | ~ spl8_1
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f238,f115,f50,f65,f60,f75,f55,f126,f240])).

fof(f126,plain,
    ( spl8_14
  <=> l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f115,plain,
    ( spl8_12
  <=> v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK2,X0)
        | r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) )
    | ~ spl8_12 ),
    inference(resolution,[],[f44,f117])).

fof(f117,plain,
    ( v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f115])).

fof(f44,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X2,X5)
      | r2_hidden(X5,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X2,X5)
      | r2_hidden(X5,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X4 != X5
      | ~ r1_orders_2(X1,X2,X5)
      | r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X0)
                    & v6_waybel_0(X3,X0) )
                 => ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).

fof(f222,plain,
    ( spl8_28
    | ~ spl8_14
    | spl8_2
    | ~ spl8_6
    | ~ spl8_3
    | spl8_4
    | ~ spl8_1
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f218,f115,f50,f65,f60,f75,f55,f126,f220])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
        | m1_subset_1(sK5(sK1,sK2,X0),u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) )
    | ~ spl8_12 ),
    inference(resolution,[],[f47,f117])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | m1_subset_1(sK5(X1,X2,X4),u1_struct_0(X1))
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | m1_subset_1(sK5(X1,X2,X4),u1_struct_0(X1))
      | ~ r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f209,plain,
    ( spl8_26
    | ~ spl8_14
    | spl8_2
    | ~ spl8_6
    | ~ spl8_3
    | spl8_4
    | ~ spl8_1
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f205,f115,f50,f65,f60,f75,f55,f126,f207])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
        | r1_orders_2(sK1,sK2,sK5(sK1,sK2,X0))
        | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) )
    | ~ spl8_12 ),
    inference(resolution,[],[f45,f117])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | r1_orders_2(X1,X2,sK5(X1,X2,X4))
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | r1_orders_2(X1,X2,sK5(X1,X2,X4))
      | ~ r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f196,plain,
    ( spl8_24
    | ~ spl8_14
    | spl8_2
    | ~ spl8_6
    | ~ spl8_3
    | spl8_4
    | ~ spl8_1
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f192,f115,f50,f65,f60,f75,f55,f126,f194])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
        | sK5(sK1,sK2,X0) = X0
        | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) )
    | ~ spl8_12 ),
    inference(resolution,[],[f46,f117])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | sK5(X1,X2,X4) = X4
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | sK5(X1,X2,X4) = X4
      | ~ r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f189,plain,
    ( spl8_23
    | spl8_2
    | spl8_4
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f184,f60,f50,f65,f55,f187])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X0,X1)
        | r2_hidden(X1,a_3_0_waybel_9(sK0,sK1,X0)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f48,f62])).

fof(f62,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f48,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ l1_waybel_0(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ r1_orders_2(X2,X3,X4)
      | r2_hidden(X4,a_3_0_waybel_9(X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | X0 != X4
      | ~ r1_orders_2(X2,X3,X4)
      | r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f129,plain,
    ( spl8_14
    | ~ spl8_6
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f124,f121,f75,f126])).

fof(f121,plain,
    ( spl8_13
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | l1_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f124,plain,
    ( l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | ~ spl8_6
    | ~ spl8_13 ),
    inference(resolution,[],[f122,f77])).

fof(f77,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | l1_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0) )
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,
    ( spl8_13
    | spl8_2
    | spl8_4
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f119,f60,f50,f65,f55,f121])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | l1_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0) )
    | ~ spl8_3 ),
    inference(resolution,[],[f35,f62])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(f118,plain,
    ( spl8_12
    | ~ spl8_6
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f113,f110,f75,f115])).

fof(f110,plain,
    ( spl8_11
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v6_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f113,plain,
    ( v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | ~ spl8_6
    | ~ spl8_11 ),
    inference(resolution,[],[f111,f77])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v6_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( spl8_11
    | spl8_2
    | spl8_4
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f108,f60,f50,f65,f55,f110])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v6_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0) )
    | ~ spl8_3 ),
    inference(resolution,[],[f34,f62])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f16,f75])).

fof(f16,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_waybel_9)).

fof(f73,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f17,f70])).

fof(f17,plain,(
    u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) != a_3_0_waybel_9(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f68,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f18,f65])).

fof(f18,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f8])).

% (18919)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (18918)Refutation not found, incomplete strategy% (18918)------------------------------
% (18918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18918)Termination reason: Refutation not found, incomplete strategy

% (18918)Memory used [KB]: 6524
% (18918)Time elapsed: 0.114 s
% (18918)------------------------------
% (18918)------------------------------
% (18921)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (18905)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (18914)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (18899)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (18902)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f63,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f19,f60])).

fof(f19,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f58,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f20,f55])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
