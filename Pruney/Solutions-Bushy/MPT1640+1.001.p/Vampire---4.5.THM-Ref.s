%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1640+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:14 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 290 expanded)
%              Number of leaves         :   27 ( 129 expanded)
%              Depth                    :   12
%              Number of atoms          :  582 (1346 expanded)
%              Number of equality atoms :   33 ( 193 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f212,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f63,f68,f73,f80,f93,f100,f109,f117,f122,f127,f151,f156,f165,f192,f206])).

fof(f206,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f204,f52])).

fof(f52,plain,
    ( v5_orders_2(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_3
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f204,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f203,f57])).

fof(f57,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f203,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f202,f72])).

fof(f72,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_7
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f202,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl4_5
    | ~ spl4_6
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f201,f67])).

fof(f67,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f201,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl4_5
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f200,f164])).

fof(f164,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_18
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f200,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl4_5
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f195,f62])).

fof(f62,plain,
    ( sK1 != sK2
    | spl4_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f195,plain,
    ( sK1 = sK2
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl4_19 ),
    inference(resolution,[],[f191,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,X1)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(f191,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl4_19
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f192,plain,
    ( spl4_19
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f169,f153,f91,f70,f65,f189])).

fof(f91,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k6_waybel_0(sK0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f153,plain,
    ( spl4_17
  <=> r2_hidden(sK2,k6_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f169,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f168,f67])).

fof(f168,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f167,f72])).

fof(f167,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(resolution,[],[f155,f92])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k6_waybel_0(sK0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f155,plain,
    ( r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f153])).

fof(f165,plain,
    ( spl4_18
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f160,f148,f115,f65,f162])).

fof(f115,plain,
    ( spl4_13
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k6_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f148,plain,
    ( spl4_16
  <=> r2_hidden(sK1,k6_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f160,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f157,f67])).

fof(f157,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1)
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(resolution,[],[f150,f116])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f150,plain,
    ( r2_hidden(sK1,k6_waybel_0(sK0,sK1))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f156,plain,
    ( spl4_17
    | spl4_1
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f146,f124,f77,f70,f55,f40,f153])).

fof(f40,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f77,plain,
    ( spl4_8
  <=> k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f124,plain,
    ( spl4_15
  <=> r1_orders_2(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f146,plain,
    ( r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f145,f79])).

fof(f79,plain,
    ( k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f145,plain,
    ( r2_hidden(sK2,k6_waybel_0(sK0,sK2))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f144,f42])).

fof(f42,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f144,plain,
    ( r2_hidden(sK2,k6_waybel_0(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f143,f57])).

fof(f143,plain,
    ( r2_hidden(sK2,k6_waybel_0(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f140,f72])).

fof(f140,plain,
    ( r2_hidden(sK2,k6_waybel_0(sK0,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_15 ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,
    ( r2_hidden(sK2,k6_waybel_0(sK0,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_15 ),
    inference(resolution,[],[f126,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(X2,k6_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_0)).

fof(f126,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f124])).

fof(f151,plain,
    ( spl4_16
    | spl4_1
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f136,f119,f65,f55,f40,f148])).

fof(f119,plain,
    ( spl4_14
  <=> r1_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f136,plain,
    ( r2_hidden(sK1,k6_waybel_0(sK0,sK1))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f135,f42])).

fof(f135,plain,
    ( r2_hidden(sK1,k6_waybel_0(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f134,f57])).

fof(f134,plain,
    ( r2_hidden(sK1,k6_waybel_0(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f131,f67])).

fof(f131,plain,
    ( r2_hidden(sK1,k6_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_14 ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( r2_hidden(sK1,k6_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_14 ),
    inference(resolution,[],[f121,f32])).

fof(f121,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f127,plain,
    ( spl4_15
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f113,f107,f70,f124])).

fof(f107,plain,
    ( spl4_12
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f113,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(resolution,[],[f108,f72])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f122,plain,
    ( spl4_14
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f112,f107,f65,f119])).

fof(f112,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(resolution,[],[f108,f67])).

fof(f117,plain,
    ( spl4_13
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f111,f91,f77,f70,f115])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0) )
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f110,f72])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0) )
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(superposition,[],[f92,f79])).

fof(f109,plain,
    ( spl4_12
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f105,f98,f55,f45,f40,f107])).

fof(f45,plain,
    ( spl4_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f98,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( ~ r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f104,f42])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X0)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f103,f47])).

fof(f47,plain,
    ( v3_orders_2(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f102,f57])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_11 ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_11 ),
    inference(resolution,[],[f99,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f38,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP3(X0) ) ),
    inference(cnf_transformation,[],[f37_D])).

fof(f37_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(X0))
    <=> ~ sP3(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP3(X0) ) ),
    inference(general_splitting,[],[f34,f37_D])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,
    ( spl4_11
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f96,f55,f45,f40,f98])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f95,f42])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f94,f47])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f35,f57])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f93,plain,
    ( spl4_10
    | spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f89,f55,f40,f91])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k6_waybel_0(sK0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X0) )
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f88,f42])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k6_waybel_0(sK0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X0)
        | v2_struct_0(sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f31,f57])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X2,k6_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f29,f77])).

fof(f29,plain,(
    k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK1 != sK2
    & k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k6_waybel_0(sK0,X1) = k6_waybel_0(sK0,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & k6_waybel_0(sK0,X1) = k6_waybel_0(sK0,X2)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( sK1 != X2
          & k6_waybel_0(sK0,X2) = k6_waybel_0(sK0,sK1)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k6_waybel_0(sK0,X2) = k6_waybel_0(sK0,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( sK1 != sK2
      & k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_0)).

fof(f73,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f28,f70])).

fof(f28,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f27,f65])).

fof(f27,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f30,f60])).

fof(f30,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f23,f40])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

%------------------------------------------------------------------------------
