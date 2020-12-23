%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:08 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 663 expanded)
%              Number of leaves         :   43 ( 295 expanded)
%              Depth                    :   19
%              Number of atoms          : 1027 (4474 expanded)
%              Number of equality atoms :   19 (  27 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f773,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f113,f120,f124,f132,f136,f140,f144,f148,f152,f165,f197,f250,f256,f265,f269,f275,f280,f284,f291,f310,f330,f334,f344,f350,f354,f357,f358,f376,f382,f385,f387,f388,f428,f430,f685,f706,f718,f762,f764])).

fof(f764,plain,
    ( spl4_38
    | ~ spl4_90 ),
    inference(avatar_split_clause,[],[f695,f683,f332])).

fof(f332,plain,
    ( spl4_38
  <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f683,plain,
    ( spl4_90
  <=> r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f695,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl4_90 ),
    inference(resolution,[],[f684,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f684,plain,
    ( r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)))
    | ~ spl4_90 ),
    inference(avatar_component_clause,[],[f683])).

fof(f762,plain,
    ( spl4_10
    | spl4_12
    | ~ spl4_11
    | ~ spl4_9
    | spl4_33
    | ~ spl4_18
    | ~ spl4_95 ),
    inference(avatar_split_clause,[],[f753,f716,f195,f307,f130,f138,f142,f134])).

fof(f134,plain,
    ( spl4_10
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f142,plain,
    ( spl4_12
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f138,plain,
    ( spl4_11
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f130,plain,
    ( spl4_9
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f307,plain,
    ( spl4_33
  <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f195,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f716,plain,
    ( spl4_95
  <=> r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_95])])).

fof(f753,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ spl4_18
    | ~ spl4_95 ),
    inference(superposition,[],[f717,f196])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f195])).

fof(f717,plain,
    ( r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl4_95 ),
    inference(avatar_component_clause,[],[f716])).

fof(f718,plain,
    ( spl4_95
    | ~ spl4_37
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f711,f332,f328,f716])).

fof(f328,plain,
    ( spl4_37
  <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f711,plain,
    ( r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl4_37
    | ~ spl4_38 ),
    inference(resolution,[],[f329,f419])).

fof(f419,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(u1_struct_0(sK3),X1)
        | r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(X1,u1_struct_0(sK2))) )
    | ~ spl4_38 ),
    inference(resolution,[],[f333,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f333,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f332])).

fof(f329,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f328])).

fof(f706,plain,
    ( spl4_37
    | ~ spl4_90 ),
    inference(avatar_split_clause,[],[f694,f683,f328])).

fof(f694,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl4_90 ),
    inference(resolution,[],[f684,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f685,plain,
    ( ~ spl4_6
    | spl4_90
    | ~ spl4_11
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f673,f254,f138,f683,f110])).

fof(f110,plain,
    ( spl4_6
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f254,plain,
    ( spl4_25
  <=> ! [X0] :
        ( ~ r1_tsep_1(sK3,X0)
        | r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f673,plain,
    ( r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)))
    | ~ r1_tsep_1(sK3,sK1)
    | ~ spl4_11
    | ~ spl4_25 ),
    inference(resolution,[],[f255,f139])).

fof(f139,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0)))
        | ~ r1_tsep_1(sK3,X0) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f254])).

fof(f430,plain,
    ( ~ spl4_29
    | spl4_50 ),
    inference(avatar_split_clause,[],[f429,f426,f278])).

fof(f278,plain,
    ( spl4_29
  <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f426,plain,
    ( spl4_50
  <=> l1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f429,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl4_50 ),
    inference(resolution,[],[f427,f76])).

fof(f76,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f427,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | spl4_50 ),
    inference(avatar_component_clause,[],[f426])).

fof(f428,plain,
    ( ~ spl4_39
    | ~ spl4_50
    | spl4_4
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f420,f307,f98,f426,f339])).

fof(f339,plain,
    ( spl4_39
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f98,plain,
    ( spl4_4
  <=> r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f420,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_struct_0(sK3)
    | ~ spl4_33 ),
    inference(resolution,[],[f308,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f308,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f307])).

fof(f388,plain,
    ( ~ spl4_16
    | ~ spl4_15
    | ~ spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f263,f95,f89,f160,f163])).

fof(f163,plain,
    ( spl4_16
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f160,plain,
    ( spl4_15
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f89,plain,
    ( spl4_1
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f95,plain,
    ( spl4_3
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f263,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | spl4_3 ),
    inference(resolution,[],[f117,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f156,f76])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f80,f76])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f117,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f387,plain,
    ( ~ spl4_29
    | ~ spl4_15
    | ~ spl4_2
    | spl4_4 ),
    inference(avatar_split_clause,[],[f386,f98,f92,f160,f278])).

fof(f92,plain,
    ( spl4_2
  <=> r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f386,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl4_4 ),
    inference(resolution,[],[f115,f157])).

fof(f115,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f385,plain,
    ( ~ spl4_13
    | ~ spl4_9
    | spl4_16 ),
    inference(avatar_split_clause,[],[f384,f163,f130,f146])).

fof(f146,plain,
    ( spl4_13
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f384,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_9
    | spl4_16 ),
    inference(resolution,[],[f383,f131])).

fof(f131,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f383,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | spl4_16 ),
    inference(resolution,[],[f164,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f164,plain,
    ( ~ l1_pre_topc(sK2)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f382,plain,
    ( ~ spl4_16
    | spl4_44 ),
    inference(avatar_split_clause,[],[f381,f374,f163])).

fof(f374,plain,
    ( spl4_44
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f381,plain,
    ( ~ l1_pre_topc(sK2)
    | spl4_44 ),
    inference(resolution,[],[f375,f76])).

fof(f375,plain,
    ( ~ l1_struct_0(sK2)
    | spl4_44 ),
    inference(avatar_component_clause,[],[f374])).

fof(f376,plain,
    ( ~ spl4_39
    | ~ spl4_44
    | spl4_3
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f370,f332,f95,f374,f339])).

fof(f370,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | ~ spl4_38 ),
    inference(resolution,[],[f333,f75])).

fof(f358,plain,
    ( ~ spl4_15
    | ~ spl4_27
    | ~ spl4_6
    | spl4_5 ),
    inference(avatar_split_clause,[],[f270,f102,f110,f267,f160])).

fof(f267,plain,
    ( spl4_27
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f102,plain,
    ( spl4_5
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f270,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK3)
    | spl4_5 ),
    inference(resolution,[],[f106,f157])).

fof(f106,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f357,plain,
    ( ~ spl4_13
    | ~ spl4_11
    | spl4_27 ),
    inference(avatar_split_clause,[],[f356,f267,f138,f146])).

fof(f356,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_11
    | spl4_27 ),
    inference(resolution,[],[f355,f139])).

fof(f355,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | spl4_27 ),
    inference(resolution,[],[f268,f77])).

fof(f268,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_27 ),
    inference(avatar_component_clause,[],[f267])).

fof(f354,plain,
    ( ~ spl4_27
    | spl4_40 ),
    inference(avatar_split_clause,[],[f353,f342,f267])).

fof(f342,plain,
    ( spl4_40
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f353,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_40 ),
    inference(resolution,[],[f343,f76])).

fof(f343,plain,
    ( ~ l1_struct_0(sK1)
    | spl4_40 ),
    inference(avatar_component_clause,[],[f342])).

fof(f350,plain,
    ( ~ spl4_15
    | spl4_39 ),
    inference(avatar_split_clause,[],[f349,f339,f160])).

fof(f349,plain,
    ( ~ l1_pre_topc(sK3)
    | spl4_39 ),
    inference(resolution,[],[f340,f76])).

fof(f340,plain,
    ( ~ l1_struct_0(sK3)
    | spl4_39 ),
    inference(avatar_component_clause,[],[f339])).

fof(f344,plain,
    ( ~ spl4_39
    | ~ spl4_40
    | spl4_6
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f335,f328,f110,f342,f339])).

fof(f335,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ spl4_37 ),
    inference(resolution,[],[f329,f75])).

fof(f334,plain,
    ( spl4_10
    | spl4_12
    | ~ spl4_11
    | ~ spl4_9
    | spl4_38
    | ~ spl4_18
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f321,f307,f195,f332,f130,f138,f142,f134])).

fof(f321,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ spl4_18
    | ~ spl4_33 ),
    inference(resolution,[],[f308,f209])).

fof(f209,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X2,u1_struct_0(k1_tsep_1(sK0,X0,X1)))
        | r1_xboole_0(X2,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(X1) )
    | ~ spl4_18 ),
    inference(superposition,[],[f83,f196])).

fof(f330,plain,
    ( spl4_10
    | spl4_12
    | ~ spl4_11
    | ~ spl4_9
    | spl4_37
    | ~ spl4_18
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f320,f307,f195,f328,f130,f138,f142,f134])).

fof(f320,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ spl4_18
    | ~ spl4_33 ),
    inference(resolution,[],[f308,f210])).

fof(f210,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_xboole_0(X5,u1_struct_0(k1_tsep_1(sK0,X3,X4)))
        | r1_xboole_0(X5,u1_struct_0(X3))
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | v2_struct_0(X4) )
    | ~ spl4_18 ),
    inference(superposition,[],[f82,f196])).

fof(f310,plain,
    ( spl4_33
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f298,f289,f307])).

fof(f289,plain,
    ( spl4_30
  <=> r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f298,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl4_30 ),
    inference(resolution,[],[f290,f82])).

fof(f290,plain,
    ( r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f289])).

fof(f291,plain,
    ( ~ spl4_24
    | spl4_30
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f286,f273,f98,f289,f241])).

fof(f241,plain,
    ( spl4_24
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f273,plain,
    ( spl4_28
  <=> ! [X0] :
        ( ~ r1_tsep_1(sK3,X0)
        | r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f286,plain,
    ( r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(resolution,[],[f274,f99])).

fof(f99,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f274,plain,
    ( ! [X0] :
        ( ~ r1_tsep_1(sK3,X0)
        | r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f273])).

fof(f284,plain,
    ( spl4_14
    | spl4_12
    | ~ spl4_11
    | spl4_10
    | ~ spl4_9
    | ~ spl4_13
    | spl4_29 ),
    inference(avatar_split_clause,[],[f283,f278,f146,f130,f134,f138,f142,f150])).

fof(f150,plain,
    ( spl4_14
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f283,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | spl4_29 ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_29 ),
    inference(resolution,[],[f281,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f281,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0)
        | ~ l1_pre_topc(X0) )
    | spl4_29 ),
    inference(resolution,[],[f279,f77])).

fof(f279,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f278])).

fof(f280,plain,
    ( ~ spl4_15
    | ~ spl4_29
    | ~ spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f276,f92,f98,f278,f160])).

fof(f276,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK3)
    | spl4_2 ),
    inference(resolution,[],[f105,f157])).

fof(f105,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f275,plain,
    ( spl4_28
    | ~ spl4_7
    | ~ spl4_24
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f271,f146,f98,f241,f122,f273])).

fof(f122,plain,
    ( spl4_7
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f271,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ r1_tsep_1(sK3,X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0))) )
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(resolution,[],[f99,f233])).

fof(f233,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ r1_tsep_1(X1,X2)
        | ~ m1_pre_topc(X2,sK0)
        | r1_xboole_0(u1_struct_0(X1),k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2))) )
    | ~ spl4_13 ),
    inference(resolution,[],[f231,f147])).

fof(f147,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f231,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(X2,sK0)
        | ~ r1_tsep_1(X0,X2)
        | ~ m1_pre_topc(X0,X3)
        | ~ r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | r1_xboole_0(u1_struct_0(X0),k2_xboole_0(u1_struct_0(X2),u1_struct_0(X1))) )
    | ~ spl4_13 ),
    inference(resolution,[],[f222,f147])).

fof(f222,plain,
    ( ! [X6,X4,X7,X5,X3] :
        ( ~ l1_pre_topc(X7)
        | ~ r1_tsep_1(X3,X5)
        | ~ m1_pre_topc(X4,sK0)
        | ~ r1_tsep_1(X3,X4)
        | ~ m1_pre_topc(X3,X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(X5,X7)
        | r1_xboole_0(u1_struct_0(X3),k2_xboole_0(u1_struct_0(X4),u1_struct_0(X5))) )
    | ~ spl4_13 ),
    inference(resolution,[],[f190,f77])).

fof(f190,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ l1_pre_topc(X3)
        | r1_xboole_0(u1_struct_0(X2),k2_xboole_0(u1_struct_0(X4),u1_struct_0(X3)))
        | ~ r1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X4,sK0)
        | ~ r1_tsep_1(X2,X4)
        | ~ m1_pre_topc(X2,X5)
        | ~ l1_pre_topc(X5) )
    | ~ spl4_13 ),
    inference(resolution,[],[f187,f77])).

fof(f187,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ r1_tsep_1(X0,X2)
        | r1_xboole_0(u1_struct_0(X0),k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(X1,sK0)
        | ~ r1_tsep_1(X0,X1) )
    | ~ spl4_13 ),
    inference(resolution,[],[f177,f147])).

fof(f177,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ l1_pre_topc(X5)
      | ~ r1_tsep_1(X2,X3)
      | ~ r1_tsep_1(X2,X4)
      | r1_xboole_0(u1_struct_0(X2),k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4)))
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(X3,X5)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f175,f77])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ r1_tsep_1(X1,X2)
      | ~ r1_tsep_1(X1,X0)
      | r1_xboole_0(u1_struct_0(X1),k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ r1_tsep_1(X1,X2)
      | ~ r1_tsep_1(X1,X0)
      | r1_xboole_0(u1_struct_0(X1),k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0)))
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f173,f76])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ r1_tsep_1(X0,X2)
      | r1_xboole_0(u1_struct_0(X0),k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f172,f76])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X2)
      | r1_xboole_0(u1_struct_0(X0),k2_xboole_0(u1_struct_0(X2),u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X0,X2)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f171,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),X2)
      | ~ r1_tsep_1(X0,X1)
      | r1_xboole_0(u1_struct_0(X0),k2_xboole_0(X2,u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f170,f76])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),X2)
      | r1_xboole_0(u1_struct_0(X0),k2_xboole_0(X2,u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f167,f76])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X0)
      | ~ r1_xboole_0(u1_struct_0(X0),X2)
      | r1_xboole_0(u1_struct_0(X0),k2_xboole_0(X2,u1_struct_0(X1))) ) ),
    inference(resolution,[],[f74,f81])).

fof(f269,plain,
    ( ~ spl4_27
    | ~ spl4_15
    | ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f262,f110,f102,f160,f267])).

fof(f262,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | spl4_6 ),
    inference(resolution,[],[f116,f157])).

fof(f116,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f265,plain,
    ( ~ spl4_13
    | ~ spl4_7
    | spl4_15 ),
    inference(avatar_split_clause,[],[f264,f160,f122,f146])).

fof(f264,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_7
    | spl4_15 ),
    inference(resolution,[],[f251,f123])).

fof(f123,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl4_15 ),
    inference(resolution,[],[f161,f77])).

fof(f161,plain,
    ( ~ l1_pre_topc(sK3)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f160])).

fof(f256,plain,
    ( spl4_25
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f252,f146,f95,f130,f122,f254])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ r1_tsep_1(sK3,X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))) )
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(resolution,[],[f96,f233])).

fof(f96,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f250,plain,
    ( spl4_14
    | ~ spl4_13
    | spl4_12
    | ~ spl4_11
    | spl4_10
    | ~ spl4_9
    | spl4_24 ),
    inference(avatar_split_clause,[],[f245,f241,f130,f134,f138,f142,f146,f150])).

fof(f245,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_24 ),
    inference(resolution,[],[f242,f86])).

fof(f242,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_24 ),
    inference(avatar_component_clause,[],[f241])).

fof(f197,plain,
    ( spl4_14
    | spl4_18
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f191,f146,f195,f150])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0))
        | v2_struct_0(sK0) )
    | ~ spl4_13 ),
    inference(resolution,[],[f155,f147])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f154,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f153,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f87,f86])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f165,plain,
    ( ~ spl4_15
    | ~ spl4_16
    | ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f158,f89,f95,f163,f160])).

fof(f158,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | spl4_1 ),
    inference(resolution,[],[f157,f107])).

fof(f107,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f152,plain,(
    ~ spl4_14 ),
    inference(avatar_split_clause,[],[f30,f150])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
        & ( ~ r1_tsep_1(sK3,sK2)
          | ~ r1_tsep_1(sK3,sK1) ) )
      | ( r1_tsep_1(sK3,sK2)
        & r1_tsep_1(sK3,sK1)
        & ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) )
      | ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
        & ( ~ r1_tsep_1(sK2,sK3)
          | ~ r1_tsep_1(sK1,sK3) ) )
      | ( r1_tsep_1(sK2,sK3)
        & r1_tsep_1(sK1,sK3)
        & ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ) )
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                        & ( ~ r1_tsep_1(X3,X2)
                          | ~ r1_tsep_1(X3,X1) ) )
                      | ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1)
                        & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                        & ( ~ r1_tsep_1(X2,X3)
                          | ~ r1_tsep_1(X1,X3) ) )
                      | ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3)
                        & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( r1_tsep_1(X3,k1_tsep_1(sK0,X1,X2))
                      & ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) ) )
                    | ( r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1)
                      & ~ r1_tsep_1(X3,k1_tsep_1(sK0,X1,X2)) )
                    | ( r1_tsep_1(k1_tsep_1(sK0,X1,X2),X3)
                      & ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) ) )
                    | ( r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3)
                      & ~ r1_tsep_1(k1_tsep_1(sK0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( r1_tsep_1(X3,k1_tsep_1(sK0,X1,X2))
                    & ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,X1) ) )
                  | ( r1_tsep_1(X3,X2)
                    & r1_tsep_1(X3,X1)
                    & ~ r1_tsep_1(X3,k1_tsep_1(sK0,X1,X2)) )
                  | ( r1_tsep_1(k1_tsep_1(sK0,X1,X2),X3)
                    & ( ~ r1_tsep_1(X2,X3)
                      | ~ r1_tsep_1(X1,X3) ) )
                  | ( r1_tsep_1(X2,X3)
                    & r1_tsep_1(X1,X3)
                    & ~ r1_tsep_1(k1_tsep_1(sK0,X1,X2),X3) ) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( r1_tsep_1(X3,k1_tsep_1(sK0,sK1,X2))
                  & ( ~ r1_tsep_1(X3,X2)
                    | ~ r1_tsep_1(X3,sK1) ) )
                | ( r1_tsep_1(X3,X2)
                  & r1_tsep_1(X3,sK1)
                  & ~ r1_tsep_1(X3,k1_tsep_1(sK0,sK1,X2)) )
                | ( r1_tsep_1(k1_tsep_1(sK0,sK1,X2),X3)
                  & ( ~ r1_tsep_1(X2,X3)
                    | ~ r1_tsep_1(sK1,X3) ) )
                | ( r1_tsep_1(X2,X3)
                  & r1_tsep_1(sK1,X3)
                  & ~ r1_tsep_1(k1_tsep_1(sK0,sK1,X2),X3) ) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( r1_tsep_1(X3,k1_tsep_1(sK0,sK1,X2))
                & ( ~ r1_tsep_1(X3,X2)
                  | ~ r1_tsep_1(X3,sK1) ) )
              | ( r1_tsep_1(X3,X2)
                & r1_tsep_1(X3,sK1)
                & ~ r1_tsep_1(X3,k1_tsep_1(sK0,sK1,X2)) )
              | ( r1_tsep_1(k1_tsep_1(sK0,sK1,X2),X3)
                & ( ~ r1_tsep_1(X2,X3)
                  | ~ r1_tsep_1(sK1,X3) ) )
              | ( r1_tsep_1(X2,X3)
                & r1_tsep_1(sK1,X3)
                & ~ r1_tsep_1(k1_tsep_1(sK0,sK1,X2),X3) ) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK2))
              & ( ~ r1_tsep_1(X3,sK2)
                | ~ r1_tsep_1(X3,sK1) ) )
            | ( r1_tsep_1(X3,sK2)
              & r1_tsep_1(X3,sK1)
              & ~ r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK2)) )
            | ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),X3)
              & ( ~ r1_tsep_1(sK2,X3)
                | ~ r1_tsep_1(sK1,X3) ) )
            | ( r1_tsep_1(sK2,X3)
              & r1_tsep_1(sK1,X3)
              & ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),X3) ) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( ( ( r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK2))
            & ( ~ r1_tsep_1(X3,sK2)
              | ~ r1_tsep_1(X3,sK1) ) )
          | ( r1_tsep_1(X3,sK2)
            & r1_tsep_1(X3,sK1)
            & ~ r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK2)) )
          | ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),X3)
            & ( ~ r1_tsep_1(sK2,X3)
              | ~ r1_tsep_1(sK1,X3) ) )
          | ( r1_tsep_1(sK2,X3)
            & r1_tsep_1(sK1,X3)
            & ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),X3) ) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
          & ( ~ r1_tsep_1(sK3,sK2)
            | ~ r1_tsep_1(sK3,sK1) ) )
        | ( r1_tsep_1(sK3,sK2)
          & r1_tsep_1(sK3,sK1)
          & ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) )
        | ( r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
          & ( ~ r1_tsep_1(sK2,sK3)
            | ~ r1_tsep_1(sK1,sK3) ) )
        | ( r1_tsep_1(sK2,sK3)
          & r1_tsep_1(sK1,sK3)
          & ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) ) )
                    | ( r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1)
                      & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) ) )
                    | ( r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3)
                      & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) ) )
                    | ( r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1)
                      & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) ) )
                    | ( r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3)
                      & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ~ ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                          & ~ ( r1_tsep_1(X3,X2)
                              & r1_tsep_1(X3,X1) ) )
                      & ~ ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1)
                          & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      & ~ ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                          & ~ ( r1_tsep_1(X2,X3)
                              & r1_tsep_1(X1,X3) ) )
                      & ~ ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3)
                          & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
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
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ~ ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                          & ~ ( r1_tsep_1(X3,X2)
                              & r1_tsep_1(X3,X1) ) )
                      & ~ ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1)
                          & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      & ~ ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                          & ~ ( r1_tsep_1(X2,X3)
                              & r1_tsep_1(X1,X3) ) )
                      & ~ ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3)
                          & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                        & ~ ( r1_tsep_1(X3,X2)
                            & r1_tsep_1(X3,X1) ) )
                    & ~ ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1)
                        & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ~ ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                        & ~ ( r1_tsep_1(X2,X3)
                            & r1_tsep_1(X1,X3) ) )
                    & ~ ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3)
                        & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tmap_1)).

fof(f148,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f31,f146])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f144,plain,(
    ~ spl4_12 ),
    inference(avatar_split_clause,[],[f32,f142])).

fof(f32,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f140,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f33,f138])).

fof(f33,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f136,plain,(
    ~ spl4_10 ),
    inference(avatar_split_clause,[],[f34,f134])).

fof(f34,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f132,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f35,f130])).

fof(f35,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f124,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f37,f122])).

fof(f37,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f120,plain,
    ( ~ spl4_2
    | ~ spl4_5
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f38,f95,f110,f98,f89,f102,f92])).

fof(f38,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ r1_tsep_1(sK1,sK3)
    | ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f113,plain,
    ( spl4_5
    | spl4_2
    | spl4_6
    | spl4_4 ),
    inference(avatar_split_clause,[],[f66,f98,f110,f92,f102])).

fof(f66,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK3,sK1)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f100,plain,
    ( spl4_1
    | spl4_2
    | spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f73,f98,f95,f92,f89])).

fof(f73,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK3,sK2)
    | r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:29:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (5350)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.47  % (5348)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.47  % (5350)Refutation not found, incomplete strategy% (5350)------------------------------
% 0.22/0.47  % (5350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (5350)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (5350)Memory used [KB]: 6140
% 0.22/0.47  % (5350)Time elapsed: 0.043 s
% 0.22/0.47  % (5350)------------------------------
% 0.22/0.47  % (5350)------------------------------
% 0.22/0.48  % (5341)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (5349)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (5341)Refutation not found, incomplete strategy% (5341)------------------------------
% 0.22/0.49  % (5341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (5341)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (5341)Memory used [KB]: 10618
% 0.22/0.49  % (5341)Time elapsed: 0.071 s
% 0.22/0.49  % (5341)------------------------------
% 0.22/0.49  % (5341)------------------------------
% 0.22/0.50  % (5340)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (5344)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (5355)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (5351)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (5342)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (5345)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (5346)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (5354)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (5343)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (5347)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (5360)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (5357)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (5358)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.52  % (5359)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.52  % (5352)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (5356)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.53  % (5353)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.53  % (5360)Refutation not found, incomplete strategy% (5360)------------------------------
% 0.22/0.53  % (5360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5360)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (5360)Memory used [KB]: 10618
% 0.22/0.53  % (5360)Time elapsed: 0.101 s
% 0.22/0.53  % (5360)------------------------------
% 0.22/0.53  % (5360)------------------------------
% 1.38/0.54  % (5346)Refutation found. Thanks to Tanya!
% 1.38/0.54  % SZS status Theorem for theBenchmark
% 1.38/0.54  % SZS output start Proof for theBenchmark
% 1.38/0.55  fof(f773,plain,(
% 1.38/0.55    $false),
% 1.38/0.55    inference(avatar_sat_refutation,[],[f100,f113,f120,f124,f132,f136,f140,f144,f148,f152,f165,f197,f250,f256,f265,f269,f275,f280,f284,f291,f310,f330,f334,f344,f350,f354,f357,f358,f376,f382,f385,f387,f388,f428,f430,f685,f706,f718,f762,f764])).
% 1.38/0.55  fof(f764,plain,(
% 1.38/0.55    spl4_38 | ~spl4_90),
% 1.38/0.55    inference(avatar_split_clause,[],[f695,f683,f332])).
% 1.38/0.55  fof(f332,plain,(
% 1.38/0.55    spl4_38 <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.38/0.55  fof(f683,plain,(
% 1.38/0.55    spl4_90 <=> r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).
% 1.38/0.55  fof(f695,plain,(
% 1.38/0.55    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~spl4_90),
% 1.38/0.55    inference(resolution,[],[f684,f82])).
% 1.38/0.55  fof(f82,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f20])).
% 1.38/0.55  fof(f20,plain,(
% 1.38/0.55    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.38/0.55    inference(ennf_transformation,[],[f1])).
% 1.38/0.55  fof(f1,axiom,(
% 1.38/0.55    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.38/0.55  fof(f684,plain,(
% 1.38/0.55    r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))) | ~spl4_90),
% 1.38/0.55    inference(avatar_component_clause,[],[f683])).
% 1.38/0.55  fof(f762,plain,(
% 1.38/0.55    spl4_10 | spl4_12 | ~spl4_11 | ~spl4_9 | spl4_33 | ~spl4_18 | ~spl4_95),
% 1.38/0.55    inference(avatar_split_clause,[],[f753,f716,f195,f307,f130,f138,f142,f134])).
% 1.38/0.55  fof(f134,plain,(
% 1.38/0.55    spl4_10 <=> v2_struct_0(sK2)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.38/0.55  fof(f142,plain,(
% 1.38/0.55    spl4_12 <=> v2_struct_0(sK1)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.38/0.55  fof(f138,plain,(
% 1.38/0.55    spl4_11 <=> m1_pre_topc(sK1,sK0)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.38/0.55  fof(f130,plain,(
% 1.38/0.55    spl4_9 <=> m1_pre_topc(sK2,sK0)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.38/0.55  fof(f307,plain,(
% 1.38/0.55    spl4_33 <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.38/0.55  fof(f195,plain,(
% 1.38/0.55    spl4_18 <=> ! [X1,X0] : (~m1_pre_topc(X0,sK0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(X0))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.38/0.55  fof(f716,plain,(
% 1.38/0.55    spl4_95 <=> r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_95])])).
% 1.38/0.55  fof(f753,plain,(
% 1.38/0.55    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | v2_struct_0(sK2) | (~spl4_18 | ~spl4_95)),
% 1.38/0.55    inference(superposition,[],[f717,f196])).
% 1.38/0.55  fof(f196,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0)) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(X0)) ) | ~spl4_18),
% 1.38/0.55    inference(avatar_component_clause,[],[f195])).
% 1.38/0.55  fof(f717,plain,(
% 1.38/0.55    r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl4_95),
% 1.38/0.55    inference(avatar_component_clause,[],[f716])).
% 1.38/0.55  fof(f718,plain,(
% 1.38/0.55    spl4_95 | ~spl4_37 | ~spl4_38),
% 1.38/0.55    inference(avatar_split_clause,[],[f711,f332,f328,f716])).
% 1.38/0.55  fof(f328,plain,(
% 1.38/0.55    spl4_37 <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.38/0.55  fof(f711,plain,(
% 1.38/0.55    r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (~spl4_37 | ~spl4_38)),
% 1.38/0.55    inference(resolution,[],[f329,f419])).
% 1.38/0.55  fof(f419,plain,(
% 1.38/0.55    ( ! [X1] : (~r1_xboole_0(u1_struct_0(sK3),X1) | r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(X1,u1_struct_0(sK2)))) ) | ~spl4_38),
% 1.38/0.55    inference(resolution,[],[f333,f81])).
% 1.38/0.55  fof(f81,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.38/0.55    inference(cnf_transformation,[],[f20])).
% 1.38/0.55  fof(f333,plain,(
% 1.38/0.55    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~spl4_38),
% 1.38/0.55    inference(avatar_component_clause,[],[f332])).
% 1.38/0.55  fof(f329,plain,(
% 1.38/0.55    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl4_37),
% 1.38/0.55    inference(avatar_component_clause,[],[f328])).
% 1.38/0.55  fof(f706,plain,(
% 1.38/0.55    spl4_37 | ~spl4_90),
% 1.38/0.55    inference(avatar_split_clause,[],[f694,f683,f328])).
% 1.38/0.55  fof(f694,plain,(
% 1.38/0.55    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl4_90),
% 1.38/0.55    inference(resolution,[],[f684,f83])).
% 1.38/0.55  fof(f83,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f20])).
% 1.38/0.55  fof(f685,plain,(
% 1.38/0.55    ~spl4_6 | spl4_90 | ~spl4_11 | ~spl4_25),
% 1.38/0.55    inference(avatar_split_clause,[],[f673,f254,f138,f683,f110])).
% 1.38/0.55  fof(f110,plain,(
% 1.38/0.55    spl4_6 <=> r1_tsep_1(sK3,sK1)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.38/0.55  fof(f254,plain,(
% 1.38/0.55    spl4_25 <=> ! [X0] : (~r1_tsep_1(sK3,X0) | r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.38/0.55  fof(f673,plain,(
% 1.38/0.55    r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))) | ~r1_tsep_1(sK3,sK1) | (~spl4_11 | ~spl4_25)),
% 1.38/0.55    inference(resolution,[],[f255,f139])).
% 1.38/0.55  fof(f139,plain,(
% 1.38/0.55    m1_pre_topc(sK1,sK0) | ~spl4_11),
% 1.38/0.55    inference(avatar_component_clause,[],[f138])).
% 1.38/0.55  fof(f255,plain,(
% 1.38/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))) | ~r1_tsep_1(sK3,X0)) ) | ~spl4_25),
% 1.38/0.55    inference(avatar_component_clause,[],[f254])).
% 1.38/0.55  fof(f430,plain,(
% 1.38/0.55    ~spl4_29 | spl4_50),
% 1.38/0.55    inference(avatar_split_clause,[],[f429,f426,f278])).
% 1.38/0.55  fof(f278,plain,(
% 1.38/0.55    spl4_29 <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.38/0.55  fof(f426,plain,(
% 1.38/0.55    spl4_50 <=> l1_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.38/0.55  fof(f429,plain,(
% 1.38/0.55    ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | spl4_50),
% 1.38/0.55    inference(resolution,[],[f427,f76])).
% 1.38/0.55  fof(f76,plain,(
% 1.38/0.55    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f14])).
% 1.38/0.55  fof(f14,plain,(
% 1.38/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.38/0.55    inference(ennf_transformation,[],[f2])).
% 1.38/0.55  fof(f2,axiom,(
% 1.38/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.38/0.55  fof(f427,plain,(
% 1.38/0.55    ~l1_struct_0(k1_tsep_1(sK0,sK1,sK2)) | spl4_50),
% 1.38/0.55    inference(avatar_component_clause,[],[f426])).
% 1.38/0.55  fof(f428,plain,(
% 1.38/0.55    ~spl4_39 | ~spl4_50 | spl4_4 | ~spl4_33),
% 1.38/0.55    inference(avatar_split_clause,[],[f420,f307,f98,f426,f339])).
% 1.38/0.55  fof(f339,plain,(
% 1.38/0.55    spl4_39 <=> l1_struct_0(sK3)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.38/0.55  fof(f98,plain,(
% 1.38/0.55    spl4_4 <=> r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.38/0.55  fof(f420,plain,(
% 1.38/0.55    r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | ~l1_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~l1_struct_0(sK3) | ~spl4_33),
% 1.38/0.55    inference(resolution,[],[f308,f75])).
% 1.38/0.55  fof(f75,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f28])).
% 1.38/0.55  fof(f28,plain,(
% 1.38/0.55    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.38/0.55    inference(nnf_transformation,[],[f13])).
% 1.38/0.55  fof(f13,plain,(
% 1.38/0.55    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.38/0.55    inference(ennf_transformation,[],[f5])).
% 1.38/0.55  fof(f5,axiom,(
% 1.38/0.55    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 1.38/0.55  fof(f308,plain,(
% 1.38/0.55    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~spl4_33),
% 1.38/0.55    inference(avatar_component_clause,[],[f307])).
% 1.38/0.55  fof(f388,plain,(
% 1.38/0.55    ~spl4_16 | ~spl4_15 | ~spl4_1 | spl4_3),
% 1.38/0.55    inference(avatar_split_clause,[],[f263,f95,f89,f160,f163])).
% 1.38/0.55  fof(f163,plain,(
% 1.38/0.55    spl4_16 <=> l1_pre_topc(sK2)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.38/0.55  fof(f160,plain,(
% 1.38/0.55    spl4_15 <=> l1_pre_topc(sK3)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.38/0.55  fof(f89,plain,(
% 1.38/0.55    spl4_1 <=> r1_tsep_1(sK2,sK3)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.38/0.55  fof(f95,plain,(
% 1.38/0.55    spl4_3 <=> r1_tsep_1(sK3,sK2)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.38/0.55  fof(f263,plain,(
% 1.38/0.55    ~r1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK3) | ~l1_pre_topc(sK2) | spl4_3),
% 1.38/0.55    inference(resolution,[],[f117,f157])).
% 1.38/0.55  fof(f157,plain,(
% 1.38/0.55    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~r1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 1.38/0.55    inference(resolution,[],[f156,f76])).
% 1.38/0.55  fof(f156,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~l1_struct_0(X0) | r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_pre_topc(X1)) )),
% 1.38/0.55    inference(resolution,[],[f80,f76])).
% 1.38/0.55  fof(f80,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f19])).
% 1.38/0.55  fof(f19,plain,(
% 1.38/0.55    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.38/0.55    inference(flattening,[],[f18])).
% 1.38/0.55  fof(f18,plain,(
% 1.38/0.55    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 1.38/0.55    inference(ennf_transformation,[],[f7])).
% 1.38/0.55  fof(f7,axiom,(
% 1.38/0.55    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 1.38/0.55  fof(f117,plain,(
% 1.38/0.55    ~r1_tsep_1(sK3,sK2) | spl4_3),
% 1.38/0.55    inference(avatar_component_clause,[],[f95])).
% 1.38/0.55  fof(f387,plain,(
% 1.38/0.55    ~spl4_29 | ~spl4_15 | ~spl4_2 | spl4_4),
% 1.38/0.55    inference(avatar_split_clause,[],[f386,f98,f92,f160,f278])).
% 1.38/0.55  fof(f92,plain,(
% 1.38/0.55    spl4_2 <=> r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.38/0.55  fof(f386,plain,(
% 1.38/0.55    ~r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) | ~l1_pre_topc(sK3) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | spl4_4),
% 1.38/0.55    inference(resolution,[],[f115,f157])).
% 1.38/0.55  fof(f115,plain,(
% 1.38/0.55    ~r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | spl4_4),
% 1.38/0.55    inference(avatar_component_clause,[],[f98])).
% 1.38/0.55  fof(f385,plain,(
% 1.38/0.55    ~spl4_13 | ~spl4_9 | spl4_16),
% 1.38/0.55    inference(avatar_split_clause,[],[f384,f163,f130,f146])).
% 1.38/0.55  fof(f146,plain,(
% 1.38/0.55    spl4_13 <=> l1_pre_topc(sK0)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.38/0.55  fof(f384,plain,(
% 1.38/0.55    ~l1_pre_topc(sK0) | (~spl4_9 | spl4_16)),
% 1.38/0.55    inference(resolution,[],[f383,f131])).
% 1.38/0.55  fof(f131,plain,(
% 1.38/0.55    m1_pre_topc(sK2,sK0) | ~spl4_9),
% 1.38/0.55    inference(avatar_component_clause,[],[f130])).
% 1.38/0.55  fof(f383,plain,(
% 1.38/0.55    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | spl4_16),
% 1.38/0.55    inference(resolution,[],[f164,f77])).
% 1.38/0.55  fof(f77,plain,(
% 1.38/0.55    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f15])).
% 1.38/0.55  fof(f15,plain,(
% 1.38/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.38/0.55    inference(ennf_transformation,[],[f3])).
% 1.38/0.55  fof(f3,axiom,(
% 1.38/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.38/0.55  fof(f164,plain,(
% 1.38/0.55    ~l1_pre_topc(sK2) | spl4_16),
% 1.38/0.55    inference(avatar_component_clause,[],[f163])).
% 1.38/0.55  fof(f382,plain,(
% 1.38/0.55    ~spl4_16 | spl4_44),
% 1.38/0.55    inference(avatar_split_clause,[],[f381,f374,f163])).
% 1.38/0.55  fof(f374,plain,(
% 1.38/0.55    spl4_44 <=> l1_struct_0(sK2)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.38/0.55  fof(f381,plain,(
% 1.38/0.55    ~l1_pre_topc(sK2) | spl4_44),
% 1.38/0.55    inference(resolution,[],[f375,f76])).
% 1.38/0.55  fof(f375,plain,(
% 1.38/0.55    ~l1_struct_0(sK2) | spl4_44),
% 1.38/0.55    inference(avatar_component_clause,[],[f374])).
% 1.38/0.55  fof(f376,plain,(
% 1.38/0.55    ~spl4_39 | ~spl4_44 | spl4_3 | ~spl4_38),
% 1.38/0.55    inference(avatar_split_clause,[],[f370,f332,f95,f374,f339])).
% 1.38/0.55  fof(f370,plain,(
% 1.38/0.55    r1_tsep_1(sK3,sK2) | ~l1_struct_0(sK2) | ~l1_struct_0(sK3) | ~spl4_38),
% 1.38/0.55    inference(resolution,[],[f333,f75])).
% 1.38/0.55  fof(f358,plain,(
% 1.38/0.55    ~spl4_15 | ~spl4_27 | ~spl4_6 | spl4_5),
% 1.38/0.55    inference(avatar_split_clause,[],[f270,f102,f110,f267,f160])).
% 1.38/0.55  fof(f267,plain,(
% 1.38/0.55    spl4_27 <=> l1_pre_topc(sK1)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.38/0.55  fof(f102,plain,(
% 1.38/0.55    spl4_5 <=> r1_tsep_1(sK1,sK3)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.38/0.55  fof(f270,plain,(
% 1.38/0.55    ~r1_tsep_1(sK3,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK3) | spl4_5),
% 1.38/0.55    inference(resolution,[],[f106,f157])).
% 1.38/0.55  fof(f106,plain,(
% 1.38/0.55    ~r1_tsep_1(sK1,sK3) | spl4_5),
% 1.38/0.55    inference(avatar_component_clause,[],[f102])).
% 1.38/0.55  fof(f357,plain,(
% 1.38/0.55    ~spl4_13 | ~spl4_11 | spl4_27),
% 1.38/0.55    inference(avatar_split_clause,[],[f356,f267,f138,f146])).
% 1.38/0.55  fof(f356,plain,(
% 1.38/0.55    ~l1_pre_topc(sK0) | (~spl4_11 | spl4_27)),
% 1.38/0.55    inference(resolution,[],[f355,f139])).
% 1.38/0.55  fof(f355,plain,(
% 1.38/0.55    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | spl4_27),
% 1.38/0.55    inference(resolution,[],[f268,f77])).
% 1.38/0.55  fof(f268,plain,(
% 1.38/0.55    ~l1_pre_topc(sK1) | spl4_27),
% 1.38/0.55    inference(avatar_component_clause,[],[f267])).
% 1.38/0.55  fof(f354,plain,(
% 1.38/0.55    ~spl4_27 | spl4_40),
% 1.38/0.55    inference(avatar_split_clause,[],[f353,f342,f267])).
% 1.38/0.55  fof(f342,plain,(
% 1.38/0.55    spl4_40 <=> l1_struct_0(sK1)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.38/0.55  fof(f353,plain,(
% 1.38/0.55    ~l1_pre_topc(sK1) | spl4_40),
% 1.38/0.55    inference(resolution,[],[f343,f76])).
% 1.38/0.55  fof(f343,plain,(
% 1.38/0.55    ~l1_struct_0(sK1) | spl4_40),
% 1.38/0.55    inference(avatar_component_clause,[],[f342])).
% 1.38/0.55  fof(f350,plain,(
% 1.38/0.55    ~spl4_15 | spl4_39),
% 1.38/0.55    inference(avatar_split_clause,[],[f349,f339,f160])).
% 1.38/0.55  fof(f349,plain,(
% 1.38/0.55    ~l1_pre_topc(sK3) | spl4_39),
% 1.38/0.55    inference(resolution,[],[f340,f76])).
% 1.38/0.55  fof(f340,plain,(
% 1.38/0.55    ~l1_struct_0(sK3) | spl4_39),
% 1.38/0.55    inference(avatar_component_clause,[],[f339])).
% 1.38/0.55  fof(f344,plain,(
% 1.38/0.55    ~spl4_39 | ~spl4_40 | spl4_6 | ~spl4_37),
% 1.38/0.55    inference(avatar_split_clause,[],[f335,f328,f110,f342,f339])).
% 1.38/0.55  fof(f335,plain,(
% 1.38/0.55    r1_tsep_1(sK3,sK1) | ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | ~spl4_37),
% 1.38/0.55    inference(resolution,[],[f329,f75])).
% 1.38/0.55  fof(f334,plain,(
% 1.38/0.55    spl4_10 | spl4_12 | ~spl4_11 | ~spl4_9 | spl4_38 | ~spl4_18 | ~spl4_33),
% 1.38/0.55    inference(avatar_split_clause,[],[f321,f307,f195,f332,f130,f138,f142,f134])).
% 1.38/0.55  fof(f321,plain,(
% 1.38/0.55    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | v2_struct_0(sK2) | (~spl4_18 | ~spl4_33)),
% 1.38/0.55    inference(resolution,[],[f308,f209])).
% 1.38/0.55  fof(f209,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X2,u1_struct_0(k1_tsep_1(sK0,X0,X1))) | r1_xboole_0(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(X1)) ) | ~spl4_18),
% 1.38/0.55    inference(superposition,[],[f83,f196])).
% 1.38/0.55  fof(f330,plain,(
% 1.38/0.55    spl4_10 | spl4_12 | ~spl4_11 | ~spl4_9 | spl4_37 | ~spl4_18 | ~spl4_33),
% 1.38/0.55    inference(avatar_split_clause,[],[f320,f307,f195,f328,f130,f138,f142,f134])).
% 1.38/0.55  fof(f320,plain,(
% 1.38/0.55    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | v2_struct_0(sK2) | (~spl4_18 | ~spl4_33)),
% 1.38/0.55    inference(resolution,[],[f308,f210])).
% 1.38/0.55  fof(f210,plain,(
% 1.38/0.55    ( ! [X4,X5,X3] : (~r1_xboole_0(X5,u1_struct_0(k1_tsep_1(sK0,X3,X4))) | r1_xboole_0(X5,u1_struct_0(X3)) | ~m1_pre_topc(X4,sK0) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | v2_struct_0(X4)) ) | ~spl4_18),
% 1.38/0.55    inference(superposition,[],[f82,f196])).
% 1.38/0.55  fof(f310,plain,(
% 1.38/0.55    spl4_33 | ~spl4_30),
% 1.38/0.55    inference(avatar_split_clause,[],[f298,f289,f307])).
% 1.38/0.55  fof(f289,plain,(
% 1.38/0.55    spl4_30 <=> r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.38/0.55  fof(f298,plain,(
% 1.38/0.55    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~spl4_30),
% 1.38/0.55    inference(resolution,[],[f290,f82])).
% 1.38/0.55  fof(f290,plain,(
% 1.38/0.55    r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) | ~spl4_30),
% 1.38/0.55    inference(avatar_component_clause,[],[f289])).
% 1.38/0.55  fof(f291,plain,(
% 1.38/0.55    ~spl4_24 | spl4_30 | ~spl4_4 | ~spl4_28),
% 1.38/0.55    inference(avatar_split_clause,[],[f286,f273,f98,f289,f241])).
% 1.38/0.55  fof(f241,plain,(
% 1.38/0.55    spl4_24 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.38/0.55  fof(f273,plain,(
% 1.38/0.55    spl4_28 <=> ! [X0] : (~r1_tsep_1(sK3,X0) | r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.38/0.55  fof(f286,plain,(
% 1.38/0.55    r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | (~spl4_4 | ~spl4_28)),
% 1.38/0.55    inference(resolution,[],[f274,f99])).
% 1.38/0.55  fof(f99,plain,(
% 1.38/0.55    r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | ~spl4_4),
% 1.38/0.55    inference(avatar_component_clause,[],[f98])).
% 1.38/0.55  fof(f274,plain,(
% 1.38/0.55    ( ! [X0] : (~r1_tsep_1(sK3,X0) | r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0)) ) | ~spl4_28),
% 1.38/0.55    inference(avatar_component_clause,[],[f273])).
% 1.38/0.55  fof(f284,plain,(
% 1.38/0.55    spl4_14 | spl4_12 | ~spl4_11 | spl4_10 | ~spl4_9 | ~spl4_13 | spl4_29),
% 1.38/0.55    inference(avatar_split_clause,[],[f283,f278,f146,f130,f134,f138,f142,f150])).
% 1.38/0.55  fof(f150,plain,(
% 1.38/0.55    spl4_14 <=> v2_struct_0(sK0)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.38/0.55  fof(f283,plain,(
% 1.38/0.55    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | spl4_29),
% 1.38/0.55    inference(duplicate_literal_removal,[],[f282])).
% 1.38/0.55  fof(f282,plain,(
% 1.38/0.55    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_29),
% 1.38/0.55    inference(resolution,[],[f281,f86])).
% 1.38/0.55  fof(f86,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f22])).
% 1.38/0.55  fof(f22,plain,(
% 1.38/0.55    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.38/0.55    inference(flattening,[],[f21])).
% 1.38/0.55  fof(f21,plain,(
% 1.38/0.55    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.38/0.55    inference(ennf_transformation,[],[f6])).
% 1.38/0.55  fof(f6,axiom,(
% 1.38/0.55    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 1.38/0.55  fof(f281,plain,(
% 1.38/0.55    ( ! [X0] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0) | ~l1_pre_topc(X0)) ) | spl4_29),
% 1.38/0.55    inference(resolution,[],[f279,f77])).
% 1.38/0.55  fof(f279,plain,(
% 1.38/0.55    ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | spl4_29),
% 1.38/0.55    inference(avatar_component_clause,[],[f278])).
% 1.38/0.55  fof(f280,plain,(
% 1.38/0.55    ~spl4_15 | ~spl4_29 | ~spl4_4 | spl4_2),
% 1.38/0.55    inference(avatar_split_clause,[],[f276,f92,f98,f278,f160])).
% 1.38/0.55  fof(f276,plain,(
% 1.38/0.55    ~r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(sK3) | spl4_2),
% 1.38/0.55    inference(resolution,[],[f105,f157])).
% 1.38/0.55  fof(f105,plain,(
% 1.38/0.55    ~r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) | spl4_2),
% 1.38/0.55    inference(avatar_component_clause,[],[f92])).
% 1.38/0.55  fof(f275,plain,(
% 1.38/0.55    spl4_28 | ~spl4_7 | ~spl4_24 | ~spl4_4 | ~spl4_13),
% 1.38/0.55    inference(avatar_split_clause,[],[f271,f146,f98,f241,f122,f273])).
% 1.38/0.55  fof(f122,plain,(
% 1.38/0.55    spl4_7 <=> m1_pre_topc(sK3,sK0)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.38/0.55  fof(f271,plain,(
% 1.38/0.55    ( ! [X0] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | ~m1_pre_topc(sK3,sK0) | ~r1_tsep_1(sK3,X0) | ~m1_pre_topc(X0,sK0) | r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)))) ) | (~spl4_4 | ~spl4_13)),
% 1.38/0.55    inference(resolution,[],[f99,f233])).
% 1.38/0.55  fof(f233,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~r1_tsep_1(X1,X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,sK0) | r1_xboole_0(u1_struct_0(X1),k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)))) ) | ~spl4_13),
% 1.38/0.55    inference(resolution,[],[f231,f147])).
% 1.38/0.55  fof(f147,plain,(
% 1.38/0.55    l1_pre_topc(sK0) | ~spl4_13),
% 1.38/0.55    inference(avatar_component_clause,[],[f146])).
% 1.38/0.55  fof(f231,plain,(
% 1.38/0.55    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X3) | ~m1_pre_topc(X2,sK0) | ~r1_tsep_1(X0,X2) | ~m1_pre_topc(X0,X3) | ~r1_tsep_1(X0,X1) | ~m1_pre_topc(X1,sK0) | r1_xboole_0(u1_struct_0(X0),k2_xboole_0(u1_struct_0(X2),u1_struct_0(X1)))) ) | ~spl4_13),
% 1.38/0.55    inference(resolution,[],[f222,f147])).
% 1.38/0.55  fof(f222,plain,(
% 1.38/0.55    ( ! [X6,X4,X7,X5,X3] : (~l1_pre_topc(X7) | ~r1_tsep_1(X3,X5) | ~m1_pre_topc(X4,sK0) | ~r1_tsep_1(X3,X4) | ~m1_pre_topc(X3,X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(X5,X7) | r1_xboole_0(u1_struct_0(X3),k2_xboole_0(u1_struct_0(X4),u1_struct_0(X5)))) ) | ~spl4_13),
% 1.38/0.55    inference(resolution,[],[f190,f77])).
% 1.38/0.55  fof(f190,plain,(
% 1.38/0.55    ( ! [X4,X2,X5,X3] : (~l1_pre_topc(X3) | r1_xboole_0(u1_struct_0(X2),k2_xboole_0(u1_struct_0(X4),u1_struct_0(X3))) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X4,sK0) | ~r1_tsep_1(X2,X4) | ~m1_pre_topc(X2,X5) | ~l1_pre_topc(X5)) ) | ~spl4_13),
% 1.38/0.55    inference(resolution,[],[f187,f77])).
% 1.38/0.55  fof(f187,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tsep_1(X0,X2) | r1_xboole_0(u1_struct_0(X0),k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_pre_topc(X1,sK0) | ~r1_tsep_1(X0,X1)) ) | ~spl4_13),
% 1.38/0.55    inference(resolution,[],[f177,f147])).
% 1.38/0.55  fof(f177,plain,(
% 1.38/0.55    ( ! [X4,X2,X5,X3] : (~l1_pre_topc(X5) | ~r1_tsep_1(X2,X3) | ~r1_tsep_1(X2,X4) | r1_xboole_0(u1_struct_0(X2),k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))) | ~l1_pre_topc(X4) | ~m1_pre_topc(X3,X5) | ~l1_pre_topc(X2)) )),
% 1.38/0.55    inference(resolution,[],[f175,f77])).
% 1.38/0.55  fof(f175,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~l1_pre_topc(X2) | ~l1_pre_topc(X1) | ~r1_tsep_1(X1,X2) | ~r1_tsep_1(X1,X0) | r1_xboole_0(u1_struct_0(X1),k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.38/0.55    inference(duplicate_literal_removal,[],[f174])).
% 1.38/0.55  fof(f174,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~r1_tsep_1(X1,X2) | ~r1_tsep_1(X1,X0) | r1_xboole_0(u1_struct_0(X1),k2_xboole_0(u1_struct_0(X2),u1_struct_0(X0))) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1)) )),
% 1.38/0.55    inference(resolution,[],[f173,f76])).
% 1.38/0.55  fof(f173,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~l1_pre_topc(X2) | ~l1_pre_topc(X0) | ~r1_tsep_1(X0,X1) | ~r1_tsep_1(X0,X2) | r1_xboole_0(u1_struct_0(X0),k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~l1_pre_topc(X1)) )),
% 1.38/0.55    inference(resolution,[],[f172,f76])).
% 1.38/0.55  fof(f172,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~l1_struct_0(X2) | r1_xboole_0(u1_struct_0(X0),k2_xboole_0(u1_struct_0(X2),u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~r1_tsep_1(X0,X2) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X0)) )),
% 1.38/0.55    inference(resolution,[],[f171,f74])).
% 1.38/0.55  fof(f74,plain,(
% 1.38/0.55    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f28])).
% 1.38/0.55  fof(f171,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(u1_struct_0(X0),X2) | ~r1_tsep_1(X0,X1) | r1_xboole_0(u1_struct_0(X0),k2_xboole_0(X2,u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.38/0.55    inference(resolution,[],[f170,f76])).
% 1.38/0.55  fof(f170,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),X2) | r1_xboole_0(u1_struct_0(X0),k2_xboole_0(X2,u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 1.38/0.55    inference(resolution,[],[f167,f76])).
% 1.38/0.55  fof(f167,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X0) | ~r1_xboole_0(u1_struct_0(X0),X2) | r1_xboole_0(u1_struct_0(X0),k2_xboole_0(X2,u1_struct_0(X1)))) )),
% 1.38/0.55    inference(resolution,[],[f74,f81])).
% 1.38/0.55  fof(f269,plain,(
% 1.38/0.55    ~spl4_27 | ~spl4_15 | ~spl4_5 | spl4_6),
% 1.38/0.55    inference(avatar_split_clause,[],[f262,f110,f102,f160,f267])).
% 1.38/0.55  fof(f262,plain,(
% 1.38/0.55    ~r1_tsep_1(sK1,sK3) | ~l1_pre_topc(sK3) | ~l1_pre_topc(sK1) | spl4_6),
% 1.38/0.55    inference(resolution,[],[f116,f157])).
% 1.38/0.55  fof(f116,plain,(
% 1.38/0.55    ~r1_tsep_1(sK3,sK1) | spl4_6),
% 1.38/0.55    inference(avatar_component_clause,[],[f110])).
% 1.38/0.55  fof(f265,plain,(
% 1.38/0.55    ~spl4_13 | ~spl4_7 | spl4_15),
% 1.38/0.55    inference(avatar_split_clause,[],[f264,f160,f122,f146])).
% 1.38/0.55  fof(f264,plain,(
% 1.38/0.55    ~l1_pre_topc(sK0) | (~spl4_7 | spl4_15)),
% 1.38/0.55    inference(resolution,[],[f251,f123])).
% 1.38/0.55  fof(f123,plain,(
% 1.38/0.55    m1_pre_topc(sK3,sK0) | ~spl4_7),
% 1.38/0.55    inference(avatar_component_clause,[],[f122])).
% 1.38/0.55  fof(f251,plain,(
% 1.38/0.55    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl4_15),
% 1.38/0.55    inference(resolution,[],[f161,f77])).
% 1.38/0.55  fof(f161,plain,(
% 1.38/0.55    ~l1_pre_topc(sK3) | spl4_15),
% 1.38/0.55    inference(avatar_component_clause,[],[f160])).
% 1.38/0.55  fof(f256,plain,(
% 1.38/0.55    spl4_25 | ~spl4_7 | ~spl4_9 | ~spl4_3 | ~spl4_13),
% 1.38/0.55    inference(avatar_split_clause,[],[f252,f146,f95,f130,f122,f254])).
% 1.38/0.55  fof(f252,plain,(
% 1.38/0.55    ( ! [X0] : (~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK3,sK0) | ~r1_tsep_1(sK3,X0) | ~m1_pre_topc(X0,sK0) | r1_xboole_0(u1_struct_0(sK3),k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0)))) ) | (~spl4_3 | ~spl4_13)),
% 1.38/0.55    inference(resolution,[],[f96,f233])).
% 1.38/0.55  fof(f96,plain,(
% 1.38/0.55    r1_tsep_1(sK3,sK2) | ~spl4_3),
% 1.38/0.55    inference(avatar_component_clause,[],[f95])).
% 1.38/0.55  fof(f250,plain,(
% 1.38/0.55    spl4_14 | ~spl4_13 | spl4_12 | ~spl4_11 | spl4_10 | ~spl4_9 | spl4_24),
% 1.38/0.55    inference(avatar_split_clause,[],[f245,f241,f130,f134,f138,f142,f146,f150])).
% 1.38/0.55  fof(f245,plain,(
% 1.38/0.55    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_24),
% 1.38/0.55    inference(resolution,[],[f242,f86])).
% 1.38/0.55  fof(f242,plain,(
% 1.38/0.55    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | spl4_24),
% 1.38/0.55    inference(avatar_component_clause,[],[f241])).
% 1.38/0.55  fof(f197,plain,(
% 1.38/0.55    spl4_14 | spl4_18 | ~spl4_13),
% 1.38/0.55    inference(avatar_split_clause,[],[f191,f146,f195,f150])).
% 1.38/0.55  fof(f191,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0)) | v2_struct_0(sK0)) ) | ~spl4_13),
% 1.38/0.55    inference(resolution,[],[f155,f147])).
% 1.38/0.55  fof(f155,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | v2_struct_0(X0)) )),
% 1.38/0.55    inference(subsumption_resolution,[],[f154,f84])).
% 1.38/0.55  fof(f84,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f22])).
% 1.38/0.55  fof(f154,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.55    inference(subsumption_resolution,[],[f153,f85])).
% 1.38/0.55  fof(f85,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f22])).
% 1.38/0.55  fof(f153,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.55    inference(subsumption_resolution,[],[f87,f86])).
% 1.38/0.55  fof(f87,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.55    inference(equality_resolution,[],[f78])).
% 1.38/0.55  fof(f78,plain,(
% 1.38/0.55    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f29])).
% 1.38/0.55  fof(f29,plain,(
% 1.38/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.38/0.55    inference(nnf_transformation,[],[f17])).
% 1.38/0.55  fof(f17,plain,(
% 1.38/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.38/0.55    inference(flattening,[],[f16])).
% 1.38/0.55  fof(f16,plain,(
% 1.38/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.38/0.55    inference(ennf_transformation,[],[f4])).
% 1.38/0.55  fof(f4,axiom,(
% 1.38/0.55    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).
% 1.38/0.55  fof(f165,plain,(
% 1.38/0.55    ~spl4_15 | ~spl4_16 | ~spl4_3 | spl4_1),
% 1.38/0.55    inference(avatar_split_clause,[],[f158,f89,f95,f163,f160])).
% 1.38/0.55  fof(f158,plain,(
% 1.38/0.55    ~r1_tsep_1(sK3,sK2) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK3) | spl4_1),
% 1.38/0.55    inference(resolution,[],[f157,f107])).
% 1.38/0.55  fof(f107,plain,(
% 1.38/0.55    ~r1_tsep_1(sK2,sK3) | spl4_1),
% 1.38/0.55    inference(avatar_component_clause,[],[f89])).
% 1.38/0.55  fof(f152,plain,(
% 1.38/0.55    ~spl4_14),
% 1.38/0.55    inference(avatar_split_clause,[],[f30,f150])).
% 1.38/0.55  fof(f30,plain,(
% 1.38/0.55    ~v2_struct_0(sK0)),
% 1.38/0.55    inference(cnf_transformation,[],[f27])).
% 1.38/0.55  fof(f27,plain,(
% 1.38/0.55    (((((r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) & (~r1_tsep_1(sK3,sK2) | ~r1_tsep_1(sK3,sK1))) | (r1_tsep_1(sK3,sK2) & r1_tsep_1(sK3,sK1) & ~r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))) | (r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) & (~r1_tsep_1(sK2,sK3) | ~r1_tsep_1(sK1,sK3))) | (r1_tsep_1(sK2,sK3) & r1_tsep_1(sK1,sK3) & ~r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3))) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.38/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f26,f25,f24,f23])).
% 1.38/0.55  fof(f23,plain,(
% 1.38/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1))) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3))) | (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(sK0,X1,X2)) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1))) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(sK0,X1,X2))) | (r1_tsep_1(k1_tsep_1(sK0,X1,X2),X3) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3))) | (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(sK0,X1,X2),X3))) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f24,plain,(
% 1.38/0.55    ? [X1] : (? [X2] : (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(sK0,X1,X2)) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1))) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(sK0,X1,X2))) | (r1_tsep_1(k1_tsep_1(sK0,X1,X2),X3) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3))) | (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(sK0,X1,X2),X3))) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(sK0,sK1,X2)) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,sK1))) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,sK1) & ~r1_tsep_1(X3,k1_tsep_1(sK0,sK1,X2))) | (r1_tsep_1(k1_tsep_1(sK0,sK1,X2),X3) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(sK1,X3))) | (r1_tsep_1(X2,X3) & r1_tsep_1(sK1,X3) & ~r1_tsep_1(k1_tsep_1(sK0,sK1,X2),X3))) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f25,plain,(
% 1.38/0.55    ? [X2] : (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(sK0,sK1,X2)) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,sK1))) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,sK1) & ~r1_tsep_1(X3,k1_tsep_1(sK0,sK1,X2))) | (r1_tsep_1(k1_tsep_1(sK0,sK1,X2),X3) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(sK1,X3))) | (r1_tsep_1(X2,X3) & r1_tsep_1(sK1,X3) & ~r1_tsep_1(k1_tsep_1(sK0,sK1,X2),X3))) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK2)) & (~r1_tsep_1(X3,sK2) | ~r1_tsep_1(X3,sK1))) | (r1_tsep_1(X3,sK2) & r1_tsep_1(X3,sK1) & ~r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK2))) | (r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),X3) & (~r1_tsep_1(sK2,X3) | ~r1_tsep_1(sK1,X3))) | (r1_tsep_1(sK2,X3) & r1_tsep_1(sK1,X3) & ~r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),X3))) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.62/0.56  fof(f26,plain,(
% 1.62/0.56    ? [X3] : (((r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK2)) & (~r1_tsep_1(X3,sK2) | ~r1_tsep_1(X3,sK1))) | (r1_tsep_1(X3,sK2) & r1_tsep_1(X3,sK1) & ~r1_tsep_1(X3,k1_tsep_1(sK0,sK1,sK2))) | (r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),X3) & (~r1_tsep_1(sK2,X3) | ~r1_tsep_1(sK1,X3))) | (r1_tsep_1(sK2,X3) & r1_tsep_1(sK1,X3) & ~r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),X3))) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (((r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) & (~r1_tsep_1(sK3,sK2) | ~r1_tsep_1(sK3,sK1))) | (r1_tsep_1(sK3,sK2) & r1_tsep_1(sK3,sK1) & ~r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))) | (r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) & (~r1_tsep_1(sK2,sK3) | ~r1_tsep_1(sK1,sK3))) | (r1_tsep_1(sK2,sK3) & r1_tsep_1(sK1,sK3) & ~r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3))) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.62/0.56    introduced(choice_axiom,[])).
% 1.62/0.56  fof(f12,plain,(
% 1.62/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1))) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3))) | (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.62/0.56    inference(flattening,[],[f11])).
% 1.62/0.56  fof(f11,plain,(
% 1.62/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1))) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3))) | (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.62/0.56    inference(ennf_transformation,[],[f10])).
% 1.62/0.56  fof(f10,plain,(
% 1.62/0.56    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~(r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & ~(r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)))))))),
% 1.62/0.56    inference(pure_predicate_removal,[],[f9])).
% 1.62/0.56  fof(f9,negated_conjecture,(
% 1.62/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~(r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & ~(r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)))))))),
% 1.62/0.56    inference(negated_conjecture,[],[f8])).
% 1.62/0.56  fof(f8,conjecture,(
% 1.62/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~(r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & ~(r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)))))))),
% 1.62/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tmap_1)).
% 1.62/0.56  fof(f148,plain,(
% 1.62/0.56    spl4_13),
% 1.62/0.56    inference(avatar_split_clause,[],[f31,f146])).
% 1.62/0.56  fof(f31,plain,(
% 1.62/0.56    l1_pre_topc(sK0)),
% 1.62/0.56    inference(cnf_transformation,[],[f27])).
% 1.62/0.56  fof(f144,plain,(
% 1.62/0.56    ~spl4_12),
% 1.62/0.56    inference(avatar_split_clause,[],[f32,f142])).
% 1.62/0.56  fof(f32,plain,(
% 1.62/0.56    ~v2_struct_0(sK1)),
% 1.62/0.56    inference(cnf_transformation,[],[f27])).
% 1.62/0.56  fof(f140,plain,(
% 1.62/0.56    spl4_11),
% 1.62/0.56    inference(avatar_split_clause,[],[f33,f138])).
% 1.62/0.56  fof(f33,plain,(
% 1.62/0.56    m1_pre_topc(sK1,sK0)),
% 1.62/0.56    inference(cnf_transformation,[],[f27])).
% 1.62/0.56  fof(f136,plain,(
% 1.62/0.56    ~spl4_10),
% 1.62/0.56    inference(avatar_split_clause,[],[f34,f134])).
% 1.62/0.56  fof(f34,plain,(
% 1.62/0.56    ~v2_struct_0(sK2)),
% 1.62/0.56    inference(cnf_transformation,[],[f27])).
% 1.62/0.56  fof(f132,plain,(
% 1.62/0.56    spl4_9),
% 1.62/0.56    inference(avatar_split_clause,[],[f35,f130])).
% 1.62/0.56  fof(f35,plain,(
% 1.62/0.56    m1_pre_topc(sK2,sK0)),
% 1.62/0.56    inference(cnf_transformation,[],[f27])).
% 1.62/0.56  fof(f124,plain,(
% 1.62/0.56    spl4_7),
% 1.62/0.56    inference(avatar_split_clause,[],[f37,f122])).
% 1.62/0.56  fof(f37,plain,(
% 1.62/0.56    m1_pre_topc(sK3,sK0)),
% 1.62/0.56    inference(cnf_transformation,[],[f27])).
% 1.62/0.56  fof(f120,plain,(
% 1.62/0.56    ~spl4_2 | ~spl4_5 | ~spl4_1 | ~spl4_4 | ~spl4_6 | ~spl4_3),
% 1.62/0.56    inference(avatar_split_clause,[],[f38,f95,f110,f98,f89,f102,f92])).
% 1.62/0.56  fof(f38,plain,(
% 1.62/0.56    ~r1_tsep_1(sK3,sK2) | ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | ~r1_tsep_1(sK2,sK3) | ~r1_tsep_1(sK1,sK3) | ~r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)),
% 1.62/0.56    inference(cnf_transformation,[],[f27])).
% 1.62/0.56  fof(f113,plain,(
% 1.62/0.56    spl4_5 | spl4_2 | spl4_6 | spl4_4),
% 1.62/0.56    inference(avatar_split_clause,[],[f66,f98,f110,f92,f102])).
% 1.62/0.56  fof(f66,plain,(
% 1.62/0.56    r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | r1_tsep_1(sK3,sK1) | r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) | r1_tsep_1(sK1,sK3)),
% 1.62/0.56    inference(cnf_transformation,[],[f27])).
% 1.62/0.56  fof(f100,plain,(
% 1.62/0.56    spl4_1 | spl4_2 | spl4_3 | spl4_4),
% 1.62/0.56    inference(avatar_split_clause,[],[f73,f98,f95,f92,f89])).
% 1.62/0.56  fof(f73,plain,(
% 1.62/0.56    r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) | r1_tsep_1(sK3,sK2) | r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) | r1_tsep_1(sK2,sK3)),
% 1.62/0.56    inference(cnf_transformation,[],[f27])).
% 1.62/0.56  % SZS output end Proof for theBenchmark
% 1.62/0.56  % (5346)------------------------------
% 1.62/0.56  % (5346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.56  % (5346)Termination reason: Refutation
% 1.62/0.56  
% 1.62/0.56  % (5346)Memory used [KB]: 11257
% 1.62/0.56  % (5346)Time elapsed: 0.085 s
% 1.62/0.56  % (5346)------------------------------
% 1.62/0.56  % (5346)------------------------------
% 1.62/0.56  % (5339)Success in time 0.199 s
%------------------------------------------------------------------------------
