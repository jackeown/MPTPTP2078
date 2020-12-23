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
% DateTime   : Thu Dec  3 13:18:05 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 333 expanded)
%              Number of leaves         :   33 ( 163 expanded)
%              Depth                    :   12
%              Number of atoms          :  677 (2685 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f431,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f59,f63,f67,f71,f75,f79,f83,f87,f91,f95,f99,f103,f114,f123,f143,f186,f274,f321,f407,f417,f421,f430])).

fof(f430,plain,
    ( ~ spl4_24
    | ~ spl4_5
    | ~ spl4_47
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f428,f402,f405,f69,f177])).

fof(f177,plain,
    ( spl4_24
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f69,plain,
    ( spl4_5
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f405,plain,
    ( spl4_47
  <=> m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f402,plain,
    ( spl4_46
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0)
        | ~ m1_pre_topc(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f428,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK3)
    | ~ spl4_46 ),
    inference(resolution,[],[f403,f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f403,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f402])).

fof(f421,plain,
    ( ~ spl4_37
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_5
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f419,f399,f69,f97,f93,f270])).

fof(f270,plain,
    ( spl4_37
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f93,plain,
    ( spl4_11
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f97,plain,
    ( spl4_12
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f399,plain,
    ( spl4_45
  <=> ! [X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f419,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl4_5
    | ~ spl4_45 ),
    inference(resolution,[],[f400,f70])).

fof(f70,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f400,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X1) )
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f399])).

fof(f417,plain,
    ( spl4_6
    | ~ spl4_24
    | spl4_10
    | ~ spl4_4
    | spl4_8
    | ~ spl4_3
    | spl4_47 ),
    inference(avatar_split_clause,[],[f409,f405,f61,f81,f65,f89,f177,f73])).

fof(f73,plain,
    ( spl4_6
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f89,plain,
    ( spl4_10
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f65,plain,
    ( spl4_4
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f81,plain,
    ( spl4_8
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f61,plain,
    ( spl4_3
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f409,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl4_47 ),
    inference(resolution,[],[f406,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f406,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),sK3)
    | spl4_47 ),
    inference(avatar_component_clause,[],[f405])).

fof(f407,plain,
    ( spl4_45
    | spl4_46
    | ~ spl4_47
    | spl4_1
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f397,f319,f53,f405,f402,f399])).

fof(f53,plain,
    ( spl4_1
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f319,plain,
    ( spl4_39
  <=> ! [X1,X0] :
        ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0))
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X1)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f397,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),sK3)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | spl4_1
    | ~ spl4_39 ),
    inference(resolution,[],[f322,f54])).

fof(f54,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f322,plain,
    ( ! [X2,X0,X1] :
        ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X1)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2) )
    | ~ spl4_39 ),
    inference(resolution,[],[f320,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f320,plain,
    ( ! [X0,X1] :
        ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0))
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X1)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,X1) )
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f319])).

fof(f321,plain,
    ( ~ spl4_12
    | spl4_39
    | ~ spl4_11
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f317,f140,f93,f319,f97])).

fof(f140,plain,
    ( spl4_17
  <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f317,plain,
    ( ! [X0,X1] :
        ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X1)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_11
    | ~ spl4_17 ),
    inference(duplicate_literal_removal,[],[f315])).

fof(f315,plain,
    ( ! [X0,X1] :
        ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X1)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_11
    | ~ spl4_17 ),
    inference(resolution,[],[f294,f94])).

fof(f94,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f294,plain,
    ( ! [X2,X3,X1] :
        ( ~ l1_pre_topc(X3)
        | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X2))
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X2)
        | ~ m1_pre_topc(X1,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X1)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_11
    | ~ spl4_17 ),
    inference(resolution,[],[f291,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f291,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X1)
        | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0) )
    | ~ spl4_11
    | ~ spl4_17 ),
    inference(resolution,[],[f276,f94])).

fof(f276,plain,
    ( ! [X2,X3,X1] :
        ( ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X2)
        | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X1))
        | ~ v2_pre_topc(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X1) )
    | ~ spl4_17 ),
    inference(resolution,[],[f162,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f162,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(X13)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X12)
        | ~ m1_pre_topc(X12,X13)
        | ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X13)
        | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X12))
        | ~ v2_pre_topc(X13) )
    | ~ spl4_17 ),
    inference(superposition,[],[f47,f141])).

fof(f141,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f140])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f274,plain,
    ( spl4_13
    | ~ spl4_11
    | spl4_10
    | ~ spl4_9
    | spl4_8
    | ~ spl4_7
    | spl4_37 ),
    inference(avatar_split_clause,[],[f273,f270,f77,f81,f85,f89,f93,f101])).

fof(f101,plain,
    ( spl4_13
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f85,plain,
    ( spl4_9
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f77,plain,
    ( spl4_7
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f273,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_37 ),
    inference(resolution,[],[f271,f50])).

fof(f271,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_37 ),
    inference(avatar_component_clause,[],[f270])).

fof(f186,plain,
    ( ~ spl4_11
    | ~ spl4_5
    | spl4_24 ),
    inference(avatar_split_clause,[],[f182,f177,f69,f93])).

fof(f182,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_5
    | spl4_24 ),
    inference(resolution,[],[f181,f70])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl4_24 ),
    inference(resolution,[],[f178,f42])).

fof(f178,plain,
    ( ~ l1_pre_topc(sK3)
    | spl4_24 ),
    inference(avatar_component_clause,[],[f177])).

fof(f143,plain,
    ( spl4_6
    | ~ spl4_5
    | spl4_17
    | ~ spl4_4
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f134,f120,f112,f93,f61,f65,f140,f69,f73])).

fof(f112,plain,
    ( spl4_14
  <=> ! [X0] :
        ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f120,plain,
    ( spl4_15
  <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f134,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(resolution,[],[f132,f62])).

fof(f62,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f130,f121])).

fof(f121,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f120])).

fof(f130,plain,
    ( ! [X0] :
        ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2))
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(resolution,[],[f116,f94])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2))
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0) )
    | ~ spl4_14 ),
    inference(resolution,[],[f113,f42])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2))
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK2,X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f112])).

fof(f123,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | spl4_15
    | spl4_13
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f115,f112,f93,f101,f120,f85,f77])).

fof(f115,plain,
    ( v2_struct_0(sK0)
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(resolution,[],[f113,f94])).

fof(f114,plain,
    ( spl4_10
    | spl4_8
    | spl4_14
    | spl4_2 ),
    inference(avatar_split_clause,[],[f108,f57,f112,f81,f89])).

fof(f57,plain,
    ( spl4_2
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f108,plain,
    ( ! [X0] :
        ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2))
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl4_2 ),
    inference(resolution,[],[f106,f58])).

fof(f58,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f105,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f104,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f51,f50])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f103,plain,(
    ~ spl4_13 ),
    inference(avatar_split_clause,[],[f28,f101])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK1,sK3)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f24,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X1,X3)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3)
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(X1,X3)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3)
              & ~ r1_tsep_1(sK1,X2)
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(sK1,X3)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3)
            & ~ r1_tsep_1(sK1,X2)
            & m1_pre_topc(X2,X3)
            & m1_pre_topc(sK1,X3)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3)
          & ~ r1_tsep_1(sK1,sK2)
          & m1_pre_topc(sK2,X3)
          & m1_pre_topc(sK1,X3)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3)
        & ~ r1_tsep_1(sK1,sK2)
        & m1_pre_topc(sK2,X3)
        & m1_pre_topc(sK1,X3)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK2,sK3)
      & m1_pre_topc(sK1,sK3)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                        | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
                 => ( ( m1_pre_topc(X2,X3)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                      | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).

fof(f99,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f29,f97])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f95,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f30,f93])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,(
    ~ spl4_10 ),
    inference(avatar_split_clause,[],[f31,f89])).

fof(f31,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f32,f85])).

fof(f32,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f83,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f33,f81])).

fof(f33,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f34,f77])).

fof(f34,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f35,f73])).

fof(f35,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f36,f69])).

fof(f36,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f37,f65])).

fof(f37,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f38,f61])).

fof(f38,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f39,f57])).

fof(f39,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f40,f53])).

fof(f40,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:40:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.48  % (26882)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.48  % (26891)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.23/0.48  % (26896)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.23/0.48  % (26882)Refutation not found, incomplete strategy% (26882)------------------------------
% 0.23/0.48  % (26882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.48  % (26886)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.48  % (26895)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.23/0.49  % (26892)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.23/0.49  % (26882)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.49  
% 0.23/0.49  % (26882)Memory used [KB]: 10618
% 0.23/0.49  % (26882)Time elapsed: 0.052 s
% 0.23/0.49  % (26882)------------------------------
% 0.23/0.49  % (26882)------------------------------
% 0.23/0.49  % (26887)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.49  % (26891)Refutation not found, incomplete strategy% (26891)------------------------------
% 0.23/0.49  % (26891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (26891)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.49  
% 0.23/0.49  % (26891)Memory used [KB]: 6140
% 0.23/0.49  % (26891)Time elapsed: 0.064 s
% 0.23/0.49  % (26891)------------------------------
% 0.23/0.49  % (26891)------------------------------
% 0.23/0.50  % (26894)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.23/0.50  % (26887)Refutation found. Thanks to Tanya!
% 0.23/0.50  % SZS status Theorem for theBenchmark
% 0.23/0.50  % SZS output start Proof for theBenchmark
% 0.23/0.50  fof(f431,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(avatar_sat_refutation,[],[f55,f59,f63,f67,f71,f75,f79,f83,f87,f91,f95,f99,f103,f114,f123,f143,f186,f274,f321,f407,f417,f421,f430])).
% 0.23/0.50  fof(f430,plain,(
% 0.23/0.50    ~spl4_24 | ~spl4_5 | ~spl4_47 | ~spl4_46),
% 0.23/0.50    inference(avatar_split_clause,[],[f428,f402,f405,f69,f177])).
% 0.23/0.50  fof(f177,plain,(
% 0.23/0.50    spl4_24 <=> l1_pre_topc(sK3)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.23/0.50  fof(f69,plain,(
% 0.23/0.50    spl4_5 <=> m1_pre_topc(sK3,sK0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.23/0.50  fof(f405,plain,(
% 0.23/0.50    spl4_47 <=> m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),sK3)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.23/0.50  fof(f402,plain,(
% 0.23/0.50    spl4_46 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0) | ~m1_pre_topc(sK3,X0))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.23/0.50  fof(f428,plain,(
% 0.23/0.50    ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),sK3) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK3) | ~spl4_46),
% 0.23/0.50    inference(resolution,[],[f403,f41])).
% 0.23/0.50  fof(f41,plain,(
% 0.23/0.50    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f11])).
% 0.23/0.50  fof(f11,plain,(
% 0.23/0.50    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f5])).
% 0.23/0.50  fof(f5,axiom,(
% 0.23/0.50    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.23/0.50  fof(f403,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl4_46),
% 0.23/0.50    inference(avatar_component_clause,[],[f402])).
% 0.23/0.50  fof(f421,plain,(
% 0.23/0.50    ~spl4_37 | ~spl4_11 | ~spl4_12 | ~spl4_5 | ~spl4_45),
% 0.23/0.50    inference(avatar_split_clause,[],[f419,f399,f69,f97,f93,f270])).
% 0.23/0.50  fof(f270,plain,(
% 0.23/0.50    spl4_37 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.23/0.50  fof(f93,plain,(
% 0.23/0.50    spl4_11 <=> l1_pre_topc(sK0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.23/0.50  fof(f97,plain,(
% 0.23/0.50    spl4_12 <=> v2_pre_topc(sK0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.23/0.50  fof(f399,plain,(
% 0.23/0.50    spl4_45 <=> ! [X1] : (~m1_pre_topc(sK3,X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X1))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.23/0.50  fof(f419,plain,(
% 0.23/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | (~spl4_5 | ~spl4_45)),
% 0.23/0.50    inference(resolution,[],[f400,f70])).
% 0.23/0.50  fof(f70,plain,(
% 0.23/0.50    m1_pre_topc(sK3,sK0) | ~spl4_5),
% 0.23/0.50    inference(avatar_component_clause,[],[f69])).
% 0.23/0.50  fof(f400,plain,(
% 0.23/0.50    ( ! [X1] : (~m1_pre_topc(sK3,X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X1)) ) | ~spl4_45),
% 0.23/0.50    inference(avatar_component_clause,[],[f399])).
% 0.23/0.50  fof(f417,plain,(
% 0.23/0.50    spl4_6 | ~spl4_24 | spl4_10 | ~spl4_4 | spl4_8 | ~spl4_3 | spl4_47),
% 0.23/0.50    inference(avatar_split_clause,[],[f409,f405,f61,f81,f65,f89,f177,f73])).
% 0.23/0.50  fof(f73,plain,(
% 0.23/0.50    spl4_6 <=> v2_struct_0(sK3)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.23/0.50  fof(f89,plain,(
% 0.23/0.50    spl4_10 <=> v2_struct_0(sK1)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.23/0.50  fof(f65,plain,(
% 0.23/0.50    spl4_4 <=> m1_pre_topc(sK1,sK3)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.23/0.50  fof(f81,plain,(
% 0.23/0.50    spl4_8 <=> v2_struct_0(sK2)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.23/0.50  fof(f61,plain,(
% 0.23/0.50    spl4_3 <=> m1_pre_topc(sK2,sK3)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.23/0.50  fof(f409,plain,(
% 0.23/0.50    ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK3) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | spl4_47),
% 0.23/0.50    inference(resolution,[],[f406,f50])).
% 0.23/0.50  fof(f50,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f20])).
% 0.23/0.50  fof(f20,plain,(
% 0.23/0.50    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.50    inference(flattening,[],[f19])).
% 0.23/0.50  fof(f19,plain,(
% 0.23/0.50    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f4])).
% 0.23/0.50  fof(f4,axiom,(
% 0.23/0.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 0.23/0.50  fof(f406,plain,(
% 0.23/0.50    ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),sK3) | spl4_47),
% 0.23/0.50    inference(avatar_component_clause,[],[f405])).
% 0.23/0.50  fof(f407,plain,(
% 0.23/0.50    spl4_45 | spl4_46 | ~spl4_47 | spl4_1 | ~spl4_39),
% 0.23/0.50    inference(avatar_split_clause,[],[f397,f319,f53,f405,f402,f399])).
% 0.23/0.50  fof(f53,plain,(
% 0.23/0.50    spl4_1 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.23/0.50  fof(f319,plain,(
% 0.23/0.50    spl4_39 <=> ! [X1,X0] : (r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X1) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,X1))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.23/0.50  fof(f397,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),sK3) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (spl4_1 | ~spl4_39)),
% 0.23/0.50    inference(resolution,[],[f322,f54])).
% 0.23/0.50  fof(f54,plain,(
% 0.23/0.50    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) | spl4_1),
% 0.23/0.50    inference(avatar_component_clause,[],[f53])).
% 0.23/0.50  fof(f322,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X1) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) ) | ~spl4_39),
% 0.23/0.50    inference(resolution,[],[f320,f46])).
% 0.23/0.50  fof(f46,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f27])).
% 0.23/0.50  fof(f27,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.50    inference(nnf_transformation,[],[f18])).
% 0.23/0.50  fof(f18,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.50    inference(flattening,[],[f17])).
% 0.23/0.50  fof(f17,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f6])).
% 0.23/0.50  fof(f6,axiom,(
% 0.23/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.23/0.50  fof(f320,plain,(
% 0.23/0.50    ( ! [X0,X1] : (r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X1) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,X1)) ) | ~spl4_39),
% 0.23/0.50    inference(avatar_component_clause,[],[f319])).
% 0.23/0.50  fof(f321,plain,(
% 0.23/0.50    ~spl4_12 | spl4_39 | ~spl4_11 | ~spl4_17),
% 0.23/0.50    inference(avatar_split_clause,[],[f317,f140,f93,f319,f97])).
% 0.23/0.50  fof(f140,plain,(
% 0.23/0.50    spl4_17 <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.23/0.50  fof(f317,plain,(
% 0.23/0.50    ( ! [X0,X1] : (r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X1) | ~v2_pre_topc(sK0)) ) | (~spl4_11 | ~spl4_17)),
% 0.23/0.50    inference(duplicate_literal_removal,[],[f315])).
% 0.23/0.50  fof(f315,plain,(
% 0.23/0.50    ( ! [X0,X1] : (r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X1) | ~v2_pre_topc(sK0)) ) | (~spl4_11 | ~spl4_17)),
% 0.23/0.50    inference(resolution,[],[f294,f94])).
% 0.23/0.50  fof(f94,plain,(
% 0.23/0.50    l1_pre_topc(sK0) | ~spl4_11),
% 0.23/0.50    inference(avatar_component_clause,[],[f93])).
% 0.23/0.50  fof(f294,plain,(
% 0.23/0.50    ( ! [X2,X3,X1] : (~l1_pre_topc(X3) | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X2)) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X2) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X1) | ~v2_pre_topc(X3)) ) | (~spl4_11 | ~spl4_17)),
% 0.23/0.50    inference(resolution,[],[f291,f45])).
% 0.23/0.50  fof(f45,plain,(
% 0.23/0.50    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f16])).
% 0.23/0.50  fof(f16,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.50    inference(flattening,[],[f15])).
% 0.23/0.50  fof(f15,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f1])).
% 0.23/0.50  fof(f1,axiom,(
% 0.23/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.23/0.50  fof(f291,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~v2_pre_topc(X1) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X1) | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0)) ) | (~spl4_11 | ~spl4_17)),
% 0.23/0.50    inference(resolution,[],[f276,f94])).
% 0.23/0.50  fof(f276,plain,(
% 0.23/0.50    ( ! [X2,X3,X1] : (~l1_pre_topc(X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X2) | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X1)) | ~v2_pre_topc(X2) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X1)) ) | ~spl4_17),
% 0.23/0.50    inference(resolution,[],[f162,f42])).
% 0.23/0.50  fof(f42,plain,(
% 0.23/0.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f12])).
% 0.23/0.50  fof(f12,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f2])).
% 0.23/0.50  fof(f2,axiom,(
% 0.23/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.23/0.50  fof(f162,plain,(
% 0.23/0.50    ( ! [X12,X13] : (~l1_pre_topc(X13) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X12) | ~m1_pre_topc(X12,X13) | ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X13) | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X12)) | ~v2_pre_topc(X13)) ) | ~spl4_17),
% 0.23/0.50    inference(superposition,[],[f47,f141])).
% 0.23/0.50  fof(f141,plain,(
% 0.23/0.50    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) | ~spl4_17),
% 0.23/0.50    inference(avatar_component_clause,[],[f140])).
% 0.23/0.50  fof(f47,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f27])).
% 0.23/0.50  fof(f274,plain,(
% 0.23/0.50    spl4_13 | ~spl4_11 | spl4_10 | ~spl4_9 | spl4_8 | ~spl4_7 | spl4_37),
% 0.23/0.50    inference(avatar_split_clause,[],[f273,f270,f77,f81,f85,f89,f93,f101])).
% 0.23/0.50  fof(f101,plain,(
% 0.23/0.50    spl4_13 <=> v2_struct_0(sK0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.23/0.50  fof(f85,plain,(
% 0.23/0.50    spl4_9 <=> m1_pre_topc(sK1,sK0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.23/0.50  fof(f77,plain,(
% 0.23/0.50    spl4_7 <=> m1_pre_topc(sK2,sK0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.23/0.50  fof(f273,plain,(
% 0.23/0.50    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_37),
% 0.23/0.50    inference(resolution,[],[f271,f50])).
% 0.23/0.50  fof(f271,plain,(
% 0.23/0.50    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | spl4_37),
% 0.23/0.50    inference(avatar_component_clause,[],[f270])).
% 0.23/0.50  fof(f186,plain,(
% 0.23/0.50    ~spl4_11 | ~spl4_5 | spl4_24),
% 0.23/0.50    inference(avatar_split_clause,[],[f182,f177,f69,f93])).
% 0.23/0.50  fof(f182,plain,(
% 0.23/0.50    ~l1_pre_topc(sK0) | (~spl4_5 | spl4_24)),
% 0.23/0.50    inference(resolution,[],[f181,f70])).
% 0.23/0.50  fof(f181,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl4_24),
% 0.23/0.50    inference(resolution,[],[f178,f42])).
% 0.23/0.50  fof(f178,plain,(
% 0.23/0.50    ~l1_pre_topc(sK3) | spl4_24),
% 0.23/0.50    inference(avatar_component_clause,[],[f177])).
% 0.23/0.50  fof(f143,plain,(
% 0.23/0.50    spl4_6 | ~spl4_5 | spl4_17 | ~spl4_4 | ~spl4_3 | ~spl4_11 | ~spl4_14 | ~spl4_15),
% 0.23/0.50    inference(avatar_split_clause,[],[f134,f120,f112,f93,f61,f65,f140,f69,f73])).
% 0.23/0.50  fof(f112,plain,(
% 0.23/0.50    spl4_14 <=> ! [X0] : (k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2)) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK2,X0))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.23/0.50  fof(f120,plain,(
% 0.23/0.50    spl4_15 <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.23/0.50  fof(f134,plain,(
% 0.23/0.50    ~m1_pre_topc(sK1,sK3) | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | (~spl4_3 | ~spl4_11 | ~spl4_14 | ~spl4_15)),
% 0.23/0.50    inference(resolution,[],[f132,f62])).
% 0.23/0.50  fof(f62,plain,(
% 0.23/0.50    m1_pre_topc(sK2,sK3) | ~spl4_3),
% 0.23/0.50    inference(avatar_component_clause,[],[f61])).
% 0.23/0.50  fof(f132,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK1,X0) | u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | (~spl4_11 | ~spl4_14 | ~spl4_15)),
% 0.23/0.50    inference(forward_demodulation,[],[f130,f121])).
% 0.23/0.50  fof(f121,plain,(
% 0.23/0.50    k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl4_15),
% 0.23/0.50    inference(avatar_component_clause,[],[f120])).
% 0.23/0.50  fof(f130,plain,(
% 0.23/0.50    ( ! [X0] : (k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2)) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | (~spl4_11 | ~spl4_14)),
% 0.23/0.50    inference(resolution,[],[f116,f94])).
% 0.23/0.50  fof(f116,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~l1_pre_topc(X1) | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2)) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0)) ) | ~spl4_14),
% 0.23/0.50    inference(resolution,[],[f113,f42])).
% 0.23/0.50  fof(f113,plain,(
% 0.23/0.50    ( ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(X0) | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2)) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK2,X0)) ) | ~spl4_14),
% 0.23/0.50    inference(avatar_component_clause,[],[f112])).
% 0.23/0.50  fof(f123,plain,(
% 0.23/0.50    ~spl4_7 | ~spl4_9 | spl4_15 | spl4_13 | ~spl4_11 | ~spl4_14),
% 0.23/0.50    inference(avatar_split_clause,[],[f115,f112,f93,f101,f120,f85,f77])).
% 0.23/0.50  fof(f115,plain,(
% 0.23/0.50    v2_struct_0(sK0) | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK2,sK0) | (~spl4_11 | ~spl4_14)),
% 0.23/0.50    inference(resolution,[],[f113,f94])).
% 0.23/0.50  fof(f114,plain,(
% 0.23/0.50    spl4_10 | spl4_8 | spl4_14 | spl4_2),
% 0.23/0.50    inference(avatar_split_clause,[],[f108,f57,f112,f81,f89])).
% 0.23/0.50  fof(f57,plain,(
% 0.23/0.50    spl4_2 <=> r1_tsep_1(sK1,sK2)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.23/0.50  fof(f108,plain,(
% 0.23/0.50    ( ! [X0] : (k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2)) | ~m1_pre_topc(sK2,X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | spl4_2),
% 0.23/0.50    inference(resolution,[],[f106,f58])).
% 0.23/0.50  fof(f58,plain,(
% 0.23/0.50    ~r1_tsep_1(sK1,sK2) | spl4_2),
% 0.23/0.50    inference(avatar_component_clause,[],[f57])).
% 0.23/0.50  fof(f106,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f105,f48])).
% 0.23/0.50  fof(f48,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f20])).
% 0.23/0.50  fof(f105,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f104,f49])).
% 0.23/0.50  fof(f49,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f20])).
% 0.23/0.50  fof(f104,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f51,f50])).
% 0.23/0.50  fof(f51,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.50    inference(equality_resolution,[],[f43])).
% 0.23/0.50  fof(f43,plain,(
% 0.23/0.50    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f26])).
% 0.23/0.50  fof(f26,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.50    inference(nnf_transformation,[],[f14])).
% 0.23/0.50  fof(f14,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.50    inference(flattening,[],[f13])).
% 0.23/0.50  fof(f13,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f3])).
% 0.23/0.50  fof(f3,axiom,(
% 0.23/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).
% 0.23/0.50  fof(f103,plain,(
% 0.23/0.50    ~spl4_13),
% 0.23/0.50    inference(avatar_split_clause,[],[f28,f101])).
% 0.23/0.50  fof(f28,plain,(
% 0.23/0.50    ~v2_struct_0(sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f25,plain,(
% 0.23/0.50    (((~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f24,f23,f22,f21])).
% 0.23/0.50  fof(f21,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f22,plain,(
% 0.23/0.50    ? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f23,plain,(
% 0.23/0.50    ? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f24,plain,(
% 0.23/0.50    ? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f10,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.23/0.50    inference(flattening,[],[f9])).
% 0.23/0.50  fof(f9,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f8])).
% 0.23/0.50  fof(f8,negated_conjecture,(
% 0.23/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 0.23/0.50    inference(negated_conjecture,[],[f7])).
% 0.23/0.50  fof(f7,conjecture,(
% 0.23/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).
% 0.23/0.50  fof(f99,plain,(
% 0.23/0.50    spl4_12),
% 0.23/0.50    inference(avatar_split_clause,[],[f29,f97])).
% 0.23/0.50  fof(f29,plain,(
% 0.23/0.50    v2_pre_topc(sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f95,plain,(
% 0.23/0.50    spl4_11),
% 0.23/0.50    inference(avatar_split_clause,[],[f30,f93])).
% 0.23/0.50  fof(f30,plain,(
% 0.23/0.50    l1_pre_topc(sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f91,plain,(
% 0.23/0.50    ~spl4_10),
% 0.23/0.50    inference(avatar_split_clause,[],[f31,f89])).
% 0.23/0.50  fof(f31,plain,(
% 0.23/0.50    ~v2_struct_0(sK1)),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f87,plain,(
% 0.23/0.50    spl4_9),
% 0.23/0.50    inference(avatar_split_clause,[],[f32,f85])).
% 0.23/0.50  fof(f32,plain,(
% 0.23/0.50    m1_pre_topc(sK1,sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f83,plain,(
% 0.23/0.50    ~spl4_8),
% 0.23/0.50    inference(avatar_split_clause,[],[f33,f81])).
% 0.23/0.50  fof(f33,plain,(
% 0.23/0.50    ~v2_struct_0(sK2)),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f79,plain,(
% 0.23/0.50    spl4_7),
% 0.23/0.50    inference(avatar_split_clause,[],[f34,f77])).
% 0.23/0.50  fof(f34,plain,(
% 0.23/0.50    m1_pre_topc(sK2,sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f75,plain,(
% 0.23/0.50    ~spl4_6),
% 0.23/0.50    inference(avatar_split_clause,[],[f35,f73])).
% 0.23/0.50  fof(f35,plain,(
% 0.23/0.50    ~v2_struct_0(sK3)),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f71,plain,(
% 0.23/0.50    spl4_5),
% 0.23/0.50    inference(avatar_split_clause,[],[f36,f69])).
% 0.23/0.50  fof(f36,plain,(
% 0.23/0.50    m1_pre_topc(sK3,sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f67,plain,(
% 0.23/0.50    spl4_4),
% 0.23/0.50    inference(avatar_split_clause,[],[f37,f65])).
% 0.23/0.50  fof(f37,plain,(
% 0.23/0.50    m1_pre_topc(sK1,sK3)),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f63,plain,(
% 0.23/0.50    spl4_3),
% 0.23/0.50    inference(avatar_split_clause,[],[f38,f61])).
% 0.23/0.50  fof(f38,plain,(
% 0.23/0.50    m1_pre_topc(sK2,sK3)),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f59,plain,(
% 0.23/0.50    ~spl4_2),
% 0.23/0.50    inference(avatar_split_clause,[],[f39,f57])).
% 0.23/0.50  fof(f39,plain,(
% 0.23/0.50    ~r1_tsep_1(sK1,sK2)),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f55,plain,(
% 0.23/0.50    ~spl4_1),
% 0.23/0.50    inference(avatar_split_clause,[],[f40,f53])).
% 0.23/0.50  fof(f40,plain,(
% 0.23/0.50    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  % SZS output end Proof for theBenchmark
% 0.23/0.50  % (26887)------------------------------
% 0.23/0.50  % (26887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (26887)Termination reason: Refutation
% 0.23/0.50  
% 0.23/0.50  % (26887)Memory used [KB]: 10874
% 0.23/0.50  % (26887)Time elapsed: 0.014 s
% 0.23/0.50  % (26887)------------------------------
% 0.23/0.50  % (26887)------------------------------
% 0.23/0.50  % (26880)Success in time 0.13 s
%------------------------------------------------------------------------------
