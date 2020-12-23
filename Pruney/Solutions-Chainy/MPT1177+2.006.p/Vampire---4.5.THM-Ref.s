%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:18 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 352 expanded)
%              Number of leaves         :   41 ( 165 expanded)
%              Depth                    :    9
%              Number of atoms          :  749 (1604 expanded)
%              Number of equality atoms :   42 (  56 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f514,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f91,f96,f101,f110,f111,f139,f144,f150,f162,f169,f188,f234,f303,f362,f363,f364,f382,f388,f413,f429,f481,f487,f488,f501,f505])).

fof(f505,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | spl4_56 ),
    inference(avatar_contradiction_clause,[],[f502])).

fof(f502,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | spl4_56 ),
    inference(unit_resulting_resolution,[],[f85,f75,f80,f65,f70,f100,f90,f500,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f500,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_56 ),
    inference(avatar_component_clause,[],[f498])).

fof(f498,plain,
    ( spl4_56
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f90,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_6
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f100,plain,
    ( m2_orders_2(sK3,sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_8
  <=> m2_orders_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f70,plain,
    ( v5_orders_2(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl4_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f65,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f80,plain,
    ( v3_orders_2(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_4
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f75,plain,
    ( v4_orders_2(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f85,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f501,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_56
    | ~ spl4_10
    | spl4_5
    | ~ spl4_4
    | ~ spl4_1
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f496,f360,f63,f78,f83,f107,f498,f73,f68])).

fof(f107,plain,
    ( spl4_10
  <=> m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f360,plain,
    ( spl4_43
  <=> ! [X0] :
        ( ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_orders_2(sK2,X0,sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_orders_2(X0)
        | ~ v5_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f496,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK2,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl4_1
    | ~ spl4_43 ),
    inference(resolution,[],[f361,f65])).

fof(f361,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_orders_2(sK2,X0,sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0) )
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f360])).

fof(f488,plain,
    ( k1_xboole_0 != sK3
    | m1_orders_2(sK2,sK0,k1_xboole_0)
    | ~ m1_orders_2(sK2,sK0,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f487,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_10
    | spl4_39
    | spl4_40 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_10
    | spl4_39
    | spl4_40 ),
    inference(unit_resulting_resolution,[],[f65,f85,f80,f70,f75,f324,f109,f100,f95,f90,f321,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_orders_2(X3,X0,X2)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m2_orders_2(X3,X0,X1)
      | X2 = X3
      | v2_struct_0(X0)
      | m1_orders_2(X2,X0,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).

fof(f321,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | spl4_39 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl4_39
  <=> m1_orders_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f95,plain,
    ( m2_orders_2(sK2,sK0,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_7
  <=> m2_orders_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f109,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f324,plain,
    ( sK2 != sK3
    | spl4_40 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl4_40
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f481,plain,
    ( spl4_40
    | ~ spl4_7
    | ~ spl4_39
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f478,f427,f103,f88,f319,f93,f323])).

fof(f103,plain,
    ( spl4_9
  <=> r2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f427,plain,
    ( spl4_50
  <=> ! [X3,X5,X4] :
        ( X3 = X4
        | ~ m2_orders_2(X3,sK0,X5)
        | ~ m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X4,sK0,X3)
        | ~ r1_tarski(X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f478,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | ~ m2_orders_2(sK2,sK0,sK1)
    | sK2 = sK3
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_50 ),
    inference(resolution,[],[f475,f104])).

fof(f104,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f475,plain,
    ( ! [X4,X5] :
        ( ~ r2_xboole_0(X4,X5)
        | ~ m1_orders_2(X5,sK0,X4)
        | ~ m2_orders_2(X4,sK0,sK1)
        | X4 = X5 )
    | ~ spl4_6
    | ~ spl4_50 ),
    inference(resolution,[],[f471,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f471,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | X0 = X1
        | ~ m1_orders_2(X1,sK0,X0)
        | ~ m2_orders_2(X0,sK0,sK1) )
    | ~ spl4_6
    | ~ spl4_50 ),
    inference(resolution,[],[f428,f90])).

fof(f428,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X3,sK0,X5)
        | X3 = X4
        | ~ m1_orders_2(X4,sK0,X3)
        | ~ r1_tarski(X3,X4) )
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f427])).

fof(f429,plain,
    ( spl4_5
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_50
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f420,f411,f427,f78,f73,f68,f63,f83])).

fof(f411,plain,
    ( spl4_48
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | X0 = X1
        | ~ r1_tarski(X0,X1)
        | ~ m1_orders_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f420,plain,
    ( ! [X4,X5,X3] :
        ( X3 = X4
        | ~ r1_tarski(X3,X4)
        | ~ m1_orders_2(X4,sK0,X3)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X3,sK0,X5)
        | v2_struct_0(sK0) )
    | ~ spl4_48 ),
    inference(resolution,[],[f412,f51])).

fof(f412,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | X0 = X1
        | ~ r1_tarski(X0,X1)
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f411])).

fof(f413,plain,
    ( spl4_5
    | spl4_48
    | ~ spl4_4
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f409,f63,f73,f68,f78,f411,f83])).

fof(f409,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | v2_struct_0(sK0)
        | ~ r1_tarski(X0,X1)
        | X0 = X1 )
    | ~ spl4_1 ),
    inference(resolution,[],[f124,f65])).

fof(f124,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ v3_orders_2(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_orders_2(X5,X3,X4)
      | v2_struct_0(X3)
      | ~ r1_tarski(X4,X5)
      | X4 = X5 ) ),
    inference(resolution,[],[f47,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

fof(f388,plain,(
    ~ spl4_45 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | ~ spl4_45 ),
    inference(unit_resulting_resolution,[],[f61,f381])).

fof(f381,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl4_45
  <=> r2_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f61,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f382,plain,
    ( spl4_45
    | ~ spl4_9
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f377,f323,f103,f379])).

fof(f377,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ spl4_9
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f104,f325])).

fof(f325,plain,
    ( sK2 = sK3
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f323])).

fof(f364,plain,
    ( k1_xboole_0 != sK3
    | m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ m2_orders_2(sK3,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f363,plain,
    ( sK2 != sK3
    | m1_orders_2(sK3,sK0,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f362,plain,
    ( spl4_40
    | spl4_43
    | spl4_9 ),
    inference(avatar_split_clause,[],[f352,f103,f360,f323])).

fof(f352,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_orders_2(sK2,X0,sK3)
        | v2_struct_0(X0)
        | sK2 = sK3
        | ~ v3_orders_2(X0) )
    | spl4_9 ),
    inference(resolution,[],[f123,f105])).

fof(f105,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( r2_xboole_0(X2,X1)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | v2_struct_0(X0)
      | X1 = X2
      | ~ v3_orders_2(X0) ) ),
    inference(resolution,[],[f47,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f303,plain,
    ( spl4_37
    | ~ spl4_38
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f285,f232,f98,f88,f300,f296])).

fof(f296,plain,
    ( spl4_37
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f300,plain,
    ( spl4_38
  <=> m1_orders_2(sK3,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f232,plain,
    ( spl4_27
  <=> ! [X3,X2] :
        ( ~ m1_orders_2(X2,sK0,X2)
        | ~ m2_orders_2(X2,sK0,X3)
        | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f285,plain,
    ( ~ m1_orders_2(sK3,sK0,sK3)
    | k1_xboole_0 = sK3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_27 ),
    inference(resolution,[],[f283,f100])).

fof(f283,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ m1_orders_2(X0,sK0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_6
    | ~ spl4_27 ),
    inference(resolution,[],[f233,f90])).

fof(f233,plain,
    ( ! [X2,X3] :
        ( ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X2,sK0,X3)
        | ~ m1_orders_2(X2,sK0,X2)
        | k1_xboole_0 = X2 )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f232])).

fof(f234,plain,
    ( spl4_5
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_27
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f225,f167,f232,f78,f73,f68,f63,f83])).

fof(f167,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f225,plain,
    ( ! [X2,X3] :
        ( ~ m1_orders_2(X2,sK0,X2)
        | k1_xboole_0 = X2
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X2,sK0,X3)
        | v2_struct_0(sK0) )
    | ~ spl4_17 ),
    inference(resolution,[],[f203,f51])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X0,sK0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_17 ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X0,sK0,X0)
        | k1_xboole_0 = X0
        | ~ m1_orders_2(X0,sK0,X0) )
    | ~ spl4_17 ),
    inference(factoring,[],[f168])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X0
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f167])).

fof(f188,plain,
    ( ~ spl4_20
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f182,f160,f93,f88,f185])).

fof(f185,plain,
    ( spl4_20
  <=> m1_orders_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f160,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,k1_xboole_0)
        | ~ m2_orders_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f182,plain,
    ( ~ m1_orders_2(sK2,sK0,k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(resolution,[],[f181,f95])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ m1_orders_2(X0,sK0,k1_xboole_0) )
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(resolution,[],[f161,f90])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,k1_xboole_0)
        | ~ m2_orders_2(X1,sK0,X0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f160])).

fof(f169,plain,
    ( spl4_17
    | spl4_5
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f165,f63,f78,f73,f68,f83,f167])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f48,f65])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X1,X0,X2)
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

fof(f162,plain,
    ( spl4_5
    | spl4_16
    | ~ spl4_4
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f158,f133,f63,f73,f68,f78,f160,f83])).

fof(f133,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( ~ m1_orders_2(X0,sK0,k1_xboole_0)
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X1,sK0,X0)
        | v2_struct_0(sK0)
        | ~ m1_orders_2(X1,sK0,k1_xboole_0) )
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(resolution,[],[f157,f65])).

fof(f157,plain,
    ( ! [X4,X2,X3] :
        ( ~ l1_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v5_orders_2(X2)
        | ~ v3_orders_2(X2)
        | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
        | ~ m2_orders_2(X4,X2,X3)
        | v2_struct_0(X2)
        | ~ m1_orders_2(X4,sK0,k1_xboole_0) )
    | ~ spl4_11 ),
    inference(resolution,[],[f44,f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_orders_2(X0,sK0,k1_xboole_0) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f150,plain,
    ( ~ spl4_14
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f145,f142,f88,f147])).

fof(f147,plain,
    ( spl4_14
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f142,plain,
    ( spl4_13
  <=> ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f145,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(resolution,[],[f143,f90])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f142])).

fof(f144,plain,
    ( spl4_5
    | spl4_13
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_12 ),
    inference(avatar_split_clause,[],[f140,f136,f78,f73,f68,f63,f142,f83])).

fof(f136,plain,
    ( spl4_12
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | v2_struct_0(sK0) )
    | spl4_12 ),
    inference(resolution,[],[f51,f138])).

fof(f138,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f139,plain,
    ( spl4_5
    | spl4_11
    | ~ spl4_12
    | ~ spl4_4
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f131,f63,f73,f68,f78,f136,f133,f83])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X0,sK0,k1_xboole_0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f126,f65])).

fof(f126,plain,(
    ! [X10,X11,X9] :
      ( ~ l1_orders_2(X9)
      | ~ v4_orders_2(X9)
      | ~ v5_orders_2(X9)
      | ~ v3_orders_2(X9)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ m1_orders_2(X10,X9,k1_xboole_0)
      | v2_struct_0(X9)
      | ~ r2_hidden(X11,X10) ) ),
    inference(resolution,[],[f47,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f112,f43])).

fof(f43,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f50,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f111,plain,
    ( spl4_9
    | spl4_10 ),
    inference(avatar_split_clause,[],[f33,f107,f103])).

fof(f33,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
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
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).

fof(f110,plain,
    ( ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f34,f107,f103])).

fof(f34,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f35,f98])).

fof(f35,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f96,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f36,f93])).

fof(f36,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f37,f88])).

fof(f37,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f38,f83])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f81,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f39,f78])).

fof(f39,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f40,f73])).

fof(f40,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f41,f68])).

fof(f41,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f42,f63])).

fof(f42,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n024.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 18:51:36 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.23/0.46  % (27311)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.47  % (27319)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.48  % (27319)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.49  % (27311)Refutation not found, incomplete strategy% (27311)------------------------------
% 0.23/0.49  % (27311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (27311)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.49  
% 0.23/0.49  % (27311)Memory used [KB]: 1663
% 0.23/0.49  % (27311)Time elapsed: 0.062 s
% 0.23/0.49  % (27311)------------------------------
% 0.23/0.49  % (27311)------------------------------
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.49  fof(f514,plain,(
% 0.23/0.49    $false),
% 0.23/0.49    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f91,f96,f101,f110,f111,f139,f144,f150,f162,f169,f188,f234,f303,f362,f363,f364,f382,f388,f413,f429,f481,f487,f488,f501,f505])).
% 0.23/0.49  fof(f505,plain,(
% 0.23/0.49    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_8 | spl4_56),
% 0.23/0.49    inference(avatar_contradiction_clause,[],[f502])).
% 0.23/0.49  fof(f502,plain,(
% 0.23/0.49    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_8 | spl4_56)),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f85,f75,f80,f65,f70,f100,f90,f500,f51])).
% 0.23/0.49  fof(f51,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f30])).
% 0.23/0.49  fof(f30,plain,(
% 0.23/0.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.23/0.49    inference(flattening,[],[f29])).
% 0.23/0.49  fof(f29,plain,(
% 0.23/0.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f15])).
% 0.23/0.49  fof(f15,plain,(
% 0.23/0.49    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.23/0.49    inference(pure_predicate_removal,[],[f7])).
% 0.23/0.49  fof(f7,axiom,(
% 0.23/0.49    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.23/0.49  fof(f500,plain,(
% 0.23/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_56),
% 0.23/0.49    inference(avatar_component_clause,[],[f498])).
% 0.23/0.49  fof(f498,plain,(
% 0.23/0.49    spl4_56 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.23/0.49  fof(f90,plain,(
% 0.23/0.49    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl4_6),
% 0.23/0.49    inference(avatar_component_clause,[],[f88])).
% 0.23/0.49  fof(f88,plain,(
% 0.23/0.49    spl4_6 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.23/0.49  fof(f100,plain,(
% 0.23/0.49    m2_orders_2(sK3,sK0,sK1) | ~spl4_8),
% 0.23/0.49    inference(avatar_component_clause,[],[f98])).
% 0.23/0.49  fof(f98,plain,(
% 0.23/0.49    spl4_8 <=> m2_orders_2(sK3,sK0,sK1)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.23/0.49  fof(f70,plain,(
% 0.23/0.49    v5_orders_2(sK0) | ~spl4_2),
% 0.23/0.49    inference(avatar_component_clause,[],[f68])).
% 0.23/0.49  fof(f68,plain,(
% 0.23/0.49    spl4_2 <=> v5_orders_2(sK0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.23/0.49  fof(f65,plain,(
% 0.23/0.49    l1_orders_2(sK0) | ~spl4_1),
% 0.23/0.49    inference(avatar_component_clause,[],[f63])).
% 0.23/0.49  fof(f63,plain,(
% 0.23/0.49    spl4_1 <=> l1_orders_2(sK0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.23/0.49  fof(f80,plain,(
% 0.23/0.49    v3_orders_2(sK0) | ~spl4_4),
% 0.23/0.49    inference(avatar_component_clause,[],[f78])).
% 0.23/0.49  fof(f78,plain,(
% 0.23/0.49    spl4_4 <=> v3_orders_2(sK0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.23/0.49  fof(f75,plain,(
% 0.23/0.49    v4_orders_2(sK0) | ~spl4_3),
% 0.23/0.49    inference(avatar_component_clause,[],[f73])).
% 0.23/0.49  fof(f73,plain,(
% 0.23/0.49    spl4_3 <=> v4_orders_2(sK0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.23/0.49  fof(f85,plain,(
% 0.23/0.49    ~v2_struct_0(sK0) | spl4_5),
% 0.23/0.49    inference(avatar_component_clause,[],[f83])).
% 0.23/0.49  fof(f83,plain,(
% 0.23/0.49    spl4_5 <=> v2_struct_0(sK0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.23/0.49  fof(f501,plain,(
% 0.23/0.49    ~spl4_2 | ~spl4_3 | ~spl4_56 | ~spl4_10 | spl4_5 | ~spl4_4 | ~spl4_1 | ~spl4_43),
% 0.23/0.49    inference(avatar_split_clause,[],[f496,f360,f63,f78,f83,f107,f498,f73,f68])).
% 0.23/0.49  fof(f107,plain,(
% 0.23/0.49    spl4_10 <=> m1_orders_2(sK2,sK0,sK3)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.23/0.49  fof(f360,plain,(
% 0.23/0.49    spl4_43 <=> ! [X0] : (~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_2(sK2,X0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.23/0.49  fof(f496,plain,(
% 0.23/0.49    ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | (~spl4_1 | ~spl4_43)),
% 0.23/0.49    inference(resolution,[],[f361,f65])).
% 0.23/0.49  fof(f361,plain,(
% 0.23/0.49    ( ! [X0] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_2(sK2,X0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_orders_2(X0) | ~v5_orders_2(X0)) ) | ~spl4_43),
% 0.23/0.49    inference(avatar_component_clause,[],[f360])).
% 0.23/0.49  fof(f488,plain,(
% 0.23/0.49    k1_xboole_0 != sK3 | m1_orders_2(sK2,sK0,k1_xboole_0) | ~m1_orders_2(sK2,sK0,sK3)),
% 0.23/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.23/0.49  fof(f487,plain,(
% 0.23/0.49    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | spl4_10 | spl4_39 | spl4_40),
% 0.23/0.49    inference(avatar_contradiction_clause,[],[f484])).
% 0.23/0.49  fof(f484,plain,(
% 0.23/0.49    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | spl4_10 | spl4_39 | spl4_40)),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f65,f85,f80,f70,f75,f324,f109,f100,f95,f90,f321,f45])).
% 0.23/0.49  fof(f45,plain,(
% 0.23/0.49    ( ! [X2,X0,X3,X1] : (m1_orders_2(X3,X0,X2) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m2_orders_2(X3,X0,X1) | X2 = X3 | v2_struct_0(X0) | m1_orders_2(X2,X0,X3)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f21])).
% 0.23/0.49  fof(f21,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.23/0.49    inference(flattening,[],[f20])).
% 0.23/0.49  fof(f20,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f11])).
% 0.23/0.49  fof(f11,axiom,(
% 0.23/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).
% 0.23/0.49  fof(f321,plain,(
% 0.23/0.49    ~m1_orders_2(sK3,sK0,sK2) | spl4_39),
% 0.23/0.49    inference(avatar_component_clause,[],[f319])).
% 0.23/0.49  fof(f319,plain,(
% 0.23/0.49    spl4_39 <=> m1_orders_2(sK3,sK0,sK2)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.23/0.49  fof(f95,plain,(
% 0.23/0.49    m2_orders_2(sK2,sK0,sK1) | ~spl4_7),
% 0.23/0.49    inference(avatar_component_clause,[],[f93])).
% 0.23/0.49  fof(f93,plain,(
% 0.23/0.49    spl4_7 <=> m2_orders_2(sK2,sK0,sK1)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.23/0.49  fof(f109,plain,(
% 0.23/0.49    ~m1_orders_2(sK2,sK0,sK3) | spl4_10),
% 0.23/0.49    inference(avatar_component_clause,[],[f107])).
% 0.23/0.49  fof(f324,plain,(
% 0.23/0.49    sK2 != sK3 | spl4_40),
% 0.23/0.49    inference(avatar_component_clause,[],[f323])).
% 0.23/0.49  fof(f323,plain,(
% 0.23/0.49    spl4_40 <=> sK2 = sK3),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.23/0.49  fof(f481,plain,(
% 0.23/0.49    spl4_40 | ~spl4_7 | ~spl4_39 | ~spl4_6 | ~spl4_9 | ~spl4_50),
% 0.23/0.49    inference(avatar_split_clause,[],[f478,f427,f103,f88,f319,f93,f323])).
% 0.23/0.49  fof(f103,plain,(
% 0.23/0.49    spl4_9 <=> r2_xboole_0(sK2,sK3)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.23/0.49  fof(f427,plain,(
% 0.23/0.49    spl4_50 <=> ! [X3,X5,X4] : (X3 = X4 | ~m2_orders_2(X3,sK0,X5) | ~m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0))) | ~m1_orders_2(X4,sK0,X3) | ~r1_tarski(X3,X4))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.23/0.49  fof(f478,plain,(
% 0.23/0.49    ~m1_orders_2(sK3,sK0,sK2) | ~m2_orders_2(sK2,sK0,sK1) | sK2 = sK3 | (~spl4_6 | ~spl4_9 | ~spl4_50)),
% 0.23/0.49    inference(resolution,[],[f475,f104])).
% 0.23/0.49  fof(f104,plain,(
% 0.23/0.49    r2_xboole_0(sK2,sK3) | ~spl4_9),
% 0.23/0.49    inference(avatar_component_clause,[],[f103])).
% 0.23/0.49  fof(f475,plain,(
% 0.23/0.49    ( ! [X4,X5] : (~r2_xboole_0(X4,X5) | ~m1_orders_2(X5,sK0,X4) | ~m2_orders_2(X4,sK0,sK1) | X4 = X5) ) | (~spl4_6 | ~spl4_50)),
% 0.23/0.49    inference(resolution,[],[f471,f56])).
% 0.23/0.49  fof(f56,plain,(
% 0.23/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f2])).
% 0.23/0.49  fof(f2,axiom,(
% 0.23/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.23/0.49  fof(f471,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~m1_orders_2(X1,sK0,X0) | ~m2_orders_2(X0,sK0,sK1)) ) | (~spl4_6 | ~spl4_50)),
% 0.23/0.49    inference(resolution,[],[f428,f90])).
% 0.23/0.49  fof(f428,plain,(
% 0.23/0.49    ( ! [X4,X5,X3] : (~m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X3,sK0,X5) | X3 = X4 | ~m1_orders_2(X4,sK0,X3) | ~r1_tarski(X3,X4)) ) | ~spl4_50),
% 0.23/0.49    inference(avatar_component_clause,[],[f427])).
% 0.23/0.49  fof(f429,plain,(
% 0.23/0.49    spl4_5 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_50 | ~spl4_48),
% 0.23/0.49    inference(avatar_split_clause,[],[f420,f411,f427,f78,f73,f68,f63,f83])).
% 0.23/0.49  fof(f411,plain,(
% 0.23/0.49    spl4_48 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | X0 = X1 | ~r1_tarski(X0,X1) | ~m1_orders_2(X1,sK0,X0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.23/0.49  fof(f420,plain,(
% 0.23/0.49    ( ! [X4,X5,X3] : (X3 = X4 | ~r1_tarski(X3,X4) | ~m1_orders_2(X4,sK0,X3) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(X5,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X3,sK0,X5) | v2_struct_0(sK0)) ) | ~spl4_48),
% 0.23/0.49    inference(resolution,[],[f412,f51])).
% 0.23/0.49  fof(f412,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | X0 = X1 | ~r1_tarski(X0,X1) | ~m1_orders_2(X1,sK0,X0)) ) | ~spl4_48),
% 0.23/0.49    inference(avatar_component_clause,[],[f411])).
% 0.23/0.49  fof(f413,plain,(
% 0.23/0.49    spl4_5 | spl4_48 | ~spl4_4 | ~spl4_2 | ~spl4_3 | ~spl4_1),
% 0.23/0.49    inference(avatar_split_clause,[],[f409,f63,f73,f68,f78,f411,f83])).
% 0.23/0.49  fof(f409,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v3_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | v2_struct_0(sK0) | ~r1_tarski(X0,X1) | X0 = X1) ) | ~spl4_1),
% 0.23/0.49    inference(resolution,[],[f124,f65])).
% 0.23/0.49  fof(f124,plain,(
% 0.23/0.49    ( ! [X4,X5,X3] : (~l1_orders_2(X3) | ~v4_orders_2(X3) | ~v5_orders_2(X3) | ~v3_orders_2(X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_orders_2(X5,X3,X4) | v2_struct_0(X3) | ~r1_tarski(X4,X5) | X4 = X5) )),
% 0.23/0.49    inference(resolution,[],[f47,f55])).
% 0.23/0.49  fof(f55,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.23/0.49    inference(cnf_transformation,[],[f3])).
% 0.23/0.49  fof(f3,axiom,(
% 0.23/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.49  fof(f47,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f23])).
% 0.23/0.49  fof(f23,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.23/0.49    inference(flattening,[],[f22])).
% 0.23/0.49  fof(f22,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f8])).
% 0.23/0.49  fof(f8,axiom,(
% 0.23/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).
% 0.23/0.49  fof(f388,plain,(
% 0.23/0.49    ~spl4_45),
% 0.23/0.49    inference(avatar_contradiction_clause,[],[f383])).
% 0.23/0.49  fof(f383,plain,(
% 0.23/0.49    $false | ~spl4_45),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f61,f381])).
% 0.23/0.49  fof(f381,plain,(
% 0.23/0.49    r2_xboole_0(sK2,sK2) | ~spl4_45),
% 0.23/0.49    inference(avatar_component_clause,[],[f379])).
% 0.23/0.49  fof(f379,plain,(
% 0.23/0.49    spl4_45 <=> r2_xboole_0(sK2,sK2)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.23/0.49  fof(f61,plain,(
% 0.23/0.49    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.23/0.49    inference(equality_resolution,[],[f57])).
% 0.23/0.49  fof(f57,plain,(
% 0.23/0.49    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f2])).
% 0.23/0.49  fof(f382,plain,(
% 0.23/0.49    spl4_45 | ~spl4_9 | ~spl4_40),
% 0.23/0.49    inference(avatar_split_clause,[],[f377,f323,f103,f379])).
% 0.23/0.49  fof(f377,plain,(
% 0.23/0.49    r2_xboole_0(sK2,sK2) | (~spl4_9 | ~spl4_40)),
% 0.23/0.49    inference(forward_demodulation,[],[f104,f325])).
% 0.23/0.49  fof(f325,plain,(
% 0.23/0.49    sK2 = sK3 | ~spl4_40),
% 0.23/0.49    inference(avatar_component_clause,[],[f323])).
% 0.23/0.49  fof(f364,plain,(
% 0.23/0.49    k1_xboole_0 != sK3 | m2_orders_2(k1_xboole_0,sK0,sK1) | ~m2_orders_2(sK3,sK0,sK1)),
% 0.23/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.23/0.49  fof(f363,plain,(
% 0.23/0.49    sK2 != sK3 | m1_orders_2(sK3,sK0,sK3) | ~m1_orders_2(sK2,sK0,sK3)),
% 0.23/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.23/0.49  fof(f362,plain,(
% 0.23/0.49    spl4_40 | spl4_43 | spl4_9),
% 0.23/0.49    inference(avatar_split_clause,[],[f352,f103,f360,f323])).
% 0.23/0.49  fof(f352,plain,(
% 0.23/0.49    ( ! [X0] : (~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(sK2,X0,sK3) | v2_struct_0(X0) | sK2 = sK3 | ~v3_orders_2(X0)) ) | spl4_9),
% 0.23/0.49    inference(resolution,[],[f123,f105])).
% 0.23/0.49  fof(f105,plain,(
% 0.23/0.49    ~r2_xboole_0(sK2,sK3) | spl4_9),
% 0.23/0.49    inference(avatar_component_clause,[],[f103])).
% 0.23/0.49  fof(f123,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (r2_xboole_0(X2,X1) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | v2_struct_0(X0) | X1 = X2 | ~v3_orders_2(X0)) )),
% 0.23/0.49    inference(resolution,[],[f47,f58])).
% 0.23/0.49  fof(f58,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f2])).
% 0.23/0.49  fof(f303,plain,(
% 0.23/0.49    spl4_37 | ~spl4_38 | ~spl4_6 | ~spl4_8 | ~spl4_27),
% 0.23/0.49    inference(avatar_split_clause,[],[f285,f232,f98,f88,f300,f296])).
% 0.23/0.49  fof(f296,plain,(
% 0.23/0.49    spl4_37 <=> k1_xboole_0 = sK3),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.23/0.49  fof(f300,plain,(
% 0.23/0.49    spl4_38 <=> m1_orders_2(sK3,sK0,sK3)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.23/0.49  fof(f232,plain,(
% 0.23/0.49    spl4_27 <=> ! [X3,X2] : (~m1_orders_2(X2,sK0,X2) | ~m2_orders_2(X2,sK0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(sK0))) | k1_xboole_0 = X2)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.23/0.49  fof(f285,plain,(
% 0.23/0.49    ~m1_orders_2(sK3,sK0,sK3) | k1_xboole_0 = sK3 | (~spl4_6 | ~spl4_8 | ~spl4_27)),
% 0.23/0.49    inference(resolution,[],[f283,f100])).
% 0.23/0.49  fof(f283,plain,(
% 0.23/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X0,sK0,X0) | k1_xboole_0 = X0) ) | (~spl4_6 | ~spl4_27)),
% 0.23/0.49    inference(resolution,[],[f233,f90])).
% 0.23/0.49  fof(f233,plain,(
% 0.23/0.49    ( ! [X2,X3] : (~m1_orders_1(X3,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X2,sK0,X3) | ~m1_orders_2(X2,sK0,X2) | k1_xboole_0 = X2) ) | ~spl4_27),
% 0.23/0.49    inference(avatar_component_clause,[],[f232])).
% 0.23/0.49  fof(f234,plain,(
% 0.23/0.49    spl4_5 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_27 | ~spl4_17),
% 0.23/0.49    inference(avatar_split_clause,[],[f225,f167,f232,f78,f73,f68,f63,f83])).
% 0.23/0.49  fof(f167,plain,(
% 0.23/0.49    spl4_17 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | ~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.23/0.49  fof(f225,plain,(
% 0.23/0.49    ( ! [X2,X3] : (~m1_orders_2(X2,sK0,X2) | k1_xboole_0 = X2 | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X2,sK0,X3) | v2_struct_0(sK0)) ) | ~spl4_17),
% 0.23/0.49    inference(resolution,[],[f203,f51])).
% 0.23/0.49  fof(f203,plain,(
% 0.23/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X0,sK0,X0) | k1_xboole_0 = X0) ) | ~spl4_17),
% 0.23/0.49    inference(duplicate_literal_removal,[],[f202])).
% 0.23/0.49  fof(f202,plain,(
% 0.23/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X0,sK0,X0) | k1_xboole_0 = X0 | ~m1_orders_2(X0,sK0,X0)) ) | ~spl4_17),
% 0.23/0.49    inference(factoring,[],[f168])).
% 0.23/0.49  fof(f168,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_orders_2(X1,sK0,X0)) ) | ~spl4_17),
% 0.23/0.49    inference(avatar_component_clause,[],[f167])).
% 0.23/0.49  fof(f188,plain,(
% 0.23/0.49    ~spl4_20 | ~spl4_6 | ~spl4_7 | ~spl4_16),
% 0.23/0.49    inference(avatar_split_clause,[],[f182,f160,f93,f88,f185])).
% 0.23/0.49  fof(f185,plain,(
% 0.23/0.49    spl4_20 <=> m1_orders_2(sK2,sK0,k1_xboole_0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.23/0.49  fof(f160,plain,(
% 0.23/0.49    spl4_16 <=> ! [X1,X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,k1_xboole_0) | ~m2_orders_2(X1,sK0,X0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.23/0.49  fof(f182,plain,(
% 0.23/0.49    ~m1_orders_2(sK2,sK0,k1_xboole_0) | (~spl4_6 | ~spl4_7 | ~spl4_16)),
% 0.23/0.49    inference(resolution,[],[f181,f95])).
% 0.23/0.49  fof(f181,plain,(
% 0.23/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X0,sK0,k1_xboole_0)) ) | (~spl4_6 | ~spl4_16)),
% 0.23/0.49    inference(resolution,[],[f161,f90])).
% 0.23/0.49  fof(f161,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,k1_xboole_0) | ~m2_orders_2(X1,sK0,X0)) ) | ~spl4_16),
% 0.23/0.49    inference(avatar_component_clause,[],[f160])).
% 0.23/0.49  fof(f169,plain,(
% 0.23/0.49    spl4_17 | spl4_5 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_1),
% 0.23/0.49    inference(avatar_split_clause,[],[f165,f63,f78,f73,f68,f83,f167])).
% 0.23/0.49  fof(f165,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | ~m1_orders_2(X0,sK0,X1) | ~m1_orders_2(X1,sK0,X0)) ) | ~spl4_1),
% 0.23/0.49    inference(resolution,[],[f48,f65])).
% 0.23/0.49  fof(f48,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | ~m1_orders_2(X1,X0,X2) | ~m1_orders_2(X2,X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f25])).
% 0.23/0.49  fof(f25,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.23/0.49    inference(flattening,[],[f24])).
% 0.23/0.49  fof(f24,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f9])).
% 0.23/0.49  fof(f9,axiom,(
% 0.23/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).
% 0.23/0.49  fof(f162,plain,(
% 0.23/0.49    spl4_5 | spl4_16 | ~spl4_4 | ~spl4_2 | ~spl4_3 | ~spl4_1 | ~spl4_11),
% 0.23/0.49    inference(avatar_split_clause,[],[f158,f133,f63,f73,f68,f78,f160,f83])).
% 0.23/0.49  fof(f133,plain,(
% 0.23/0.49    spl4_11 <=> ! [X1,X0] : (~m1_orders_2(X0,sK0,k1_xboole_0) | ~r2_hidden(X1,X0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.23/0.49  fof(f158,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v3_orders_2(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | v2_struct_0(sK0) | ~m1_orders_2(X1,sK0,k1_xboole_0)) ) | (~spl4_1 | ~spl4_11)),
% 0.23/0.49    inference(resolution,[],[f157,f65])).
% 0.23/0.49  fof(f157,plain,(
% 0.23/0.49    ( ! [X4,X2,X3] : (~l1_orders_2(X2) | ~v4_orders_2(X2) | ~v5_orders_2(X2) | ~v3_orders_2(X2) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) | ~m2_orders_2(X4,X2,X3) | v2_struct_0(X2) | ~m1_orders_2(X4,sK0,k1_xboole_0)) ) | ~spl4_11),
% 0.23/0.49    inference(resolution,[],[f44,f134])).
% 0.23/0.49  fof(f134,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_orders_2(X0,sK0,k1_xboole_0)) ) | ~spl4_11),
% 0.23/0.49    inference(avatar_component_clause,[],[f133])).
% 0.23/0.49  fof(f44,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f19])).
% 0.23/0.49  fof(f19,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.23/0.49    inference(flattening,[],[f18])).
% 0.23/0.49  fof(f18,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f10])).
% 0.23/0.49  fof(f10,axiom,(
% 0.23/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).
% 0.23/0.49  fof(f150,plain,(
% 0.23/0.49    ~spl4_14 | ~spl4_6 | ~spl4_13),
% 0.23/0.49    inference(avatar_split_clause,[],[f145,f142,f88,f147])).
% 0.23/0.49  fof(f147,plain,(
% 0.23/0.49    spl4_14 <=> m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.23/0.49  fof(f142,plain,(
% 0.23/0.49    spl4_13 <=> ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.23/0.49  fof(f145,plain,(
% 0.23/0.49    ~m2_orders_2(k1_xboole_0,sK0,sK1) | (~spl4_6 | ~spl4_13)),
% 0.23/0.49    inference(resolution,[],[f143,f90])).
% 0.23/0.49  fof(f143,plain,(
% 0.23/0.49    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | ~spl4_13),
% 0.23/0.49    inference(avatar_component_clause,[],[f142])).
% 0.23/0.49  fof(f144,plain,(
% 0.23/0.49    spl4_5 | spl4_13 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_12),
% 0.23/0.49    inference(avatar_split_clause,[],[f140,f136,f78,f73,f68,f63,f142,f83])).
% 0.23/0.49  fof(f136,plain,(
% 0.23/0.49    spl4_12 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.23/0.49  fof(f140,plain,(
% 0.23/0.49    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0) | v2_struct_0(sK0)) ) | spl4_12),
% 0.23/0.49    inference(resolution,[],[f51,f138])).
% 0.23/0.49  fof(f138,plain,(
% 0.23/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_12),
% 0.23/0.49    inference(avatar_component_clause,[],[f136])).
% 0.23/0.49  fof(f139,plain,(
% 0.23/0.49    spl4_5 | spl4_11 | ~spl4_12 | ~spl4_4 | ~spl4_2 | ~spl4_3 | ~spl4_1),
% 0.23/0.49    inference(avatar_split_clause,[],[f131,f63,f73,f68,f78,f136,f133,f83])).
% 0.23/0.49  fof(f131,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v3_orders_2(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X0,sK0,k1_xboole_0) | v2_struct_0(sK0) | ~r2_hidden(X1,X0)) ) | ~spl4_1),
% 0.23/0.49    inference(resolution,[],[f126,f65])).
% 0.23/0.49  fof(f126,plain,(
% 0.23/0.49    ( ! [X10,X11,X9] : (~l1_orders_2(X9) | ~v4_orders_2(X9) | ~v5_orders_2(X9) | ~v3_orders_2(X9) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X9))) | ~m1_orders_2(X10,X9,k1_xboole_0) | v2_struct_0(X9) | ~r2_hidden(X11,X10)) )),
% 0.23/0.49    inference(resolution,[],[f47,f120])).
% 0.23/0.49  fof(f120,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 0.23/0.49    inference(resolution,[],[f112,f43])).
% 0.23/0.49  fof(f43,plain,(
% 0.23/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f4])).
% 0.23/0.49  fof(f4,axiom,(
% 0.23/0.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.23/0.49  fof(f112,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.23/0.49    inference(resolution,[],[f50,f49])).
% 0.23/0.49  fof(f49,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f26])).
% 0.23/0.49  fof(f26,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f14])).
% 0.23/0.49  fof(f14,plain,(
% 0.23/0.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.23/0.49    inference(unused_predicate_definition_removal,[],[f1])).
% 0.23/0.49  fof(f1,axiom,(
% 0.23/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.23/0.49  fof(f50,plain,(
% 0.23/0.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f28])).
% 0.23/0.49  fof(f28,plain,(
% 0.23/0.49    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.23/0.49    inference(flattening,[],[f27])).
% 0.23/0.49  fof(f27,plain,(
% 0.23/0.49    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.23/0.49    inference(ennf_transformation,[],[f5])).
% 0.23/0.49  fof(f5,axiom,(
% 0.23/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.23/0.49  fof(f111,plain,(
% 0.23/0.49    spl4_9 | spl4_10),
% 0.23/0.49    inference(avatar_split_clause,[],[f33,f107,f103])).
% 0.23/0.49  fof(f33,plain,(
% 0.23/0.49    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 0.23/0.49    inference(cnf_transformation,[],[f17])).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.23/0.49    inference(flattening,[],[f16])).
% 0.23/0.49  fof(f16,plain,(
% 0.23/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f13])).
% 0.23/0.49  fof(f13,negated_conjecture,(
% 0.23/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.23/0.49    inference(negated_conjecture,[],[f12])).
% 0.23/0.49  fof(f12,conjecture,(
% 0.23/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).
% 0.23/0.49  fof(f110,plain,(
% 0.23/0.49    ~spl4_9 | ~spl4_10),
% 0.23/0.49    inference(avatar_split_clause,[],[f34,f107,f103])).
% 0.23/0.49  fof(f34,plain,(
% 0.23/0.49    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 0.23/0.49    inference(cnf_transformation,[],[f17])).
% 0.23/0.49  fof(f101,plain,(
% 0.23/0.49    spl4_8),
% 0.23/0.49    inference(avatar_split_clause,[],[f35,f98])).
% 0.23/0.49  fof(f35,plain,(
% 0.23/0.49    m2_orders_2(sK3,sK0,sK1)),
% 0.23/0.49    inference(cnf_transformation,[],[f17])).
% 0.23/0.49  fof(f96,plain,(
% 0.23/0.49    spl4_7),
% 0.23/0.49    inference(avatar_split_clause,[],[f36,f93])).
% 0.23/0.49  fof(f36,plain,(
% 0.23/0.49    m2_orders_2(sK2,sK0,sK1)),
% 0.23/0.49    inference(cnf_transformation,[],[f17])).
% 0.23/0.49  fof(f91,plain,(
% 0.23/0.49    spl4_6),
% 0.23/0.49    inference(avatar_split_clause,[],[f37,f88])).
% 0.23/0.49  fof(f37,plain,(
% 0.23/0.49    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.23/0.49    inference(cnf_transformation,[],[f17])).
% 0.23/0.49  fof(f86,plain,(
% 0.23/0.49    ~spl4_5),
% 0.23/0.49    inference(avatar_split_clause,[],[f38,f83])).
% 0.23/0.49  fof(f38,plain,(
% 0.23/0.49    ~v2_struct_0(sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f17])).
% 0.23/0.49  fof(f81,plain,(
% 0.23/0.49    spl4_4),
% 0.23/0.49    inference(avatar_split_clause,[],[f39,f78])).
% 0.23/0.49  fof(f39,plain,(
% 0.23/0.49    v3_orders_2(sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f17])).
% 0.23/0.49  fof(f76,plain,(
% 0.23/0.49    spl4_3),
% 0.23/0.49    inference(avatar_split_clause,[],[f40,f73])).
% 0.23/0.49  fof(f40,plain,(
% 0.23/0.49    v4_orders_2(sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f17])).
% 0.23/0.49  fof(f71,plain,(
% 0.23/0.49    spl4_2),
% 0.23/0.49    inference(avatar_split_clause,[],[f41,f68])).
% 0.23/0.49  fof(f41,plain,(
% 0.23/0.49    v5_orders_2(sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f17])).
% 0.23/0.49  fof(f66,plain,(
% 0.23/0.49    spl4_1),
% 0.23/0.49    inference(avatar_split_clause,[],[f42,f63])).
% 0.23/0.49  fof(f42,plain,(
% 0.23/0.49    l1_orders_2(sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f17])).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (27319)------------------------------
% 0.23/0.49  % (27319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (27319)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (27319)Memory used [KB]: 6524
% 0.23/0.49  % (27319)Time elapsed: 0.066 s
% 0.23/0.49  % (27319)------------------------------
% 0.23/0.49  % (27319)------------------------------
% 0.23/0.49  % (27303)Success in time 0.112 s
%------------------------------------------------------------------------------
