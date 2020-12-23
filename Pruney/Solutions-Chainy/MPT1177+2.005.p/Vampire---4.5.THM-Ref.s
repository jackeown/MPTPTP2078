%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 506 expanded)
%              Number of leaves         :   47 ( 226 expanded)
%              Depth                    :   11
%              Number of atoms          : 1076 (2823 expanded)
%              Number of equality atoms :   49 (  80 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f448,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f90,f95,f100,f105,f110,f115,f120,f129,f131,f199,f204,f208,f220,f224,f229,f271,f275,f281,f293,f302,f318,f322,f335,f342,f366,f368,f385,f399,f403,f408,f445,f447])).

fof(f447,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_20
    | ~ spl6_38
    | spl6_40 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_20
    | ~ spl6_38
    | spl6_40 ),
    inference(unit_resulting_resolution,[],[f84,f89,f94,f99,f104,f407,f407,f219,f439,f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X2,X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f63,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_2(X2,X0,X1)
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

fof(f439,plain,
    ( k1_xboole_0 != sK2
    | spl6_40 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl6_40
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f219,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl6_20
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f407,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl6_38
  <=> m1_orders_2(sK2,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f104,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f99,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f94,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f89,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl6_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f84,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f445,plain,
    ( k1_xboole_0 != sK2
    | sK2 != sK3
    | m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ m2_orders_2(sK3,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f408,plain,
    ( spl6_38
    | spl6_9
    | ~ spl6_10
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f394,f332,f126,f122,f405])).

fof(f122,plain,
    ( spl6_9
  <=> r2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f126,plain,
    ( spl6_10
  <=> m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f332,plain,
    ( spl6_35
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f394,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | spl6_9
    | ~ spl6_10
    | ~ spl6_35 ),
    inference(backward_demodulation,[],[f128,f388])).

fof(f388,plain,
    ( sK2 = sK3
    | spl6_9
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f386,f123])).

fof(f123,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f386,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK2,sK3)
    | ~ spl6_35 ),
    inference(resolution,[],[f334,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f334,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f332])).

fof(f128,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f403,plain,
    ( sK2 != sK3
    | m1_orders_2(sK2,sK0,sK3)
    | ~ m1_orders_2(sK3,sK0,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f399,plain,
    ( spl6_30
    | spl6_9
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f388,f332,f122,f307])).

fof(f307,plain,
    ( spl6_30
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f385,plain,
    ( ~ spl6_24
    | ~ spl6_31
    | spl6_36 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | ~ spl6_24
    | ~ spl6_31
    | spl6_36 ),
    inference(subsumption_resolution,[],[f380,f341])).

fof(f341,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl6_36 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl6_36
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f380,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl6_24
    | ~ spl6_31 ),
    inference(resolution,[],[f312,f274])).

fof(f274,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl6_24
  <=> ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f312,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl6_31
  <=> m1_orders_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f368,plain,
    ( ~ spl6_7
    | ~ spl6_9
    | spl6_10
    | spl6_31
    | ~ spl6_33 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_9
    | spl6_10
    | spl6_31
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f356,f80])).

fof(f80,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f356,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ spl6_7
    | ~ spl6_9
    | spl6_10
    | spl6_31
    | ~ spl6_33 ),
    inference(backward_demodulation,[],[f124,f349])).

fof(f349,plain,
    ( sK2 = sK3
    | ~ spl6_7
    | spl6_10
    | spl6_31
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f336,f127])).

fof(f127,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f336,plain,
    ( sK2 = sK3
    | m1_orders_2(sK2,sK0,sK3)
    | ~ spl6_7
    | spl6_31
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f329,f313])).

fof(f313,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | spl6_31 ),
    inference(avatar_component_clause,[],[f311])).

fof(f329,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3)
    | ~ spl6_7
    | ~ spl6_33 ),
    inference(resolution,[],[f321,f114])).

fof(f114,plain,
    ( m2_orders_2(sK3,sK0,sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_7
  <=> m2_orders_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f321,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | sK2 = X0
        | m1_orders_2(X0,sK0,sK2)
        | m1_orders_2(sK2,sK0,X0) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl6_33
  <=> ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | sK2 = X0
        | m1_orders_2(X0,sK0,sK2)
        | m1_orders_2(sK2,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f124,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f366,plain,
    ( spl6_30
    | ~ spl6_7
    | spl6_10
    | spl6_31
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f349,f320,f311,f126,f112,f307])).

fof(f342,plain,
    ( ~ spl6_36
    | spl6_30
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f337,f122,f307,f339])).

fof(f337,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK3,sK2)
    | ~ spl6_9 ),
    inference(resolution,[],[f124,f135])).

fof(f135,plain,(
    ! [X2,X1] :
      ( ~ r2_xboole_0(X2,X1)
      | X1 = X2
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f74,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f335,plain,
    ( spl6_35
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f327,f316,f126,f332])).

fof(f316,plain,
    ( spl6_32
  <=> ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f327,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(resolution,[],[f317,f128])).

fof(f317,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3) )
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f316])).

fof(f322,plain,
    ( spl6_33
    | ~ spl6_6
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f303,f291,f107,f320])).

fof(f107,plain,
    ( spl6_6
  <=> m2_orders_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f291,plain,
    ( spl6_28
  <=> ! [X1,X0] :
        ( X0 = X1
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f303,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | sK2 = X0
        | m1_orders_2(X0,sK0,sK2)
        | m1_orders_2(sK2,sK0,X0) )
    | ~ spl6_6
    | ~ spl6_28 ),
    inference(resolution,[],[f292,f109])).

fof(f109,plain,
    ( m2_orders_2(sK2,sK0,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f292,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | ~ m2_orders_2(X0,sK0,sK1)
        | X0 = X1
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f291])).

fof(f318,plain,
    ( spl6_32
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f267,f226,f102,f97,f92,f87,f82,f316])).

fof(f226,plain,
    ( spl6_22
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f267,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f266,f84])).

fof(f266,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f265,f89])).

fof(f265,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f264,f94])).

fof(f264,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f263,f99])).

fof(f263,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f252,f104])).

fof(f252,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_22 ),
    inference(resolution,[],[f228,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | r1_tarski(X2,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

fof(f228,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f226])).

fof(f302,plain,
    ( ~ spl6_29
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f294,f279,f299])).

fof(f299,plain,
    ( spl6_29
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f279,plain,
    ( spl6_25
  <=> ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ r1_xboole_0(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f294,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl6_25 ),
    inference(resolution,[],[f280,f137])).

fof(f137,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f133,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f133,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f68,f58])).

fof(f58,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f280,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | ~ m2_orders_2(X0,sK0,sK1) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f279])).

fof(f293,plain,
    ( spl6_28
    | ~ spl6_8
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f249,f222,f117,f291])).

fof(f117,plain,
    ( spl6_8
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f222,plain,
    ( spl6_21
  <=> ! [X1,X0,X2] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( X0 = X1
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) )
    | ~ spl6_8
    | ~ spl6_21 ),
    inference(resolution,[],[f223,f119])).

fof(f119,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f223,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f222])).

fof(f281,plain,
    ( spl6_25
    | ~ spl6_6
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f276,f269,f107,f279])).

fof(f269,plain,
    ( spl6_23
  <=> ! [X1,X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f276,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ r1_xboole_0(X0,sK2) )
    | ~ spl6_6
    | ~ spl6_23 ),
    inference(resolution,[],[f270,f109])).

fof(f270,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f269])).

fof(f275,plain,
    ( spl6_24
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f248,f217,f102,f97,f92,f87,f82,f273])).

fof(f248,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f247,f84])).

fof(f247,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f246,f89])).

fof(f246,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f245,f94])).

fof(f245,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f244,f99])).

fof(f244,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_5
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f233,f104])).

fof(f233,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_20 ),
    inference(resolution,[],[f219,f62])).

fof(f271,plain,
    ( spl6_23
    | ~ spl6_8
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f209,f202,f117,f269])).

fof(f202,plain,
    ( spl6_17
  <=> ! [X1,X0,X2] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m2_orders_2(X2,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_8
    | ~ spl6_17 ),
    inference(resolution,[],[f203,f119])).

fof(f203,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X2,sK0,X1)
        | ~ m2_orders_2(X0,sK0,X1)
        | ~ r1_xboole_0(X2,X0) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f202])).

fof(f229,plain,
    ( spl6_22
    | ~ spl6_7
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f211,f206,f112,f226])).

fof(f206,plain,
    ( spl6_18
  <=> ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f211,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_7
    | ~ spl6_18 ),
    inference(resolution,[],[f207,f114])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f206])).

fof(f224,plain,
    ( spl6_21
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f190,f102,f97,f92,f87,f82,f222])).

fof(f190,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f189,f84])).

fof(f189,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f188,f89])).

fof(f188,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f187,f94])).

fof(f187,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f186,f99])).

fof(f186,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f61,f104])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m1_orders_2(X2,X0,X3)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_orders_2(X2,X0,X3)
                      | m1_orders_2(X3,X0,X2) )
                    & ( ~ m1_orders_2(X3,X0,X2)
                      | ~ m1_orders_2(X2,X0,X3) ) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).

fof(f220,plain,
    ( spl6_20
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f210,f206,f107,f217])).

fof(f210,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(resolution,[],[f207,f109])).

fof(f208,plain,
    ( spl6_18
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f200,f197,f117,f206])).

fof(f197,plain,
    ( spl6_16
  <=> ! [X1,X0] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(resolution,[],[f198,f119])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X0,sK0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f197])).

fof(f204,plain,
    ( spl6_17
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f167,f102,f97,f92,f87,f82,f202])).

fof(f167,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m2_orders_2(X2,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X2,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f166,f84])).

fof(f166,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m2_orders_2(X2,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X2,X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f165,f89])).

fof(f165,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m2_orders_2(X2,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X2,X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f164,f94])).

fof(f164,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m2_orders_2(X2,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X2,X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f163,f99])).

fof(f163,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m2_orders_2(X2,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X2,X0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f59,f104])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

fof(f199,plain,
    ( spl6_16
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f158,f102,f97,f92,f87,f82,f197])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f157,f84])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f156,f89])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f155,f94])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f154,f99])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f70,f104])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f131,plain,
    ( ~ spl6_9
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f130,f126,f122])).

fof(f130,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f57,f128])).

fof(f57,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ m1_orders_2(sK2,sK0,sK3)
      | ~ r2_xboole_0(sK2,sK3) )
    & ( m1_orders_2(sK2,sK0,sK3)
      | r2_xboole_0(sK2,sK3) )
    & m2_orders_2(sK3,sK0,sK1)
    & m2_orders_2(sK2,sK0,sK1)
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f35,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_orders_2(X2,X0,X3)
                      | ~ r2_xboole_0(X2,X3) )
                    & ( m1_orders_2(X2,X0,X3)
                      | r2_xboole_0(X2,X3) )
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,sK0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,sK0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,sK0,X1) )
              & m2_orders_2(X2,sK0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_orders_2(X2,sK0,X3)
                  | ~ r2_xboole_0(X2,X3) )
                & ( m1_orders_2(X2,sK0,X3)
                  | r2_xboole_0(X2,X3) )
                & m2_orders_2(X3,sK0,X1) )
            & m2_orders_2(X2,sK0,X1) )
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_orders_2(X2,sK0,X3)
                | ~ r2_xboole_0(X2,X3) )
              & ( m1_orders_2(X2,sK0,X3)
                | r2_xboole_0(X2,X3) )
              & m2_orders_2(X3,sK0,sK1) )
          & m2_orders_2(X2,sK0,sK1) )
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_orders_2(X2,sK0,X3)
              | ~ r2_xboole_0(X2,X3) )
            & ( m1_orders_2(X2,sK0,X3)
              | r2_xboole_0(X2,X3) )
            & m2_orders_2(X3,sK0,sK1) )
        & m2_orders_2(X2,sK0,sK1) )
   => ( ? [X3] :
          ( ( ~ m1_orders_2(sK2,sK0,X3)
            | ~ r2_xboole_0(sK2,X3) )
          & ( m1_orders_2(sK2,sK0,X3)
            | r2_xboole_0(sK2,X3) )
          & m2_orders_2(X3,sK0,sK1) )
      & m2_orders_2(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X3] :
        ( ( ~ m1_orders_2(sK2,sK0,X3)
          | ~ r2_xboole_0(sK2,X3) )
        & ( m1_orders_2(sK2,sK0,X3)
          | r2_xboole_0(sK2,X3) )
        & m2_orders_2(X3,sK0,sK1) )
   => ( ( ~ m1_orders_2(sK2,sK0,sK3)
        | ~ r2_xboole_0(sK2,sK3) )
      & ( m1_orders_2(sK2,sK0,sK3)
        | r2_xboole_0(sK2,sK3) )
      & m2_orders_2(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).

fof(f129,plain,
    ( spl6_9
    | spl6_10 ),
    inference(avatar_split_clause,[],[f56,f126,f122])).

fof(f56,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f120,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f53,f117])).

fof(f53,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f115,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f55,f112])).

fof(f55,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f110,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f54,f107])).

fof(f54,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f105,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f52,f102])).

fof(f52,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f100,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f51,f97])).

fof(f51,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f50,f92])).

fof(f50,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f49,f87])).

fof(f49,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f48,f82])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:24:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (14653)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.48  % (14653)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (14665)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f448,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f85,f90,f95,f100,f105,f110,f115,f120,f129,f131,f199,f204,f208,f220,f224,f229,f271,f275,f281,f293,f302,f318,f322,f335,f342,f366,f368,f385,f399,f403,f408,f445,f447])).
% 0.21/0.50  fof(f447,plain,(
% 0.21/0.50    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_20 | ~spl6_38 | spl6_40),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f446])).
% 0.21/0.50  fof(f446,plain,(
% 0.21/0.50    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_20 | ~spl6_38 | spl6_40)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f84,f89,f94,f99,f104,f407,f407,f219,f439,f169])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_orders_2(X2,X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f63,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).
% 0.21/0.50  fof(f439,plain,(
% 0.21/0.50    k1_xboole_0 != sK2 | spl6_40),
% 0.21/0.50    inference(avatar_component_clause,[],[f438])).
% 0.21/0.50  fof(f438,plain,(
% 0.21/0.50    spl6_40 <=> k1_xboole_0 = sK2),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f217])).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    spl6_20 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.50  fof(f407,plain,(
% 0.21/0.50    m1_orders_2(sK2,sK0,sK2) | ~spl6_38),
% 0.21/0.50    inference(avatar_component_clause,[],[f405])).
% 0.21/0.50  fof(f405,plain,(
% 0.21/0.50    spl6_38 <=> m1_orders_2(sK2,sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    l1_orders_2(sK0) | ~spl6_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl6_5 <=> l1_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    v5_orders_2(sK0) | ~spl6_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl6_4 <=> v5_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    v4_orders_2(sK0) | ~spl6_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl6_3 <=> v4_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    v3_orders_2(sK0) | ~spl6_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl6_2 <=> v3_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ~v2_struct_0(sK0) | spl6_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    spl6_1 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.50  fof(f445,plain,(
% 0.21/0.50    k1_xboole_0 != sK2 | sK2 != sK3 | m2_orders_2(k1_xboole_0,sK0,sK1) | ~m2_orders_2(sK3,sK0,sK1)),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f408,plain,(
% 0.21/0.50    spl6_38 | spl6_9 | ~spl6_10 | ~spl6_35),
% 0.21/0.50    inference(avatar_split_clause,[],[f394,f332,f126,f122,f405])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl6_9 <=> r2_xboole_0(sK2,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl6_10 <=> m1_orders_2(sK2,sK0,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.50  fof(f332,plain,(
% 0.21/0.50    spl6_35 <=> r1_tarski(sK2,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.21/0.50  fof(f394,plain,(
% 0.21/0.50    m1_orders_2(sK2,sK0,sK2) | (spl6_9 | ~spl6_10 | ~spl6_35)),
% 0.21/0.50    inference(backward_demodulation,[],[f128,f388])).
% 0.21/0.50  fof(f388,plain,(
% 0.21/0.50    sK2 = sK3 | (spl6_9 | ~spl6_35)),
% 0.21/0.50    inference(subsumption_resolution,[],[f386,f123])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ~r2_xboole_0(sK2,sK3) | spl6_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f122])).
% 0.21/0.50  fof(f386,plain,(
% 0.21/0.50    sK2 = sK3 | r2_xboole_0(sK2,sK3) | ~spl6_35),
% 0.21/0.50    inference(resolution,[],[f334,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.50    inference(flattening,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.50  fof(f334,plain,(
% 0.21/0.50    r1_tarski(sK2,sK3) | ~spl6_35),
% 0.21/0.50    inference(avatar_component_clause,[],[f332])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    m1_orders_2(sK2,sK0,sK3) | ~spl6_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f126])).
% 0.21/0.50  fof(f403,plain,(
% 0.21/0.50    sK2 != sK3 | m1_orders_2(sK2,sK0,sK3) | ~m1_orders_2(sK3,sK0,sK2)),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f399,plain,(
% 0.21/0.50    spl6_30 | spl6_9 | ~spl6_35),
% 0.21/0.50    inference(avatar_split_clause,[],[f388,f332,f122,f307])).
% 0.21/0.50  fof(f307,plain,(
% 0.21/0.50    spl6_30 <=> sK2 = sK3),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.50  fof(f385,plain,(
% 0.21/0.50    ~spl6_24 | ~spl6_31 | spl6_36),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f384])).
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    $false | (~spl6_24 | ~spl6_31 | spl6_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f380,f341])).
% 0.21/0.50  fof(f341,plain,(
% 0.21/0.50    ~r1_tarski(sK3,sK2) | spl6_36),
% 0.21/0.50    inference(avatar_component_clause,[],[f339])).
% 0.21/0.50  fof(f339,plain,(
% 0.21/0.50    spl6_36 <=> r1_tarski(sK3,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.50  fof(f380,plain,(
% 0.21/0.50    r1_tarski(sK3,sK2) | (~spl6_24 | ~spl6_31)),
% 0.21/0.50    inference(resolution,[],[f312,f274])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2)) ) | ~spl6_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f273])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    spl6_24 <=> ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.50  fof(f312,plain,(
% 0.21/0.50    m1_orders_2(sK3,sK0,sK2) | ~spl6_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f311])).
% 0.21/0.50  fof(f311,plain,(
% 0.21/0.50    spl6_31 <=> m1_orders_2(sK3,sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.50  fof(f368,plain,(
% 0.21/0.50    ~spl6_7 | ~spl6_9 | spl6_10 | spl6_31 | ~spl6_33),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f367])).
% 0.21/0.50  fof(f367,plain,(
% 0.21/0.50    $false | (~spl6_7 | ~spl6_9 | spl6_10 | spl6_31 | ~spl6_33)),
% 0.21/0.50    inference(subsumption_resolution,[],[f356,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f356,plain,(
% 0.21/0.50    r2_xboole_0(sK2,sK2) | (~spl6_7 | ~spl6_9 | spl6_10 | spl6_31 | ~spl6_33)),
% 0.21/0.50    inference(backward_demodulation,[],[f124,f349])).
% 0.21/0.50  fof(f349,plain,(
% 0.21/0.50    sK2 = sK3 | (~spl6_7 | spl6_10 | spl6_31 | ~spl6_33)),
% 0.21/0.50    inference(subsumption_resolution,[],[f336,f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ~m1_orders_2(sK2,sK0,sK3) | spl6_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f126])).
% 0.21/0.50  fof(f336,plain,(
% 0.21/0.50    sK2 = sK3 | m1_orders_2(sK2,sK0,sK3) | (~spl6_7 | spl6_31 | ~spl6_33)),
% 0.21/0.50    inference(subsumption_resolution,[],[f329,f313])).
% 0.21/0.50  fof(f313,plain,(
% 0.21/0.50    ~m1_orders_2(sK3,sK0,sK2) | spl6_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f311])).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    sK2 = sK3 | m1_orders_2(sK3,sK0,sK2) | m1_orders_2(sK2,sK0,sK3) | (~spl6_7 | ~spl6_33)),
% 0.21/0.50    inference(resolution,[],[f321,f114])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    m2_orders_2(sK3,sK0,sK1) | ~spl6_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f112])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    spl6_7 <=> m2_orders_2(sK3,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.50  fof(f321,plain,(
% 0.21/0.50    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | m1_orders_2(sK2,sK0,X0)) ) | ~spl6_33),
% 0.21/0.50    inference(avatar_component_clause,[],[f320])).
% 0.21/0.50  fof(f320,plain,(
% 0.21/0.50    spl6_33 <=> ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | m1_orders_2(sK2,sK0,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    r2_xboole_0(sK2,sK3) | ~spl6_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f122])).
% 0.21/0.50  fof(f366,plain,(
% 0.21/0.50    spl6_30 | ~spl6_7 | spl6_10 | spl6_31 | ~spl6_33),
% 0.21/0.50    inference(avatar_split_clause,[],[f349,f320,f311,f126,f112,f307])).
% 0.21/0.50  fof(f342,plain,(
% 0.21/0.50    ~spl6_36 | spl6_30 | ~spl6_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f337,f122,f307,f339])).
% 0.21/0.50  fof(f337,plain,(
% 0.21/0.50    sK2 = sK3 | ~r1_tarski(sK3,sK2) | ~spl6_9),
% 0.21/0.50    inference(resolution,[],[f124,f135])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r2_xboole_0(X2,X1) | X1 = X2 | ~r1_tarski(X1,X2)) )),
% 0.21/0.50    inference(resolution,[],[f74,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f335,plain,(
% 0.21/0.50    spl6_35 | ~spl6_10 | ~spl6_32),
% 0.21/0.50    inference(avatar_split_clause,[],[f327,f316,f126,f332])).
% 0.21/0.50  fof(f316,plain,(
% 0.21/0.50    spl6_32 <=> ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    r1_tarski(sK2,sK3) | (~spl6_10 | ~spl6_32)),
% 0.21/0.50    inference(resolution,[],[f317,f128])).
% 0.21/0.50  fof(f317,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3)) ) | ~spl6_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f316])).
% 0.21/0.50  fof(f322,plain,(
% 0.21/0.50    spl6_33 | ~spl6_6 | ~spl6_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f303,f291,f107,f320])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    spl6_6 <=> m2_orders_2(sK2,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    spl6_28 <=> ! [X1,X0] : (X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | m1_orders_2(sK2,sK0,X0)) ) | (~spl6_6 | ~spl6_28)),
% 0.21/0.50    inference(resolution,[],[f292,f109])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    m2_orders_2(sK2,sK0,sK1) | ~spl6_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f107])).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | X0 = X1 | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) ) | ~spl6_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f291])).
% 0.21/0.50  fof(f318,plain,(
% 0.21/0.50    spl6_32 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f267,f226,f102,f97,f92,f87,f82,f316])).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    spl6_22 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f266,f84])).
% 0.21/0.50  fof(f266,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f265,f89])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f264,f94])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f263,f99])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_5 | ~spl6_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f252,f104])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_22),
% 0.21/0.50    inference(resolution,[],[f228,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f226])).
% 0.21/0.50  fof(f302,plain,(
% 0.21/0.50    ~spl6_29 | ~spl6_25),
% 0.21/0.50    inference(avatar_split_clause,[],[f294,f279,f299])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    spl6_29 <=> m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.50  fof(f279,plain,(
% 0.21/0.50    spl6_25 <=> ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(X0,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    ~m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl6_25),
% 0.21/0.50    inference(resolution,[],[f280,f137])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(resolution,[],[f133,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(condensation,[],[f132])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f68,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f280,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~m2_orders_2(X0,sK0,sK1)) ) | ~spl6_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f279])).
% 0.21/0.50  fof(f293,plain,(
% 0.21/0.50    spl6_28 | ~spl6_8 | ~spl6_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f249,f222,f117,f291])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl6_8 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    spl6_21 <=> ! [X1,X0,X2] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    ( ! [X0,X1] : (X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) ) | (~spl6_8 | ~spl6_21)),
% 0.21/0.50    inference(resolution,[],[f223,f119])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl6_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f117])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) ) | ~spl6_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f222])).
% 0.21/0.50  fof(f281,plain,(
% 0.21/0.50    spl6_25 | ~spl6_6 | ~spl6_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f276,f269,f107,f279])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    spl6_23 <=> ! [X1,X0] : (~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(X0,sK2)) ) | (~spl6_6 | ~spl6_23)),
% 0.21/0.50    inference(resolution,[],[f270,f109])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(X0,X1)) ) | ~spl6_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f269])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    spl6_24 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f248,f217,f102,f97,f92,f87,f82,f273])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f247,f84])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f246,f89])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f245,f94])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f244,f99])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_5 | ~spl6_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f233,f104])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_20),
% 0.21/0.50    inference(resolution,[],[f219,f62])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    spl6_23 | ~spl6_8 | ~spl6_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f209,f202,f117,f269])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    spl6_17 <=> ! [X1,X0,X2] : (~m2_orders_2(X0,sK0,X1) | ~m2_orders_2(X2,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~r1_xboole_0(X2,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X0,X1)) ) | (~spl6_8 | ~spl6_17)),
% 0.21/0.50    inference(resolution,[],[f203,f119])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X2,sK0,X1) | ~m2_orders_2(X0,sK0,X1) | ~r1_xboole_0(X2,X0)) ) | ~spl6_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f202])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    spl6_22 | ~spl6_7 | ~spl6_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f211,f206,f112,f226])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    spl6_18 <=> ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_7 | ~spl6_18)),
% 0.21/0.50    inference(resolution,[],[f207,f114])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f206])).
% 0.21/0.50  fof(f224,plain,(
% 0.21/0.50    spl6_21 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f190,f102,f97,f92,f87,f82,f222])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f189,f84])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f188,f89])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_4 | ~spl6_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f187,f94])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_4 | ~spl6_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f186,f99])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_5),
% 0.21/0.50    inference(resolution,[],[f61,f104])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_orders_2(X2,X0,X3) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    spl6_20 | ~spl6_6 | ~spl6_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f210,f206,f107,f217])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_6 | ~spl6_18)),
% 0.21/0.50    inference(resolution,[],[f207,f109])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    spl6_18 | ~spl6_8 | ~spl6_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f200,f197,f117,f206])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    spl6_16 <=> ! [X1,X0] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl6_8 | ~spl6_16)),
% 0.21/0.50    inference(resolution,[],[f198,f119])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,X1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f197])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    spl6_17 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f167,f102,f97,f92,f87,f82,f202])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m2_orders_2(X2,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~r1_xboole_0(X2,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f166,f84])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m2_orders_2(X2,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~r1_xboole_0(X2,X0) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f165,f89])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m2_orders_2(X2,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~r1_xboole_0(X2,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_4 | ~spl6_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f164,f94])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m2_orders_2(X2,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~r1_xboole_0(X2,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_4 | ~spl6_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f163,f99])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m2_orders_2(X2,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~r1_xboole_0(X2,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_5),
% 0.21/0.50    inference(resolution,[],[f59,f104])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~r1_xboole_0(X2,X3) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    spl6_16 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f158,f102,f97,f92,f87,f82,f197])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f157,f84])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f156,f89])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_4 | ~spl6_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f155,f94])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_4 | ~spl6_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f154,f99])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_5),
% 0.21/0.50    inference(resolution,[],[f70,f104])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ~spl6_9 | ~spl6_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f130,f126,f122])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    ~r2_xboole_0(sK2,sK3) | ~spl6_10),
% 0.21/0.50    inference(subsumption_resolution,[],[f57,f128])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f35,f34,f33,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) => (? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) => ((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f12])).
% 0.21/0.50  fof(f12,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    spl6_9 | spl6_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f126,f122])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl6_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f117])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl6_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f112])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    m2_orders_2(sK3,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl6_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f107])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    m2_orders_2(sK2,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl6_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f102])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    l1_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl6_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f97])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    v5_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    spl6_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f92])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    v4_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl6_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f87])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    v3_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ~spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f82])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (14653)------------------------------
% 0.21/0.50  % (14653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14653)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (14653)Memory used [KB]: 6396
% 0.21/0.50  % (14653)Time elapsed: 0.073 s
% 0.21/0.50  % (14653)------------------------------
% 0.21/0.50  % (14653)------------------------------
% 0.21/0.51  % (14649)Success in time 0.146 s
%------------------------------------------------------------------------------
