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
% DateTime   : Thu Dec  3 13:10:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  223 ( 491 expanded)
%              Number of leaves         :   48 ( 214 expanded)
%              Depth                    :   12
%              Number of atoms          : 1066 (2716 expanded)
%              Number of equality atoms :   71 (  99 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f562,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f102,f107,f112,f117,f128,f130,f201,f227,f231,f240,f249,f302,f333,f352,f365,f376,f380,f386,f400,f423,f441,f460,f465,f504,f511,f530,f561])).

fof(f561,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_33
    | ~ spl4_46 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_33
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f81,f86,f91,f96,f101,f356,f529,f116,f529,f55])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f116,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_8
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f529,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f527])).

fof(f527,plain,
    ( spl4_46
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f356,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl4_33
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f101,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f96,plain,
    ( v5_orders_2(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f91,plain,
    ( v4_orders_2(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f86,plain,
    ( v3_orders_2(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f81,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f530,plain,
    ( spl4_46
    | ~ spl4_6
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f513,f498,f104,f527])).

fof(f104,plain,
    ( spl4_6
  <=> m2_orders_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f498,plain,
    ( spl4_44
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f513,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl4_6
    | ~ spl4_44 ),
    inference(backward_demodulation,[],[f106,f500])).

fof(f500,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f498])).

fof(f106,plain,
    ( m2_orders_2(sK2,sK0,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f511,plain,
    ( ~ spl4_41
    | ~ spl4_45 ),
    inference(avatar_contradiction_clause,[],[f510])).

fof(f510,plain,
    ( $false
    | ~ spl4_41
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f508,f464])).

fof(f464,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f462])).

fof(f462,plain,
    ( spl4_41
  <=> m1_orders_2(sK2,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f508,plain,
    ( ~ m1_orders_2(sK2,sK0,sK2)
    | ~ spl4_41
    | ~ spl4_45 ),
    inference(resolution,[],[f503,f464])).

fof(f503,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | ~ m1_orders_2(X0,sK0,sK2) )
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f502])).

fof(f502,plain,
    ( spl4_45
  <=> ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | ~ m1_orders_2(X0,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f504,plain,
    ( spl4_44
    | spl4_45
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f259,f237,f99,f94,f89,f84,f79,f502,f498])).

fof(f237,plain,
    ( spl4_20
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | k1_xboole_0 = sK2
        | ~ m1_orders_2(X0,sK0,sK2) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f258,f81])).

fof(f258,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | k1_xboole_0 = sK2
        | ~ m1_orders_2(X0,sK0,sK2)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f257,f86])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | k1_xboole_0 = sK2
        | ~ m1_orders_2(X0,sK0,sK2)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f256,f91])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | k1_xboole_0 = sK2
        | ~ m1_orders_2(X0,sK0,sK2)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f255,f96])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | k1_xboole_0 = sK2
        | ~ m1_orders_2(X0,sK0,sK2)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f252,f101])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | k1_xboole_0 = sK2
        | ~ m1_orders_2(X0,sK0,sK2)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_20 ),
    inference(resolution,[],[f239,f176])).

fof(f176,plain,(
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
    inference(subsumption_resolution,[],[f59,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f239,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f237])).

fof(f465,plain,
    ( spl4_41
    | spl4_9
    | ~ spl4_10
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f450,f383,f125,f121,f462])).

fof(f121,plain,
    ( spl4_9
  <=> r2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f125,plain,
    ( spl4_10
  <=> m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f383,plain,
    ( spl4_37
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f450,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | spl4_9
    | ~ spl4_10
    | ~ spl4_37 ),
    inference(backward_demodulation,[],[f127,f447])).

fof(f447,plain,
    ( sK2 = sK3
    | spl4_9
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f445,f122])).

fof(f122,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f445,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK2,sK3)
    | ~ spl4_37 ),
    inference(resolution,[],[f385,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f385,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f383])).

fof(f127,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f460,plain,
    ( sK2 != sK3
    | m1_orders_2(sK2,sK0,sK3)
    | ~ m1_orders_2(sK3,sK0,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f441,plain,
    ( ~ spl4_29
    | ~ spl4_35
    | spl4_39 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | ~ spl4_29
    | ~ spl4_35
    | spl4_39 ),
    inference(subsumption_resolution,[],[f436,f399])).

fof(f399,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl4_39 ),
    inference(avatar_component_clause,[],[f397])).

fof(f397,plain,
    ( spl4_39
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f436,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl4_29
    | ~ spl4_35 ),
    inference(resolution,[],[f325,f375])).

fof(f375,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl4_35
  <=> ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f325,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl4_29
  <=> m1_orders_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f423,plain,
    ( ~ spl4_6
    | ~ spl4_9
    | spl4_10
    | spl4_29
    | ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_9
    | spl4_10
    | spl4_29
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f409,f77])).

fof(f77,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f409,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ spl4_6
    | ~ spl4_9
    | spl4_10
    | spl4_29
    | ~ spl4_32 ),
    inference(backward_demodulation,[],[f123,f407])).

fof(f407,plain,
    ( sK2 = sK3
    | ~ spl4_6
    | spl4_10
    | spl4_29
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f387,f126])).

fof(f126,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f387,plain,
    ( sK2 = sK3
    | m1_orders_2(sK2,sK0,sK3)
    | ~ spl4_6
    | spl4_29
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f362,f326])).

fof(f326,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f324])).

fof(f362,plain,
    ( sK2 = sK3
    | m1_orders_2(sK2,sK0,sK3)
    | m1_orders_2(sK3,sK0,sK2)
    | ~ spl4_6
    | ~ spl4_32 ),
    inference(resolution,[],[f351,f106])).

fof(f351,plain,
    ( ! [X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | sK3 = X1
        | m1_orders_2(X1,sK0,sK3)
        | m1_orders_2(sK3,sK0,X1) )
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl4_32
  <=> ! [X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | sK3 = X1
        | m1_orders_2(X1,sK0,sK3)
        | m1_orders_2(sK3,sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f123,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f400,plain,
    ( ~ spl4_39
    | spl4_28
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f389,f121,f320,f397])).

fof(f320,plain,
    ( spl4_28
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f389,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK3,sK2)
    | ~ spl4_9 ),
    inference(resolution,[],[f123,f141])).

fof(f141,plain,(
    ! [X4,X3] :
      ( ~ r2_xboole_0(X4,X3)
      | X3 = X4
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f68,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f386,plain,
    ( spl4_37
    | ~ spl4_10
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f381,f378,f125,f383])).

fof(f378,plain,
    ( spl4_36
  <=> ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f381,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_10
    | ~ spl4_36 ),
    inference(resolution,[],[f379,f127])).

fof(f379,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f378])).

fof(f380,plain,
    ( spl4_36
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f290,f246,f99,f94,f89,f84,f79,f378])).

fof(f246,plain,
    ( spl4_22
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f290,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f289,f81])).

fof(f289,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f288,f86])).

fof(f288,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f287,f91])).

fof(f287,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f286,f96])).

fof(f286,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f275,f101])).

fof(f275,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_22 ),
    inference(resolution,[],[f248,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | r1_tarski(X2,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f248,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f246])).

fof(f376,plain,
    ( spl4_35
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f269,f237,f99,f94,f89,f84,f79,f374])).

fof(f269,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f268,f81])).

fof(f268,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f267,f86])).

fof(f267,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f266,f91])).

fof(f266,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f265,f96])).

fof(f265,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f254,f101])).

fof(f254,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_20 ),
    inference(resolution,[],[f239,f58])).

fof(f365,plain,
    ( spl4_33
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f348,f330,f354])).

fof(f330,plain,
    ( spl4_30
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f348,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_30 ),
    inference(trivial_inequality_removal,[],[f340])).

fof(f340,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_30 ),
    inference(superposition,[],[f73,f332])).

fof(f332,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f330])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f352,plain,
    ( spl4_32
    | ~ spl4_7
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f312,f300,f109,f350])).

fof(f109,plain,
    ( spl4_7
  <=> m2_orders_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f300,plain,
    ( spl4_25
  <=> ! [X1,X0] :
        ( X0 = X1
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f312,plain,
    ( ! [X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | sK3 = X1
        | m1_orders_2(X1,sK0,sK3)
        | m1_orders_2(sK3,sK0,X1) )
    | ~ spl4_7
    | ~ spl4_25 ),
    inference(resolution,[],[f301,f111])).

fof(f111,plain,
    ( m2_orders_2(sK3,sK0,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f301,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | ~ m2_orders_2(X0,sK0,sK1)
        | X0 = X1
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f300])).

fof(f333,plain,(
    spl4_30 ),
    inference(avatar_split_clause,[],[f328,f330])).

fof(f328,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f272])).

fof(f272,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k4_xboole_0(X0,X0) = X0 ) ),
    inference(superposition,[],[f172,f132])).

fof(f132,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    inference(resolution,[],[f72,f118])).

fof(f118,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f62,f61])).

fof(f61,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f172,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(X2,k4_xboole_0(X2,X3))
      | k4_xboole_0(X2,X3) = X2 ) ),
    inference(resolution,[],[f143,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | k4_xboole_0(X1,X0) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) != k1_xboole_0
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( k4_xboole_0(X1,X0) = k1_xboole_0
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

fof(f143,plain,(
    ! [X2,X1] :
      ( r2_xboole_0(k4_xboole_0(X1,X2),X1)
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f71,f60])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f302,plain,
    ( spl4_25
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f235,f225,f114,f300])).

fof(f225,plain,
    ( spl4_18
  <=> ! [X1,X0,X2] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( X0 = X1
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) )
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(resolution,[],[f226,f116])).

fof(f226,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f225])).

fof(f249,plain,
    ( spl4_22
    | ~ spl4_7
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f234,f229,f109,f246])).

fof(f229,plain,
    ( spl4_19
  <=> ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f234,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_7
    | ~ spl4_19 ),
    inference(resolution,[],[f230,f111])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f229])).

fof(f240,plain,
    ( spl4_20
    | ~ spl4_6
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f233,f229,f104,f237])).

fof(f233,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6
    | ~ spl4_19 ),
    inference(resolution,[],[f230,f106])).

fof(f231,plain,
    ( spl4_19
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f204,f199,f114,f229])).

fof(f199,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(resolution,[],[f200,f116])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X0,sK0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f199])).

fof(f227,plain,
    ( spl4_18
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f193,f99,f94,f89,f84,f79,f225])).

fof(f193,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f192,f81])).

fof(f192,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f191,f86])).

fof(f191,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f190,f91])).

fof(f190,plain,
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
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f189,f96])).

fof(f189,plain,
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
    | ~ spl4_5 ),
    inference(resolution,[],[f57,f101])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f21])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f201,plain,
    ( spl4_13
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f162,f99,f94,f89,f84,f79,f199])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f161,f81])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f160,f86])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f159,f91])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f158,f96])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5 ),
    inference(resolution,[],[f64,f101])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f130,plain,
    ( ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f129,f125,f121])).

fof(f129,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f54,f127])).

fof(f54,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f37,f36,f35,f34])).

fof(f34,plain,
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

fof(f35,plain,
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

fof(f36,plain,
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

fof(f37,plain,
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f17])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f128,plain,
    ( spl4_9
    | spl4_10 ),
    inference(avatar_split_clause,[],[f53,f125,f121])).

fof(f53,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f117,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f50,f114])).

fof(f50,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f112,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f52,f109])).

fof(f52,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f107,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f51,f104])).

fof(f51,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f102,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f49,f99])).

fof(f49,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f97,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f48,f94])).

fof(f48,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f47,f89])).

fof(f47,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f46,f84])).

fof(f46,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f45,f79])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:04:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (27467)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (27476)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (27467)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f562,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f102,f107,f112,f117,f128,f130,f201,f227,f231,f240,f249,f302,f333,f352,f365,f376,f380,f386,f400,f423,f441,f460,f465,f504,f511,f530,f561])).
% 0.22/0.51  fof(f561,plain,(
% 0.22/0.51    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_33 | ~spl4_46),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f551])).
% 0.22/0.51  fof(f551,plain,(
% 0.22/0.51    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8 | ~spl4_33 | ~spl4_46)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f81,f86,f91,f96,f101,f356,f529,f116,f529,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~r1_xboole_0(X2,X3) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl4_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f114])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    spl4_8 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.51  fof(f529,plain,(
% 0.22/0.51    m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl4_46),
% 0.22/0.51    inference(avatar_component_clause,[],[f527])).
% 0.22/0.51  fof(f527,plain,(
% 0.22/0.51    spl4_46 <=> m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.22/0.51  fof(f356,plain,(
% 0.22/0.51    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_33),
% 0.22/0.51    inference(avatar_component_clause,[],[f354])).
% 0.22/0.51  fof(f354,plain,(
% 0.22/0.51    spl4_33 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    l1_orders_2(sK0) | ~spl4_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f99])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    spl4_5 <=> l1_orders_2(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    v5_orders_2(sK0) | ~spl4_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f94])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    spl4_4 <=> v5_orders_2(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    v4_orders_2(sK0) | ~spl4_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    spl4_3 <=> v4_orders_2(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    v3_orders_2(sK0) | ~spl4_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    spl4_2 <=> v3_orders_2(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ~v2_struct_0(sK0) | spl4_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    spl4_1 <=> v2_struct_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.51  fof(f530,plain,(
% 0.22/0.51    spl4_46 | ~spl4_6 | ~spl4_44),
% 0.22/0.51    inference(avatar_split_clause,[],[f513,f498,f104,f527])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    spl4_6 <=> m2_orders_2(sK2,sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.51  fof(f498,plain,(
% 0.22/0.51    spl4_44 <=> k1_xboole_0 = sK2),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.22/0.51  fof(f513,plain,(
% 0.22/0.51    m2_orders_2(k1_xboole_0,sK0,sK1) | (~spl4_6 | ~spl4_44)),
% 0.22/0.51    inference(backward_demodulation,[],[f106,f500])).
% 0.22/0.51  fof(f500,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | ~spl4_44),
% 0.22/0.51    inference(avatar_component_clause,[],[f498])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    m2_orders_2(sK2,sK0,sK1) | ~spl4_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f104])).
% 0.22/0.51  fof(f511,plain,(
% 0.22/0.51    ~spl4_41 | ~spl4_45),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f510])).
% 0.22/0.51  fof(f510,plain,(
% 0.22/0.51    $false | (~spl4_41 | ~spl4_45)),
% 0.22/0.51    inference(subsumption_resolution,[],[f508,f464])).
% 0.22/0.51  fof(f464,plain,(
% 0.22/0.51    m1_orders_2(sK2,sK0,sK2) | ~spl4_41),
% 0.22/0.51    inference(avatar_component_clause,[],[f462])).
% 0.22/0.51  fof(f462,plain,(
% 0.22/0.51    spl4_41 <=> m1_orders_2(sK2,sK0,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.22/0.51  fof(f508,plain,(
% 0.22/0.51    ~m1_orders_2(sK2,sK0,sK2) | (~spl4_41 | ~spl4_45)),
% 0.22/0.51    inference(resolution,[],[f503,f464])).
% 0.22/0.51  fof(f503,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_orders_2(sK2,sK0,X0) | ~m1_orders_2(X0,sK0,sK2)) ) | ~spl4_45),
% 0.22/0.51    inference(avatar_component_clause,[],[f502])).
% 0.22/0.51  fof(f502,plain,(
% 0.22/0.51    spl4_45 <=> ! [X0] : (~m1_orders_2(sK2,sK0,X0) | ~m1_orders_2(X0,sK0,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.22/0.51  fof(f504,plain,(
% 0.22/0.51    spl4_44 | spl4_45 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_20),
% 0.22/0.51    inference(avatar_split_clause,[],[f259,f237,f99,f94,f89,f84,f79,f502,f498])).
% 0.22/0.51  fof(f237,plain,(
% 0.22/0.51    spl4_20 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.51  fof(f259,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_orders_2(sK2,sK0,X0) | k1_xboole_0 = sK2 | ~m1_orders_2(X0,sK0,sK2)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_20)),
% 0.22/0.51    inference(subsumption_resolution,[],[f258,f81])).
% 0.22/0.51  fof(f258,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_orders_2(sK2,sK0,X0) | k1_xboole_0 = sK2 | ~m1_orders_2(X0,sK0,sK2) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_20)),
% 0.22/0.51    inference(subsumption_resolution,[],[f257,f86])).
% 0.22/0.51  fof(f257,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_orders_2(sK2,sK0,X0) | k1_xboole_0 = sK2 | ~m1_orders_2(X0,sK0,sK2) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_20)),
% 0.22/0.51    inference(subsumption_resolution,[],[f256,f91])).
% 0.22/0.51  fof(f256,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_orders_2(sK2,sK0,X0) | k1_xboole_0 = sK2 | ~m1_orders_2(X0,sK0,sK2) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | ~spl4_5 | ~spl4_20)),
% 0.22/0.51    inference(subsumption_resolution,[],[f255,f96])).
% 0.22/0.51  fof(f255,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_orders_2(sK2,sK0,X0) | k1_xboole_0 = sK2 | ~m1_orders_2(X0,sK0,sK2) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | ~spl4_20)),
% 0.22/0.51    inference(subsumption_resolution,[],[f252,f101])).
% 0.22/0.51  fof(f252,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_orders_2(sK2,sK0,X0) | k1_xboole_0 = sK2 | ~m1_orders_2(X0,sK0,sK2) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_20),
% 0.22/0.51    inference(resolution,[],[f239,f176])).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_orders_2(X2,X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f59,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).
% 0.22/0.51  fof(f239,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f237])).
% 0.22/0.51  fof(f465,plain,(
% 0.22/0.51    spl4_41 | spl4_9 | ~spl4_10 | ~spl4_37),
% 0.22/0.51    inference(avatar_split_clause,[],[f450,f383,f125,f121,f462])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    spl4_9 <=> r2_xboole_0(sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    spl4_10 <=> m1_orders_2(sK2,sK0,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.51  fof(f383,plain,(
% 0.22/0.51    spl4_37 <=> r1_tarski(sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.22/0.51  fof(f450,plain,(
% 0.22/0.51    m1_orders_2(sK2,sK0,sK2) | (spl4_9 | ~spl4_10 | ~spl4_37)),
% 0.22/0.51    inference(backward_demodulation,[],[f127,f447])).
% 0.22/0.51  fof(f447,plain,(
% 0.22/0.51    sK2 = sK3 | (spl4_9 | ~spl4_37)),
% 0.22/0.51    inference(subsumption_resolution,[],[f445,f122])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    ~r2_xboole_0(sK2,sK3) | spl4_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f121])).
% 0.22/0.51  fof(f445,plain,(
% 0.22/0.51    sK2 = sK3 | r2_xboole_0(sK2,sK3) | ~spl4_37),
% 0.22/0.51    inference(resolution,[],[f385,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.51    inference(flattening,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.51  fof(f385,plain,(
% 0.22/0.51    r1_tarski(sK2,sK3) | ~spl4_37),
% 0.22/0.51    inference(avatar_component_clause,[],[f383])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    m1_orders_2(sK2,sK0,sK3) | ~spl4_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f125])).
% 0.22/0.51  fof(f460,plain,(
% 0.22/0.51    sK2 != sK3 | m1_orders_2(sK2,sK0,sK3) | ~m1_orders_2(sK3,sK0,sK2)),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f441,plain,(
% 0.22/0.51    ~spl4_29 | ~spl4_35 | spl4_39),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f440])).
% 0.22/0.51  fof(f440,plain,(
% 0.22/0.51    $false | (~spl4_29 | ~spl4_35 | spl4_39)),
% 0.22/0.51    inference(subsumption_resolution,[],[f436,f399])).
% 0.22/0.51  fof(f399,plain,(
% 0.22/0.51    ~r1_tarski(sK3,sK2) | spl4_39),
% 0.22/0.51    inference(avatar_component_clause,[],[f397])).
% 0.22/0.51  fof(f397,plain,(
% 0.22/0.51    spl4_39 <=> r1_tarski(sK3,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.22/0.51  fof(f436,plain,(
% 0.22/0.51    r1_tarski(sK3,sK2) | (~spl4_29 | ~spl4_35)),
% 0.22/0.51    inference(resolution,[],[f325,f375])).
% 0.22/0.51  fof(f375,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2)) ) | ~spl4_35),
% 0.22/0.51    inference(avatar_component_clause,[],[f374])).
% 0.22/0.51  fof(f374,plain,(
% 0.22/0.51    spl4_35 <=> ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.22/0.51  fof(f325,plain,(
% 0.22/0.51    m1_orders_2(sK3,sK0,sK2) | ~spl4_29),
% 0.22/0.51    inference(avatar_component_clause,[],[f324])).
% 0.22/0.51  fof(f324,plain,(
% 0.22/0.51    spl4_29 <=> m1_orders_2(sK3,sK0,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.51  fof(f423,plain,(
% 0.22/0.51    ~spl4_6 | ~spl4_9 | spl4_10 | spl4_29 | ~spl4_32),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f422])).
% 0.22/0.51  fof(f422,plain,(
% 0.22/0.51    $false | (~spl4_6 | ~spl4_9 | spl4_10 | spl4_29 | ~spl4_32)),
% 0.22/0.51    inference(subsumption_resolution,[],[f409,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f43])).
% 0.22/0.51  fof(f409,plain,(
% 0.22/0.51    r2_xboole_0(sK2,sK2) | (~spl4_6 | ~spl4_9 | spl4_10 | spl4_29 | ~spl4_32)),
% 0.22/0.51    inference(backward_demodulation,[],[f123,f407])).
% 0.22/0.51  fof(f407,plain,(
% 0.22/0.51    sK2 = sK3 | (~spl4_6 | spl4_10 | spl4_29 | ~spl4_32)),
% 0.22/0.51    inference(subsumption_resolution,[],[f387,f126])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    ~m1_orders_2(sK2,sK0,sK3) | spl4_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f125])).
% 0.22/0.51  fof(f387,plain,(
% 0.22/0.51    sK2 = sK3 | m1_orders_2(sK2,sK0,sK3) | (~spl4_6 | spl4_29 | ~spl4_32)),
% 0.22/0.51    inference(subsumption_resolution,[],[f362,f326])).
% 0.22/0.51  fof(f326,plain,(
% 0.22/0.51    ~m1_orders_2(sK3,sK0,sK2) | spl4_29),
% 0.22/0.51    inference(avatar_component_clause,[],[f324])).
% 0.22/0.51  fof(f362,plain,(
% 0.22/0.51    sK2 = sK3 | m1_orders_2(sK2,sK0,sK3) | m1_orders_2(sK3,sK0,sK2) | (~spl4_6 | ~spl4_32)),
% 0.22/0.51    inference(resolution,[],[f351,f106])).
% 0.22/0.51  fof(f351,plain,(
% 0.22/0.51    ( ! [X1] : (~m2_orders_2(X1,sK0,sK1) | sK3 = X1 | m1_orders_2(X1,sK0,sK3) | m1_orders_2(sK3,sK0,X1)) ) | ~spl4_32),
% 0.22/0.51    inference(avatar_component_clause,[],[f350])).
% 0.22/0.51  fof(f350,plain,(
% 0.22/0.51    spl4_32 <=> ! [X1] : (~m2_orders_2(X1,sK0,sK1) | sK3 = X1 | m1_orders_2(X1,sK0,sK3) | m1_orders_2(sK3,sK0,X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    r2_xboole_0(sK2,sK3) | ~spl4_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f121])).
% 0.22/0.51  fof(f400,plain,(
% 0.22/0.51    ~spl4_39 | spl4_28 | ~spl4_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f389,f121,f320,f397])).
% 0.22/0.51  fof(f320,plain,(
% 0.22/0.51    spl4_28 <=> sK2 = sK3),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.51  fof(f389,plain,(
% 0.22/0.51    sK2 = sK3 | ~r1_tarski(sK3,sK2) | ~spl4_9),
% 0.22/0.51    inference(resolution,[],[f123,f141])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ( ! [X4,X3] : (~r2_xboole_0(X4,X3) | X3 = X4 | ~r1_tarski(X3,X4)) )),
% 0.22/0.51    inference(resolution,[],[f68,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f43])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f386,plain,(
% 0.22/0.51    spl4_37 | ~spl4_10 | ~spl4_36),
% 0.22/0.51    inference(avatar_split_clause,[],[f381,f378,f125,f383])).
% 0.22/0.51  fof(f378,plain,(
% 0.22/0.51    spl4_36 <=> ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.51  fof(f381,plain,(
% 0.22/0.51    r1_tarski(sK2,sK3) | (~spl4_10 | ~spl4_36)),
% 0.22/0.51    inference(resolution,[],[f379,f127])).
% 0.22/0.51  fof(f379,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3)) ) | ~spl4_36),
% 0.22/0.51    inference(avatar_component_clause,[],[f378])).
% 0.22/0.51  fof(f380,plain,(
% 0.22/0.51    spl4_36 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f290,f246,f99,f94,f89,f84,f79,f378])).
% 0.22/0.51  fof(f246,plain,(
% 0.22/0.51    spl4_22 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.51  fof(f290,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_22)),
% 0.22/0.51    inference(subsumption_resolution,[],[f289,f81])).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_22)),
% 0.22/0.51    inference(subsumption_resolution,[],[f288,f86])).
% 0.22/0.51  fof(f288,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_22)),
% 0.22/0.51    inference(subsumption_resolution,[],[f287,f91])).
% 0.22/0.51  fof(f287,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | ~spl4_5 | ~spl4_22)),
% 0.22/0.51    inference(subsumption_resolution,[],[f286,f96])).
% 0.22/0.51  fof(f286,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | ~spl4_22)),
% 0.22/0.51    inference(subsumption_resolution,[],[f275,f101])).
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_22),
% 0.22/0.51    inference(resolution,[],[f248,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).
% 0.22/0.51  fof(f248,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f246])).
% 0.22/0.51  fof(f376,plain,(
% 0.22/0.51    spl4_35 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_20),
% 0.22/0.51    inference(avatar_split_clause,[],[f269,f237,f99,f94,f89,f84,f79,f374])).
% 0.22/0.51  fof(f269,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_20)),
% 0.22/0.51    inference(subsumption_resolution,[],[f268,f81])).
% 0.22/0.51  fof(f268,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_20)),
% 0.22/0.51    inference(subsumption_resolution,[],[f267,f86])).
% 0.22/0.51  fof(f267,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_20)),
% 0.22/0.51    inference(subsumption_resolution,[],[f266,f91])).
% 0.22/0.51  fof(f266,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | ~spl4_5 | ~spl4_20)),
% 0.22/0.51    inference(subsumption_resolution,[],[f265,f96])).
% 0.22/0.51  fof(f265,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | ~spl4_20)),
% 0.22/0.51    inference(subsumption_resolution,[],[f254,f101])).
% 0.22/0.51  fof(f254,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_20),
% 0.22/0.51    inference(resolution,[],[f239,f58])).
% 0.22/0.51  fof(f365,plain,(
% 0.22/0.51    spl4_33 | ~spl4_30),
% 0.22/0.51    inference(avatar_split_clause,[],[f348,f330,f354])).
% 0.22/0.51  fof(f330,plain,(
% 0.22/0.51    spl4_30 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.51  fof(f348,plain,(
% 0.22/0.51    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_30),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f340])).
% 0.22/0.51  fof(f340,plain,(
% 0.22/0.51    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_30),
% 0.22/0.51    inference(superposition,[],[f73,f332])).
% 0.22/0.51  fof(f332,plain,(
% 0.22/0.51    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_30),
% 0.22/0.51    inference(avatar_component_clause,[],[f330])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.51  fof(f352,plain,(
% 0.22/0.51    spl4_32 | ~spl4_7 | ~spl4_25),
% 0.22/0.51    inference(avatar_split_clause,[],[f312,f300,f109,f350])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    spl4_7 <=> m2_orders_2(sK3,sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.51  fof(f300,plain,(
% 0.22/0.51    spl4_25 <=> ! [X1,X0] : (X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.51  fof(f312,plain,(
% 0.22/0.51    ( ! [X1] : (~m2_orders_2(X1,sK0,sK1) | sK3 = X1 | m1_orders_2(X1,sK0,sK3) | m1_orders_2(sK3,sK0,X1)) ) | (~spl4_7 | ~spl4_25)),
% 0.22/0.51    inference(resolution,[],[f301,f111])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    m2_orders_2(sK3,sK0,sK1) | ~spl4_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f109])).
% 0.22/0.51  fof(f301,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | X0 = X1 | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) ) | ~spl4_25),
% 0.22/0.51    inference(avatar_component_clause,[],[f300])).
% 0.22/0.51  fof(f333,plain,(
% 0.22/0.51    spl4_30),
% 0.22/0.51    inference(avatar_split_clause,[],[f328,f330])).
% 0.22/0.51  fof(f328,plain,(
% 0.22/0.51    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.51    inference(equality_resolution,[],[f272])).
% 0.22/0.51  fof(f272,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 != X0 | k4_xboole_0(X0,X0) = X0) )),
% 0.22/0.51    inference(superposition,[],[f172,f132])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) )),
% 0.22/0.51    inference(resolution,[],[f72,f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.51    inference(resolution,[],[f62,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ( ! [X2,X3] : (k1_xboole_0 != k4_xboole_0(X2,k4_xboole_0(X2,X3)) | k4_xboole_0(X2,X3) = X2) )),
% 0.22/0.51    inference(resolution,[],[f143,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | k4_xboole_0(X1,X0) != k1_xboole_0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1] : (k4_xboole_0(X1,X0) != k1_xboole_0 | ~r2_xboole_0(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : ~(k4_xboole_0(X1,X0) = k1_xboole_0 & r2_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    ( ! [X2,X1] : (r2_xboole_0(k4_xboole_0(X1,X2),X1) | k4_xboole_0(X1,X2) = X1) )),
% 0.22/0.51    inference(resolution,[],[f71,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.51  fof(f302,plain,(
% 0.22/0.51    spl4_25 | ~spl4_8 | ~spl4_18),
% 0.22/0.51    inference(avatar_split_clause,[],[f235,f225,f114,f300])).
% 0.22/0.51  fof(f225,plain,(
% 0.22/0.51    spl4_18 <=> ! [X1,X0,X2] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    ( ! [X0,X1] : (X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) ) | (~spl4_8 | ~spl4_18)),
% 0.22/0.51    inference(resolution,[],[f226,f116])).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) ) | ~spl4_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f225])).
% 0.22/0.51  fof(f249,plain,(
% 0.22/0.51    spl4_22 | ~spl4_7 | ~spl4_19),
% 0.22/0.51    inference(avatar_split_clause,[],[f234,f229,f109,f246])).
% 0.22/0.51  fof(f229,plain,(
% 0.22/0.51    spl4_19 <=> ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.51  fof(f234,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_7 | ~spl4_19)),
% 0.22/0.51    inference(resolution,[],[f230,f111])).
% 0.22/0.51  fof(f230,plain,(
% 0.22/0.51    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f229])).
% 0.22/0.51  fof(f240,plain,(
% 0.22/0.51    spl4_20 | ~spl4_6 | ~spl4_19),
% 0.22/0.51    inference(avatar_split_clause,[],[f233,f229,f104,f237])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_6 | ~spl4_19)),
% 0.22/0.51    inference(resolution,[],[f230,f106])).
% 0.22/0.51  fof(f231,plain,(
% 0.22/0.51    spl4_19 | ~spl4_8 | ~spl4_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f204,f199,f114,f229])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    spl4_13 <=> ! [X1,X0] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl4_8 | ~spl4_13)),
% 0.22/0.51    inference(resolution,[],[f200,f116])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,X1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f199])).
% 0.22/0.51  fof(f227,plain,(
% 0.22/0.51    spl4_18 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f193,f99,f94,f89,f84,f79,f225])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f192,f81])).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f191,f86])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f190,f91])).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | ~spl4_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f189,f96])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_5),
% 0.22/0.51    inference(resolution,[],[f57,f101])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_orders_2(X2,X0,X3) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    spl4_13 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f162,f99,f94,f89,f84,f79,f199])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f161,f81])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f160,f86])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f159,f91])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | ~spl4_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f158,f96])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_5),
% 0.22/0.51    inference(resolution,[],[f64,f101])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    ~spl4_9 | ~spl4_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f129,f125,f121])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    ~r2_xboole_0(sK2,sK3) | ~spl4_10),
% 0.22/0.51    inference(subsumption_resolution,[],[f54,f127])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f37,f36,f35,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) => (? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) => ((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f14])).
% 0.22/0.51  fof(f14,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    spl4_9 | spl4_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f53,f125,f121])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    spl4_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f50,f114])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    spl4_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f52,f109])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    m2_orders_2(sK3,sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    spl4_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f51,f104])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    m2_orders_2(sK2,sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    spl4_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f49,f99])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    l1_orders_2(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    spl4_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f48,f94])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    v5_orders_2(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    spl4_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f47,f89])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    v4_orders_2(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    spl4_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f46,f84])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    v3_orders_2(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ~spl4_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f45,f79])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (27467)------------------------------
% 0.22/0.51  % (27467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27467)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (27467)Memory used [KB]: 6524
% 0.22/0.51  % (27467)Time elapsed: 0.066 s
% 0.22/0.51  % (27467)------------------------------
% 0.22/0.51  % (27467)------------------------------
% 0.22/0.51  % (27455)Success in time 0.146 s
%------------------------------------------------------------------------------
