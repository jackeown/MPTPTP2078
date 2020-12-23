%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  224 ( 509 expanded)
%              Number of leaves         :   49 ( 230 expanded)
%              Depth                    :   12
%              Number of atoms          : 1135 (2837 expanded)
%              Number of equality atoms :   55 (  80 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f508,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f111,f116,f125,f127,f194,f206,f220,f224,f233,f237,f242,f288,f299,f322,f326,f333,f340,f350,f368,f400,f424,f426,f446,f447,f465,f501,f506,f507])).

fof(f507,plain,
    ( k1_xboole_0 != sK2
    | sK2 != sK3
    | m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ m2_orders_2(sK3,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f506,plain,
    ( ~ spl5_39
    | ~ spl5_41 ),
    inference(avatar_contradiction_clause,[],[f505])).

fof(f505,plain,
    ( $false
    | ~ spl5_39
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f503,f464])).

fof(f464,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f462])).

fof(f462,plain,
    ( spl5_39
  <=> m1_orders_2(sK2,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f503,plain,
    ( ~ m1_orders_2(sK2,sK0,sK2)
    | ~ spl5_39
    | ~ spl5_41 ),
    inference(resolution,[],[f500,f464])).

fof(f500,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | ~ m1_orders_2(X0,sK0,sK2) )
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f499])).

fof(f499,plain,
    ( spl5_41
  <=> ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | ~ m1_orders_2(X0,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f501,plain,
    ( spl5_40
    | spl5_41
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f252,f230,f98,f93,f88,f83,f78,f499,f495])).

fof(f495,plain,
    ( spl5_40
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f78,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f83,plain,
    ( spl5_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f88,plain,
    ( spl5_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f93,plain,
    ( spl5_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f98,plain,
    ( spl5_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f230,plain,
    ( spl5_20
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | k1_xboole_0 = sK2
        | ~ m1_orders_2(X0,sK0,sK2) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f251,f80])).

fof(f80,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | k1_xboole_0 = sK2
        | ~ m1_orders_2(X0,sK0,sK2)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f250,f85])).

fof(f85,plain,
    ( v3_orders_2(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | k1_xboole_0 = sK2
        | ~ m1_orders_2(X0,sK0,sK2)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f249,f90])).

fof(f90,plain,
    ( v4_orders_2(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | k1_xboole_0 = sK2
        | ~ m1_orders_2(X0,sK0,sK2)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f248,f95])).

fof(f95,plain,
    ( v5_orders_2(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | k1_xboole_0 = sK2
        | ~ m1_orders_2(X0,sK0,sK2)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f245,f100])).

fof(f100,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | k1_xboole_0 = sK2
        | ~ m1_orders_2(X0,sK0,sK2)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_20 ),
    inference(resolution,[],[f232,f167])).

fof(f167,plain,(
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
    inference(subsumption_resolution,[],[f60,f66])).

fof(f66,plain,(
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

fof(f60,plain,(
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

fof(f232,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f230])).

fof(f465,plain,
    ( spl5_39
    | ~ spl5_10
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f456,f304,f122,f462])).

fof(f122,plain,
    ( spl5_10
  <=> m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f304,plain,
    ( spl5_27
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f456,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl5_10
    | ~ spl5_27 ),
    inference(backward_demodulation,[],[f124,f306])).

fof(f306,plain,
    ( sK2 = sK3
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f304])).

fof(f124,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f447,plain,
    ( sK2 != sK3
    | m1_orders_2(sK2,sK0,sK3)
    | ~ m1_orders_2(sK3,sK0,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f446,plain,
    ( ~ spl5_28
    | ~ spl5_32
    | spl5_37 ),
    inference(avatar_contradiction_clause,[],[f445])).

fof(f445,plain,
    ( $false
    | ~ spl5_28
    | ~ spl5_32
    | spl5_37 ),
    inference(subsumption_resolution,[],[f441,f399])).

fof(f399,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl5_37 ),
    inference(avatar_component_clause,[],[f397])).

fof(f397,plain,
    ( spl5_37
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f441,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl5_28
    | ~ spl5_32 ),
    inference(resolution,[],[f309,f332])).

fof(f332,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2) )
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl5_32
  <=> ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f309,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl5_28
  <=> m1_orders_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f426,plain,
    ( ~ spl5_6
    | ~ spl5_9
    | spl5_10
    | spl5_28
    | ~ spl5_31 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_9
    | spl5_10
    | spl5_28
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f414,f76])).

fof(f76,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f414,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ spl5_6
    | ~ spl5_9
    | spl5_10
    | spl5_28
    | ~ spl5_31 ),
    inference(backward_demodulation,[],[f120,f412])).

fof(f412,plain,
    ( sK2 = sK3
    | ~ spl5_6
    | spl5_10
    | spl5_28
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f411,f310])).

fof(f310,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | spl5_28 ),
    inference(avatar_component_clause,[],[f308])).

fof(f411,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2)
    | ~ spl5_6
    | spl5_10
    | ~ spl5_31 ),
    inference(subsumption_resolution,[],[f408,f123])).

fof(f123,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f408,plain,
    ( sK2 = sK3
    | m1_orders_2(sK2,sK0,sK3)
    | m1_orders_2(sK3,sK0,sK2)
    | ~ spl5_6
    | ~ spl5_31 ),
    inference(resolution,[],[f325,f105])).

fof(f105,plain,
    ( m2_orders_2(sK2,sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_6
  <=> m2_orders_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f325,plain,
    ( ! [X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | sK3 = X1
        | m1_orders_2(X1,sK0,sK3)
        | m1_orders_2(sK3,sK0,X1) )
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl5_31
  <=> ! [X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | sK3 = X1
        | m1_orders_2(X1,sK0,sK3)
        | m1_orders_2(sK3,sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f120,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl5_9
  <=> r2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f424,plain,
    ( spl5_27
    | ~ spl5_6
    | spl5_10
    | spl5_28
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f412,f324,f308,f122,f103,f304])).

fof(f400,plain,
    ( ~ spl5_37
    | spl5_27
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f370,f118,f304,f397])).

fof(f370,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK3,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f120,f134])).

fof(f134,plain,(
    ! [X2,X3] :
      ( ~ r2_xboole_0(X3,X2)
      | X2 = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f69,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f368,plain,
    ( spl5_27
    | spl5_9
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f357,f347,f118,f304])).

fof(f347,plain,
    ( spl5_35
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f357,plain,
    ( sK2 = sK3
    | spl5_9
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f355,f119])).

fof(f119,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f355,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK2,sK3)
    | ~ spl5_35 ),
    inference(resolution,[],[f349,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f349,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f347])).

fof(f350,plain,
    ( spl5_35
    | ~ spl5_10
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f341,f338,f122,f347])).

fof(f338,plain,
    ( spl5_33
  <=> ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f341,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl5_10
    | ~ spl5_33 ),
    inference(resolution,[],[f339,f124])).

fof(f339,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3) )
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f338])).

fof(f340,plain,
    ( spl5_33
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f284,f239,f98,f93,f88,f83,f78,f338])).

fof(f239,plain,
    ( spl5_22
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f284,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f283,f80])).

fof(f283,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f282,f85])).

fof(f282,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f281,f90])).

fof(f281,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f280,f95])).

fof(f280,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_5
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f269,f100])).

fof(f269,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK3)
        | r1_tarski(X2,sK3)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_22 ),
    inference(resolution,[],[f241,f59])).

fof(f59,plain,(
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

fof(f241,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f239])).

fof(f333,plain,
    ( spl5_32
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f262,f230,f98,f93,f88,f83,f78,f331])).

fof(f262,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f261,f80])).

fof(f261,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f260,f85])).

fof(f260,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f259,f90])).

fof(f259,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f258,f95])).

fof(f258,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f247,f100])).

fof(f247,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,sK2)
        | r1_tarski(X2,sK2)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_20 ),
    inference(resolution,[],[f232,f59])).

fof(f326,plain,
    ( spl5_31
    | ~ spl5_7
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f301,f286,f108,f324])).

fof(f108,plain,
    ( spl5_7
  <=> m2_orders_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f286,plain,
    ( spl5_24
  <=> ! [X1,X0] :
        ( X0 = X1
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f301,plain,
    ( ! [X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | sK3 = X1
        | m1_orders_2(X1,sK0,sK3)
        | m1_orders_2(sK3,sK0,X1) )
    | ~ spl5_7
    | ~ spl5_24 ),
    inference(resolution,[],[f287,f110])).

fof(f110,plain,
    ( m2_orders_2(sK3,sK0,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f287,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | ~ m2_orders_2(X0,sK0,sK1)
        | X0 = X1
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f286])).

fof(f322,plain,
    ( ~ spl5_29
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f312,f297,f314])).

fof(f314,plain,
    ( spl5_29
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f297,plain,
    ( spl5_26
  <=> ! [X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X1,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f312,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl5_26 ),
    inference(resolution,[],[f298,f130])).

fof(f130,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f128,f55])).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK4(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f61,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

% (23477)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
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
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f298,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK3)
        | ~ m2_orders_2(X1,sK0,sK1) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f297])).

fof(f299,plain,
    ( spl5_26
    | ~ spl5_7
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f244,f235,f108,f297])).

fof(f235,plain,
    ( spl5_21
  <=> ! [X1,X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f244,plain,
    ( ! [X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X1,sK3) )
    | ~ spl5_7
    | ~ spl5_21 ),
    inference(resolution,[],[f236,f110])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f235])).

fof(f288,plain,
    ( spl5_24
    | ~ spl5_8
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f228,f218,f113,f286])).

fof(f113,plain,
    ( spl5_8
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f218,plain,
    ( spl5_18
  <=> ! [X1,X0,X2] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( X0 = X1
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) )
    | ~ spl5_8
    | ~ spl5_18 ),
    inference(resolution,[],[f219,f115])).

fof(f115,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f219,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f218])).

fof(f242,plain,
    ( spl5_22
    | ~ spl5_7
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f227,f222,f108,f239])).

fof(f222,plain,
    ( spl5_19
  <=> ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f227,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_7
    | ~ spl5_19 ),
    inference(resolution,[],[f223,f110])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f222])).

fof(f237,plain,
    ( spl5_21
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f212,f204,f113,f235])).

fof(f204,plain,
    ( spl5_15
  <=> ! [X1,X0,X2] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m2_orders_2(X2,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(resolution,[],[f205,f115])).

fof(f205,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X2,sK0,X1)
        | ~ m2_orders_2(X0,sK0,X1)
        | ~ r1_xboole_0(X2,X0) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f204])).

fof(f233,plain,
    ( spl5_20
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f226,f222,f103,f230])).

fof(f226,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(resolution,[],[f223,f105])).

fof(f224,plain,
    ( spl5_19
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f197,f192,f113,f222])).

fof(f192,plain,
    ( spl5_13
  <=> ! [X1,X0] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(resolution,[],[f193,f115])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X0,sK0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f192])).

fof(f220,plain,
    ( spl5_18
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f181,f98,f93,f88,f83,f78,f218])).

fof(f181,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f180,f80])).

fof(f180,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f179,f85])).

fof(f179,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f178,f90])).

fof(f178,plain,
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
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f177,f95])).

fof(f177,plain,
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
    | ~ spl5_5 ),
    inference(resolution,[],[f58,f100])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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

fof(f206,plain,
    ( spl5_15
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f164,f98,f93,f88,f83,f78,f204])).

fof(f164,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m2_orders_2(X2,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X2,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f163,f80])).

fof(f163,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m2_orders_2(X2,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X2,X0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f162,f85])).

fof(f162,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m2_orders_2(X2,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X2,X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f161,f90])).

fof(f161,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m2_orders_2(X2,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X2,X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f160,f95])).

fof(f160,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m2_orders_2(X2,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(X2,X0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f56,f100])).

fof(f56,plain,(
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

fof(f194,plain,
    ( spl5_13
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f156,f98,f93,f88,f83,f78,f192])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f155,f80])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f154,f85])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f153,f90])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f152,f95])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f65,f100])).

fof(f65,plain,(
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

fof(f127,plain,
    ( ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f126,f122,f118])).

fof(f126,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f54,f124])).

fof(f54,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f36,f35,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f35,plain,
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

fof(f36,plain,
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
    inference(flattening,[],[f31])).

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

fof(f125,plain,
    ( spl5_9
    | spl5_10 ),
    inference(avatar_split_clause,[],[f53,f122,f118])).

fof(f53,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f116,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f50,f113])).

fof(f50,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f111,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f52,f108])).

fof(f52,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f106,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f51,f103])).

fof(f51,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f101,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f49,f98])).

fof(f49,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f96,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f48,f93])).

fof(f48,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f47,f88])).

fof(f47,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f86,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f46,f83])).

fof(f46,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f45,f78])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:30:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (23478)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (23478)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (23479)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f508,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f111,f116,f125,f127,f194,f206,f220,f224,f233,f237,f242,f288,f299,f322,f326,f333,f340,f350,f368,f400,f424,f426,f446,f447,f465,f501,f506,f507])).
% 0.20/0.50  fof(f507,plain,(
% 0.20/0.50    k1_xboole_0 != sK2 | sK2 != sK3 | m2_orders_2(k1_xboole_0,sK0,sK1) | ~m2_orders_2(sK3,sK0,sK1)),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f506,plain,(
% 0.20/0.50    ~spl5_39 | ~spl5_41),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f505])).
% 0.20/0.50  fof(f505,plain,(
% 0.20/0.50    $false | (~spl5_39 | ~spl5_41)),
% 0.20/0.50    inference(subsumption_resolution,[],[f503,f464])).
% 0.20/0.50  fof(f464,plain,(
% 0.20/0.50    m1_orders_2(sK2,sK0,sK2) | ~spl5_39),
% 0.20/0.50    inference(avatar_component_clause,[],[f462])).
% 0.20/0.50  fof(f462,plain,(
% 0.20/0.50    spl5_39 <=> m1_orders_2(sK2,sK0,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.20/0.50  fof(f503,plain,(
% 0.20/0.50    ~m1_orders_2(sK2,sK0,sK2) | (~spl5_39 | ~spl5_41)),
% 0.20/0.50    inference(resolution,[],[f500,f464])).
% 0.20/0.50  fof(f500,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_orders_2(sK2,sK0,X0) | ~m1_orders_2(X0,sK0,sK2)) ) | ~spl5_41),
% 0.20/0.50    inference(avatar_component_clause,[],[f499])).
% 0.20/0.50  fof(f499,plain,(
% 0.20/0.50    spl5_41 <=> ! [X0] : (~m1_orders_2(sK2,sK0,X0) | ~m1_orders_2(X0,sK0,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.20/0.50  fof(f501,plain,(
% 0.20/0.50    spl5_40 | spl5_41 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_20),
% 0.20/0.50    inference(avatar_split_clause,[],[f252,f230,f98,f93,f88,f83,f78,f499,f495])).
% 0.20/0.50  fof(f495,plain,(
% 0.20/0.50    spl5_40 <=> k1_xboole_0 = sK2),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    spl5_1 <=> v2_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    spl5_2 <=> v3_orders_2(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    spl5_3 <=> v4_orders_2(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    spl5_4 <=> v5_orders_2(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    spl5_5 <=> l1_orders_2(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.50  fof(f230,plain,(
% 0.20/0.50    spl5_20 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.50  fof(f252,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_orders_2(sK2,sK0,X0) | k1_xboole_0 = sK2 | ~m1_orders_2(X0,sK0,sK2)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_20)),
% 0.20/0.50    inference(subsumption_resolution,[],[f251,f80])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ~v2_struct_0(sK0) | spl5_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f78])).
% 0.20/0.50  fof(f251,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_orders_2(sK2,sK0,X0) | k1_xboole_0 = sK2 | ~m1_orders_2(X0,sK0,sK2) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_20)),
% 0.20/0.50    inference(subsumption_resolution,[],[f250,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    v3_orders_2(sK0) | ~spl5_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f83])).
% 0.20/0.50  fof(f250,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_orders_2(sK2,sK0,X0) | k1_xboole_0 = sK2 | ~m1_orders_2(X0,sK0,sK2) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_20)),
% 0.20/0.50    inference(subsumption_resolution,[],[f249,f90])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    v4_orders_2(sK0) | ~spl5_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f88])).
% 0.20/0.50  fof(f249,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_orders_2(sK2,sK0,X0) | k1_xboole_0 = sK2 | ~m1_orders_2(X0,sK0,sK2) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_20)),
% 0.20/0.50    inference(subsumption_resolution,[],[f248,f95])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    v5_orders_2(sK0) | ~spl5_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f93])).
% 0.20/0.50  fof(f248,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_orders_2(sK2,sK0,X0) | k1_xboole_0 = sK2 | ~m1_orders_2(X0,sK0,sK2) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_5 | ~spl5_20)),
% 0.20/0.50    inference(subsumption_resolution,[],[f245,f100])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    l1_orders_2(sK0) | ~spl5_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f98])).
% 0.20/0.50  fof(f245,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_orders_2(sK2,sK0,X0) | k1_xboole_0 = sK2 | ~m1_orders_2(X0,sK0,sK2) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_20),
% 0.20/0.50    inference(resolution,[],[f232,f167])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_orders_2(X2,X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f60,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).
% 0.20/0.50  fof(f232,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_20),
% 0.20/0.50    inference(avatar_component_clause,[],[f230])).
% 0.20/0.50  fof(f465,plain,(
% 0.20/0.50    spl5_39 | ~spl5_10 | ~spl5_27),
% 0.20/0.50    inference(avatar_split_clause,[],[f456,f304,f122,f462])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    spl5_10 <=> m1_orders_2(sK2,sK0,sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.50  fof(f304,plain,(
% 0.20/0.50    spl5_27 <=> sK2 = sK3),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.20/0.50  fof(f456,plain,(
% 0.20/0.50    m1_orders_2(sK2,sK0,sK2) | (~spl5_10 | ~spl5_27)),
% 0.20/0.50    inference(backward_demodulation,[],[f124,f306])).
% 0.20/0.50  fof(f306,plain,(
% 0.20/0.50    sK2 = sK3 | ~spl5_27),
% 0.20/0.50    inference(avatar_component_clause,[],[f304])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    m1_orders_2(sK2,sK0,sK3) | ~spl5_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f122])).
% 0.20/0.50  fof(f447,plain,(
% 0.20/0.50    sK2 != sK3 | m1_orders_2(sK2,sK0,sK3) | ~m1_orders_2(sK3,sK0,sK2)),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f446,plain,(
% 0.20/0.50    ~spl5_28 | ~spl5_32 | spl5_37),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f445])).
% 0.20/0.50  fof(f445,plain,(
% 0.20/0.50    $false | (~spl5_28 | ~spl5_32 | spl5_37)),
% 0.20/0.50    inference(subsumption_resolution,[],[f441,f399])).
% 0.20/0.50  fof(f399,plain,(
% 0.20/0.50    ~r1_tarski(sK3,sK2) | spl5_37),
% 0.20/0.50    inference(avatar_component_clause,[],[f397])).
% 0.20/0.50  fof(f397,plain,(
% 0.20/0.50    spl5_37 <=> r1_tarski(sK3,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.20/0.50  fof(f441,plain,(
% 0.20/0.50    r1_tarski(sK3,sK2) | (~spl5_28 | ~spl5_32)),
% 0.20/0.50    inference(resolution,[],[f309,f332])).
% 0.20/0.50  fof(f332,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2)) ) | ~spl5_32),
% 0.20/0.50    inference(avatar_component_clause,[],[f331])).
% 0.20/0.50  fof(f331,plain,(
% 0.20/0.50    spl5_32 <=> ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.20/0.50  fof(f309,plain,(
% 0.20/0.50    m1_orders_2(sK3,sK0,sK2) | ~spl5_28),
% 0.20/0.50    inference(avatar_component_clause,[],[f308])).
% 0.20/0.50  fof(f308,plain,(
% 0.20/0.50    spl5_28 <=> m1_orders_2(sK3,sK0,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.20/0.50  fof(f426,plain,(
% 0.20/0.50    ~spl5_6 | ~spl5_9 | spl5_10 | spl5_28 | ~spl5_31),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f425])).
% 0.20/0.50  fof(f425,plain,(
% 0.20/0.50    $false | (~spl5_6 | ~spl5_9 | spl5_10 | spl5_28 | ~spl5_31)),
% 0.20/0.50    inference(subsumption_resolution,[],[f414,f76])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.50    inference(flattening,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.50  fof(f414,plain,(
% 0.20/0.50    r2_xboole_0(sK2,sK2) | (~spl5_6 | ~spl5_9 | spl5_10 | spl5_28 | ~spl5_31)),
% 0.20/0.50    inference(backward_demodulation,[],[f120,f412])).
% 0.20/0.50  fof(f412,plain,(
% 0.20/0.50    sK2 = sK3 | (~spl5_6 | spl5_10 | spl5_28 | ~spl5_31)),
% 0.20/0.50    inference(subsumption_resolution,[],[f411,f310])).
% 0.20/0.50  fof(f310,plain,(
% 0.20/0.50    ~m1_orders_2(sK3,sK0,sK2) | spl5_28),
% 0.20/0.50    inference(avatar_component_clause,[],[f308])).
% 0.20/0.50  fof(f411,plain,(
% 0.20/0.50    sK2 = sK3 | m1_orders_2(sK3,sK0,sK2) | (~spl5_6 | spl5_10 | ~spl5_31)),
% 0.20/0.50    inference(subsumption_resolution,[],[f408,f123])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    ~m1_orders_2(sK2,sK0,sK3) | spl5_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f122])).
% 0.20/0.50  fof(f408,plain,(
% 0.20/0.50    sK2 = sK3 | m1_orders_2(sK2,sK0,sK3) | m1_orders_2(sK3,sK0,sK2) | (~spl5_6 | ~spl5_31)),
% 0.20/0.50    inference(resolution,[],[f325,f105])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    m2_orders_2(sK2,sK0,sK1) | ~spl5_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f103])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    spl5_6 <=> m2_orders_2(sK2,sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.50  fof(f325,plain,(
% 0.20/0.50    ( ! [X1] : (~m2_orders_2(X1,sK0,sK1) | sK3 = X1 | m1_orders_2(X1,sK0,sK3) | m1_orders_2(sK3,sK0,X1)) ) | ~spl5_31),
% 0.20/0.50    inference(avatar_component_clause,[],[f324])).
% 0.20/0.50  fof(f324,plain,(
% 0.20/0.50    spl5_31 <=> ! [X1] : (~m2_orders_2(X1,sK0,sK1) | sK3 = X1 | m1_orders_2(X1,sK0,sK3) | m1_orders_2(sK3,sK0,X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    r2_xboole_0(sK2,sK3) | ~spl5_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f118])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    spl5_9 <=> r2_xboole_0(sK2,sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.50  fof(f424,plain,(
% 0.20/0.50    spl5_27 | ~spl5_6 | spl5_10 | spl5_28 | ~spl5_31),
% 0.20/0.50    inference(avatar_split_clause,[],[f412,f324,f308,f122,f103,f304])).
% 0.20/0.50  fof(f400,plain,(
% 0.20/0.50    ~spl5_37 | spl5_27 | ~spl5_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f370,f118,f304,f397])).
% 0.20/0.50  fof(f370,plain,(
% 0.20/0.50    sK2 = sK3 | ~r1_tarski(sK3,sK2) | ~spl5_9),
% 0.20/0.50    inference(resolution,[],[f120,f134])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r2_xboole_0(X3,X2) | X2 = X3 | ~r1_tarski(X2,X3)) )),
% 0.20/0.50    inference(resolution,[],[f69,f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(flattening,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f368,plain,(
% 0.20/0.50    spl5_27 | spl5_9 | ~spl5_35),
% 0.20/0.50    inference(avatar_split_clause,[],[f357,f347,f118,f304])).
% 0.20/0.50  fof(f347,plain,(
% 0.20/0.50    spl5_35 <=> r1_tarski(sK2,sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.20/0.50  fof(f357,plain,(
% 0.20/0.50    sK2 = sK3 | (spl5_9 | ~spl5_35)),
% 0.20/0.50    inference(subsumption_resolution,[],[f355,f119])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ~r2_xboole_0(sK2,sK3) | spl5_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f118])).
% 0.20/0.50  fof(f355,plain,(
% 0.20/0.50    sK2 = sK3 | r2_xboole_0(sK2,sK3) | ~spl5_35),
% 0.20/0.50    inference(resolution,[],[f349,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f349,plain,(
% 0.20/0.50    r1_tarski(sK2,sK3) | ~spl5_35),
% 0.20/0.50    inference(avatar_component_clause,[],[f347])).
% 0.20/0.50  fof(f350,plain,(
% 0.20/0.50    spl5_35 | ~spl5_10 | ~spl5_33),
% 0.20/0.50    inference(avatar_split_clause,[],[f341,f338,f122,f347])).
% 0.20/0.50  fof(f338,plain,(
% 0.20/0.50    spl5_33 <=> ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.20/0.50  fof(f341,plain,(
% 0.20/0.50    r1_tarski(sK2,sK3) | (~spl5_10 | ~spl5_33)),
% 0.20/0.50    inference(resolution,[],[f339,f124])).
% 0.20/0.50  fof(f339,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3)) ) | ~spl5_33),
% 0.20/0.50    inference(avatar_component_clause,[],[f338])).
% 0.20/0.50  fof(f340,plain,(
% 0.20/0.50    spl5_33 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f284,f239,f98,f93,f88,f83,f78,f338])).
% 0.20/0.50  fof(f239,plain,(
% 0.20/0.50    spl5_22 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.50  fof(f284,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f283,f80])).
% 0.20/0.50  fof(f283,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f282,f85])).
% 0.20/0.50  fof(f282,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f281,f90])).
% 0.20/0.50  fof(f281,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f280,f95])).
% 0.20/0.50  fof(f280,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_5 | ~spl5_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f269,f100])).
% 0.20/0.50  fof(f269,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_22),
% 0.20/0.50    inference(resolution,[],[f241,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).
% 0.20/0.50  fof(f241,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_22),
% 0.20/0.50    inference(avatar_component_clause,[],[f239])).
% 0.20/0.50  fof(f333,plain,(
% 0.20/0.50    spl5_32 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_20),
% 0.20/0.50    inference(avatar_split_clause,[],[f262,f230,f98,f93,f88,f83,f78,f331])).
% 0.20/0.50  fof(f262,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_20)),
% 0.20/0.50    inference(subsumption_resolution,[],[f261,f80])).
% 0.20/0.50  fof(f261,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_20)),
% 0.20/0.50    inference(subsumption_resolution,[],[f260,f85])).
% 0.20/0.50  fof(f260,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_20)),
% 0.20/0.50    inference(subsumption_resolution,[],[f259,f90])).
% 0.20/0.50  fof(f259,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_20)),
% 0.20/0.50    inference(subsumption_resolution,[],[f258,f95])).
% 0.20/0.50  fof(f258,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_5 | ~spl5_20)),
% 0.20/0.50    inference(subsumption_resolution,[],[f247,f100])).
% 0.20/0.50  fof(f247,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_20),
% 0.20/0.50    inference(resolution,[],[f232,f59])).
% 0.20/0.50  fof(f326,plain,(
% 0.20/0.50    spl5_31 | ~spl5_7 | ~spl5_24),
% 0.20/0.50    inference(avatar_split_clause,[],[f301,f286,f108,f324])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    spl5_7 <=> m2_orders_2(sK3,sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.50  fof(f286,plain,(
% 0.20/0.50    spl5_24 <=> ! [X1,X0] : (X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.20/0.50  fof(f301,plain,(
% 0.20/0.50    ( ! [X1] : (~m2_orders_2(X1,sK0,sK1) | sK3 = X1 | m1_orders_2(X1,sK0,sK3) | m1_orders_2(sK3,sK0,X1)) ) | (~spl5_7 | ~spl5_24)),
% 0.20/0.50    inference(resolution,[],[f287,f110])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    m2_orders_2(sK3,sK0,sK1) | ~spl5_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f108])).
% 0.20/0.50  fof(f287,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | X0 = X1 | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) ) | ~spl5_24),
% 0.20/0.50    inference(avatar_component_clause,[],[f286])).
% 0.20/0.50  fof(f322,plain,(
% 0.20/0.50    ~spl5_29 | ~spl5_26),
% 0.20/0.50    inference(avatar_split_clause,[],[f312,f297,f314])).
% 0.20/0.50  fof(f314,plain,(
% 0.20/0.50    spl5_29 <=> m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.20/0.50  fof(f297,plain,(
% 0.20/0.50    spl5_26 <=> ! [X1] : (~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X1,sK3))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.20/0.50  fof(f312,plain,(
% 0.20/0.50    ~m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl5_26),
% 0.20/0.50    inference(resolution,[],[f298,f130])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.50    inference(resolution,[],[f128,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,sK4(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(resolution,[],[f61,f73])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  % (23477)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(rectify,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.50  fof(f298,plain,(
% 0.20/0.50    ( ! [X1] : (~r1_xboole_0(X1,sK3) | ~m2_orders_2(X1,sK0,sK1)) ) | ~spl5_26),
% 0.20/0.50    inference(avatar_component_clause,[],[f297])).
% 0.20/0.50  fof(f299,plain,(
% 0.20/0.50    spl5_26 | ~spl5_7 | ~spl5_21),
% 0.20/0.50    inference(avatar_split_clause,[],[f244,f235,f108,f297])).
% 0.20/0.50  fof(f235,plain,(
% 0.20/0.50    spl5_21 <=> ! [X1,X0] : (~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X0,X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.50  fof(f244,plain,(
% 0.20/0.50    ( ! [X1] : (~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X1,sK3)) ) | (~spl5_7 | ~spl5_21)),
% 0.20/0.50    inference(resolution,[],[f236,f110])).
% 0.20/0.50  fof(f236,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(X0,X1)) ) | ~spl5_21),
% 0.20/0.50    inference(avatar_component_clause,[],[f235])).
% 0.20/0.50  fof(f288,plain,(
% 0.20/0.50    spl5_24 | ~spl5_8 | ~spl5_18),
% 0.20/0.50    inference(avatar_split_clause,[],[f228,f218,f113,f286])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    spl5_8 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.50  fof(f218,plain,(
% 0.20/0.50    spl5_18 <=> ! [X1,X0,X2] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.50  fof(f228,plain,(
% 0.20/0.50    ( ! [X0,X1] : (X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) ) | (~spl5_8 | ~spl5_18)),
% 0.20/0.50    inference(resolution,[],[f219,f115])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl5_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f113])).
% 0.20/0.50  fof(f219,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) ) | ~spl5_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f218])).
% 0.20/0.50  fof(f242,plain,(
% 0.20/0.50    spl5_22 | ~spl5_7 | ~spl5_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f227,f222,f108,f239])).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    spl5_19 <=> ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.50  fof(f227,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_7 | ~spl5_19)),
% 0.20/0.50    inference(resolution,[],[f223,f110])).
% 0.20/0.50  fof(f223,plain,(
% 0.20/0.50    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f222])).
% 0.20/0.50  fof(f237,plain,(
% 0.20/0.50    spl5_21 | ~spl5_8 | ~spl5_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f212,f204,f113,f235])).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    spl5_15 <=> ! [X1,X0,X2] : (~m2_orders_2(X0,sK0,X1) | ~m2_orders_2(X2,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~r1_xboole_0(X2,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X0,X1)) ) | (~spl5_8 | ~spl5_15)),
% 0.20/0.50    inference(resolution,[],[f205,f115])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X2,sK0,X1) | ~m2_orders_2(X0,sK0,X1) | ~r1_xboole_0(X2,X0)) ) | ~spl5_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f204])).
% 0.20/0.50  fof(f233,plain,(
% 0.20/0.50    spl5_20 | ~spl5_6 | ~spl5_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f226,f222,f103,f230])).
% 0.20/0.50  fof(f226,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_6 | ~spl5_19)),
% 0.20/0.50    inference(resolution,[],[f223,f105])).
% 0.20/0.50  fof(f224,plain,(
% 0.20/0.50    spl5_19 | ~spl5_8 | ~spl5_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f197,f192,f113,f222])).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    spl5_13 <=> ! [X1,X0] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_8 | ~spl5_13)),
% 0.20/0.50    inference(resolution,[],[f193,f115])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,X1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f192])).
% 0.20/0.50  fof(f220,plain,(
% 0.20/0.50    spl5_18 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f181,f98,f93,f88,f83,f78,f218])).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f180,f80])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f179,f85])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f178,f90])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f177,f95])).
% 0.20/0.50  fof(f177,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_5),
% 0.20/0.50    inference(resolution,[],[f58,f100])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_orders_2(X2,X0,X3) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).
% 0.20/0.50  fof(f206,plain,(
% 0.20/0.50    spl5_15 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f164,f98,f93,f88,f83,f78,f204])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m2_orders_2(X2,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~r1_xboole_0(X2,X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f163,f80])).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m2_orders_2(X2,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~r1_xboole_0(X2,X0) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f162,f85])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m2_orders_2(X2,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~r1_xboole_0(X2,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f161,f90])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m2_orders_2(X2,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~r1_xboole_0(X2,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f160,f95])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m2_orders_2(X2,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~r1_xboole_0(X2,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_5),
% 0.20/0.50    inference(resolution,[],[f56,f100])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~r1_xboole_0(X2,X3) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).
% 0.20/0.50  fof(f194,plain,(
% 0.20/0.50    spl5_13 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f156,f98,f93,f88,f83,f78,f192])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f155,f80])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f154,f85])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f153,f90])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f152,f95])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_5),
% 0.20/0.50    inference(resolution,[],[f65,f100])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    ~spl5_9 | ~spl5_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f126,f122,f118])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    ~r2_xboole_0(sK2,sK3) | ~spl5_10),
% 0.20/0.50    inference(subsumption_resolution,[],[f54,f124])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f36,f35,f34,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) => (? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) => ((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f12])).
% 0.20/0.50  fof(f12,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    spl5_9 | spl5_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f53,f122,f118])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    spl5_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f50,f113])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    spl5_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f52,f108])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    m2_orders_2(sK3,sK0,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    spl5_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f51,f103])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    m2_orders_2(sK2,sK0,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    spl5_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f49,f98])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    l1_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    spl5_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f48,f93])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    v5_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    spl5_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f47,f88])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    v4_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    spl5_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f46,f83])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    v3_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ~spl5_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f45,f78])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (23478)------------------------------
% 0.20/0.50  % (23478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23478)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (23478)Memory used [KB]: 6396
% 0.20/0.51  % (23478)Time elapsed: 0.055 s
% 0.20/0.51  % (23478)------------------------------
% 0.20/0.51  % (23478)------------------------------
% 0.20/0.51  % (23487)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (23477)Refutation not found, incomplete strategy% (23477)------------------------------
% 0.20/0.51  % (23477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23477)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (23477)Memory used [KB]: 10746
% 0.20/0.51  % (23477)Time elapsed: 0.088 s
% 0.20/0.51  % (23477)------------------------------
% 0.20/0.51  % (23477)------------------------------
% 0.20/0.51  % (23473)Success in time 0.146 s
%------------------------------------------------------------------------------
