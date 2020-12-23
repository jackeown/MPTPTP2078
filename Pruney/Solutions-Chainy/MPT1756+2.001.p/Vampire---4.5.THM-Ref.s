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
% DateTime   : Thu Dec  3 13:18:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 367 expanded)
%              Number of leaves         :   26 ( 106 expanded)
%              Depth                    :   26
%              Number of atoms          : 1270 (3357 expanded)
%              Number of equality atoms :   12 ( 103 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f346,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f76,f81,f86,f91,f96,f101,f106,f161,f166,f176,f181,f186,f191,f197,f202,f207,f216,f220,f282,f341])).

fof(f341,plain,
    ( spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_20 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f339,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f339,plain,
    ( ~ r1_tarski(sK4,sK4)
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f337,f180])).

fof(f180,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl9_13
  <=> r1_tarski(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f337,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ r1_tarski(sK4,sK4)
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_20 ),
    inference(resolution,[],[f302,f196])).

fof(f196,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl9_16
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f302,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ r1_tarski(sK4,X0) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_20 ),
    inference(resolution,[],[f301,f238])).

fof(f238,plain,
    ( ! [X0] :
        ( m1_connsp_2(X0,sK1,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(sK4,X0) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f237,f196])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | m1_connsp_2(X0,sK1,sK5)
        | ~ r1_tarski(sK4,X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f236,f160])).

fof(f160,plain,
    ( v3_pre_topc(sK4,sK1)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl9_9
  <=> v3_pre_topc(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | m1_connsp_2(X0,sK1,sK5)
        | ~ v3_pre_topc(sK4,sK1)
        | ~ r1_tarski(sK4,X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | m1_connsp_2(X0,sK1,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(sK4,sK1)
        | ~ r1_tarski(sK4,X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(resolution,[],[f232,f133])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k1_tops_1(sK1,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X0,sK1)
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl9_5 ),
    inference(resolution,[],[f90,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f90,plain,
    ( l1_pre_topc(sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl9_5
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK4,k1_tops_1(sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | m1_connsp_2(X0,sK1,sK5) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(resolution,[],[f231,f165])).

fof(f165,plain,
    ( r2_hidden(sK5,sK4)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl9_10
  <=> r2_hidden(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5,X1)
        | m1_connsp_2(X0,sK1,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X1,k1_tops_1(sK1,X0)) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_14 ),
    inference(resolution,[],[f230,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f230,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,k1_tops_1(sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | m1_connsp_2(X0,sK1,sK5) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_14 ),
    inference(resolution,[],[f129,f185])).

fof(f185,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl9_14
  <=> m1_subset_1(sK5,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f129,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK1))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(X8,k1_tops_1(sK1,X9))
        | m1_connsp_2(X9,sK1,X8) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f128,f90])).

fof(f128,plain,
    ( ! [X8,X9] :
        ( ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(X8,k1_tops_1(sK1,X9))
        | m1_connsp_2(X9,sK1,X8) )
    | spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f115,f80])).

fof(f80,plain,
    ( ~ v2_struct_0(sK1)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl9_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f115,plain,
    ( ! [X8,X9] :
        ( v2_struct_0(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(X8,k1_tops_1(sK1,X9))
        | m1_connsp_2(X9,sK1,X8) )
    | ~ spl9_4 ),
    inference(resolution,[],[f85,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f85,plain,
    ( v2_pre_topc(sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl9_4
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f301,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK1,sK5)
        | ~ r1_tarski(X0,u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f300,f214])).

fof(f214,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl9_20
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f300,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19 ),
    inference(subsumption_resolution,[],[f299,f190])).

fof(f190,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl9_15
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19 ),
    inference(subsumption_resolution,[],[f298,f70])).

fof(f70,plain,
    ( ~ v2_struct_0(sK3)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl9_1
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f298,plain,
    ( ! [X0] :
        ( v2_struct_0(sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19 ),
    inference(resolution,[],[f297,f175])).

fof(f175,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl9_12
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f297,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,sK5)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19 ),
    inference(subsumption_resolution,[],[f296,f100])).

fof(f100,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl9_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f296,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,sK5)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19 ),
    inference(subsumption_resolution,[],[f295,f185])).

fof(f295,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,sK5)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19 ),
    inference(subsumption_resolution,[],[f294,f206])).

fof(f206,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl9_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f294,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,sK5)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8
    | ~ spl9_17
    | spl9_19 ),
    inference(subsumption_resolution,[],[f293,f201])).

fof(f201,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl9_17
  <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f293,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,sK5)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8
    | spl9_19 ),
    inference(subsumption_resolution,[],[f292,f95])).

fof(f95,plain,
    ( ~ v2_struct_0(sK0)
    | spl9_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl9_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f292,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,sK5)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_8
    | spl9_19 ),
    inference(subsumption_resolution,[],[f291,f90])).

fof(f291,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,sK5)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | spl9_19 ),
    inference(subsumption_resolution,[],[f290,f85])).

fof(f290,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,sK5)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_8
    | spl9_19 ),
    inference(subsumption_resolution,[],[f289,f80])).

fof(f289,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,sK5)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_2
    | ~ spl9_8
    | spl9_19 ),
    inference(subsumption_resolution,[],[f288,f105])).

fof(f105,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl9_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f288,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,sK5)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_2
    | spl9_19 ),
    inference(resolution,[],[f211,f109])).

fof(f109,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( r1_tmap_1(X1,X0,sK2,X4)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_subset_1(X4,u1_struct_0(X1))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tarski(X3,u1_struct_0(X2))
        | ~ m1_connsp_2(X3,X1,X4)
        | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f107,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f107,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X4,u1_struct_0(X1))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tarski(X3,u1_struct_0(X2))
        | ~ m1_connsp_2(X3,X1,X4)
        | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4)
        | r1_tmap_1(X1,X0,sK2,X4) )
    | ~ spl9_2 ),
    inference(resolution,[],[f75,f61])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X5)
      | X5 != X6
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

fof(f75,plain,
    ( v1_funct_1(sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl9_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f211,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl9_19 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl9_19
  <=> r1_tmap_1(sK1,sK0,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f282,plain,
    ( spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_20 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_20 ),
    inference(subsumption_resolution,[],[f280,f63])).

fof(f280,plain,
    ( ~ r1_tarski(sK4,sK4)
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_20 ),
    inference(subsumption_resolution,[],[f278,f180])).

fof(f278,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ r1_tarski(sK4,sK4)
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_20 ),
    inference(resolution,[],[f275,f196])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ r1_tarski(sK4,X0) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_20 ),
    inference(resolution,[],[f274,f238])).

fof(f274,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK1,sK5)
        | ~ r1_tarski(X0,u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_20 ),
    inference(subsumption_resolution,[],[f273,f210])).

fof(f210,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f209])).

fof(f273,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | ~ r1_tmap_1(sK1,sK0,sK2,sK5) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | spl9_20 ),
    inference(subsumption_resolution,[],[f272,f185])).

fof(f272,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ r1_tmap_1(sK1,sK0,sK2,sK5) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | spl9_20 ),
    inference(subsumption_resolution,[],[f271,f190])).

fof(f271,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ r1_tmap_1(sK1,sK0,sK2,sK5) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_18
    | spl9_20 ),
    inference(resolution,[],[f268,f215])).

fof(f215,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | spl9_20 ),
    inference(avatar_component_clause,[],[f213])).

fof(f268,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tarski(X1,u1_struct_0(sK3))
        | ~ m1_connsp_2(X1,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_tmap_1(sK1,sK0,sK2,X0) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f267,f70])).

fof(f267,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tarski(X1,u1_struct_0(sK3))
        | ~ m1_connsp_2(X1,sK1,X0)
        | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | ~ r1_tmap_1(sK1,sK0,sK2,X0) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(resolution,[],[f253,f175])).

fof(f253,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,sK1,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | ~ r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f252,f206])).

fof(f252,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,sK1,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | ~ r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f251,f100])).

fof(f251,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,sK1,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | ~ r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f250,f95])).

fof(f250,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,sK1,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | ~ r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f249,f90])).

fof(f249,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,sK1,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | ~ r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f248,f85])).

fof(f248,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,sK1,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | ~ r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f247,f80])).

fof(f247,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,sK1,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | ~ r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f246,f105])).

fof(f246,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,sK1,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | ~ r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | ~ spl9_17 ),
    inference(resolution,[],[f110,f201])).

fof(f110,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(X5))
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X5))))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X6)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ r1_tarski(X8,u1_struct_0(X7))
        | ~ m1_connsp_2(X8,X6,X9)
        | r1_tmap_1(X7,X5,k2_tmap_1(X6,X5,sK2,X7),X9)
        | ~ r1_tmap_1(X6,X5,sK2,X9) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f108,f53])).

fof(f108,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(X5)
        | ~ v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(X5))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X5))))
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ r1_tarski(X8,u1_struct_0(X7))
        | ~ m1_connsp_2(X8,X6,X9)
        | r1_tmap_1(X7,X5,k2_tmap_1(X6,X5,sK2,X7),X9)
        | ~ r1_tmap_1(X6,X5,sK2,X9) )
    | ~ spl9_2 ),
    inference(resolution,[],[f75,f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X5)
      | X5 != X6
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f220,plain,
    ( spl9_19
    | spl9_20 ),
    inference(avatar_split_clause,[],[f219,f213,f209])).

fof(f219,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl9_20 ),
    inference(subsumption_resolution,[],[f66,f215])).

fof(f66,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(forward_demodulation,[],[f23,f29])).

fof(f29,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ( ( X5 = X6
                                    & r1_tarski(X4,u1_struct_0(X3))
                                    & r2_hidden(X5,X4)
                                    & v3_pre_topc(X4,X1) )
                                 => ( r1_tmap_1(X1,X0,X2,X5)
                                  <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & r1_tarski(X4,u1_struct_0(X3))
                                  & r2_hidden(X5,X4)
                                  & v3_pre_topc(X4,X1) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

fof(f23,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f11])).

fof(f216,plain,
    ( ~ spl9_19
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f65,f213,f209])).

fof(f65,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(forward_demodulation,[],[f24,f29])).

fof(f24,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f11])).

fof(f207,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f36,f204])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f11])).

fof(f202,plain,(
    spl9_17 ),
    inference(avatar_split_clause,[],[f35,f199])).

fof(f35,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f197,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f31,f194])).

fof(f31,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f191,plain,(
    spl9_15 ),
    inference(avatar_split_clause,[],[f64,f188])).

fof(f64,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f25,f29])).

fof(f25,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f186,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f30,f183])).

fof(f30,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f181,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f28,f178])).

fof(f28,plain,(
    r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f176,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f33,f173])).

fof(f33,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f166,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f27,f163])).

fof(f27,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f11])).

fof(f161,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f26,f158])).

fof(f26,plain,(
    v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f106,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f42,f103])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f101,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f41,f98])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f96,plain,(
    ~ spl9_6 ),
    inference(avatar_split_clause,[],[f40,f93])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f91,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f39,f88])).

fof(f39,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f86,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f38,f83])).

fof(f38,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f81,plain,(
    ~ spl9_3 ),
    inference(avatar_split_clause,[],[f37,f78])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f34,f73])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f71,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f32,f68])).

fof(f32,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:24:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (28921)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.49  % (28921)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f346,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f71,f76,f81,f86,f91,f96,f101,f106,f161,f166,f176,f181,f186,f191,f197,f202,f207,f216,f220,f282,f341])).
% 0.21/0.49  fof(f341,plain,(
% 0.21/0.49    spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_12 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_20),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f340])).
% 0.21/0.49  fof(f340,plain,(
% 0.21/0.49    $false | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_12 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f339,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f339,plain,(
% 0.21/0.49    ~r1_tarski(sK4,sK4) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_12 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f337,f180])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    r1_tarski(sK4,u1_struct_0(sK3)) | ~spl9_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f178])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    spl9_13 <=> r1_tarski(sK4,u1_struct_0(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.21/0.49  fof(f337,plain,(
% 0.21/0.49    ~r1_tarski(sK4,u1_struct_0(sK3)) | ~r1_tarski(sK4,sK4) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_12 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_20)),
% 0.21/0.49    inference(resolution,[],[f302,f196])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl9_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f194])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    spl9_16 <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.50  fof(f302,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~r1_tarski(sK4,X0)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_12 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_20)),
% 0.21/0.50    inference(resolution,[],[f301,f238])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    ( ! [X0] : (m1_connsp_2(X0,sK1,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(sK4,X0)) ) | (spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_16)),
% 0.21/0.50    inference(subsumption_resolution,[],[f237,f196])).
% 0.21/0.50  fof(f237,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_connsp_2(X0,sK1,sK5) | ~r1_tarski(sK4,X0) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) ) | (spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_9 | ~spl9_10 | ~spl9_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f236,f160])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    v3_pre_topc(sK4,sK1) | ~spl9_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f158])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    spl9_9 <=> v3_pre_topc(sK4,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_connsp_2(X0,sK1,sK5) | ~v3_pre_topc(sK4,sK1) | ~r1_tarski(sK4,X0) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) ) | (spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_10 | ~spl9_14)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f235])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_connsp_2(X0,sK1,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(sK4,sK1) | ~r1_tarski(sK4,X0) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) ) | (spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_10 | ~spl9_14)),
% 0.21/0.50    inference(resolution,[],[f232,f133])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,k1_tops_1(sK1,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) ) | ~spl9_5),
% 0.21/0.50    inference(resolution,[],[f90,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    l1_pre_topc(sK1) | ~spl9_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    spl9_5 <=> l1_pre_topc(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(sK4,k1_tops_1(sK1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_connsp_2(X0,sK1,sK5)) ) | (spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_10 | ~spl9_14)),
% 0.21/0.50    inference(resolution,[],[f231,f165])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    r2_hidden(sK5,sK4) | ~spl9_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f163])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    spl9_10 <=> r2_hidden(sK5,sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK5,X1) | m1_connsp_2(X0,sK1,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X1,k1_tops_1(sK1,X0))) ) | (spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_14)),
% 0.21/0.50    inference(resolution,[],[f230,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK5,k1_tops_1(sK1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_connsp_2(X0,sK1,sK5)) ) | (spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_14)),
% 0.21/0.50    inference(resolution,[],[f129,f185])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    m1_subset_1(sK5,u1_struct_0(sK1)) | ~spl9_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f183])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    spl9_14 <=> m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ( ! [X8,X9] : (~m1_subset_1(X8,u1_struct_0(sK1)) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(X8,k1_tops_1(sK1,X9)) | m1_connsp_2(X9,sK1,X8)) ) | (spl9_3 | ~spl9_4 | ~spl9_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f128,f90])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ( ! [X8,X9] : (~l1_pre_topc(sK1) | ~m1_subset_1(X8,u1_struct_0(sK1)) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(X8,k1_tops_1(sK1,X9)) | m1_connsp_2(X9,sK1,X8)) ) | (spl9_3 | ~spl9_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f115,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~v2_struct_0(sK1) | spl9_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    spl9_3 <=> v2_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ( ! [X8,X9] : (v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(X8,u1_struct_0(sK1)) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(X8,k1_tops_1(sK1,X9)) | m1_connsp_2(X9,sK1,X8)) ) | ~spl9_4),
% 0.21/0.50    inference(resolution,[],[f85,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    v2_pre_topc(sK1) | ~spl9_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    spl9_4 <=> v2_pre_topc(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.50  fof(f301,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_connsp_2(X0,sK1,sK5) | ~r1_tarski(X0,u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_14 | ~spl9_15 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f300,f214])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~spl9_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f213])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    spl9_20 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.21/0.50  fof(f300,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_14 | ~spl9_15 | ~spl9_17 | ~spl9_18 | spl9_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f299,f190])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl9_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f188])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    spl9_15 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_14 | ~spl9_17 | ~spl9_18 | spl9_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f298,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ~v2_struct_0(sK3) | spl9_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    spl9_1 <=> v2_struct_0(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.50  fof(f298,plain,(
% 0.21/0.50    ( ! [X0] : (v2_struct_0(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_14 | ~spl9_17 | ~spl9_18 | spl9_19)),
% 0.21/0.50    inference(resolution,[],[f297,f175])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    m1_pre_topc(sK3,sK1) | ~spl9_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f173])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    spl9_12 <=> m1_pre_topc(sK3,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.21/0.50  fof(f297,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_14 | ~spl9_17 | ~spl9_18 | spl9_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f296,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    v2_pre_topc(sK0) | ~spl9_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl9_7 <=> v2_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_8 | ~spl9_14 | ~spl9_17 | ~spl9_18 | spl9_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f295,f185])).
% 0.21/0.50  fof(f295,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_8 | ~spl9_17 | ~spl9_18 | spl9_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f294,f206])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl9_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f204])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    spl9_18 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_8 | ~spl9_17 | spl9_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f293,f201])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl9_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f199])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    spl9_17 <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.21/0.50  fof(f293,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_8 | spl9_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f292,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ~v2_struct_0(sK0) | spl9_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f93])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    spl9_6 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_8 | spl9_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f291,f90])).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_8 | spl9_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f290,f85])).
% 0.21/0.50  fof(f290,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) ) | (~spl9_2 | spl9_3 | ~spl9_8 | spl9_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f289,f80])).
% 0.21/0.50  fof(f289,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) ) | (~spl9_2 | ~spl9_8 | spl9_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f288,f105])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    l1_pre_topc(sK0) | ~spl9_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    spl9_8 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~v2_pre_topc(sK0)) ) | (~spl9_2 | spl9_19)),
% 0.21/0.50    inference(resolution,[],[f211,f109])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,sK2,X4) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tarski(X3,u1_struct_0(X2)) | ~m1_connsp_2(X3,X1,X4) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4) | ~v2_pre_topc(X0)) ) | ~spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f107,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tarski(X3,u1_struct_0(X2)) | ~m1_connsp_2(X3,X1,X4) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4) | r1_tmap_1(X1,X0,sK2,X4)) ) | ~spl9_2),
% 0.21/0.50    inference(resolution,[],[f75,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.21/0.50    inference(equality_resolution,[],[f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    v1_funct_1(sK2) | ~spl9_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    spl9_2 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    ~r1_tmap_1(sK1,sK0,sK2,sK5) | spl9_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f209])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    spl9_19 <=> r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_12 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_20),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f281])).
% 0.21/0.50  fof(f281,plain,(
% 0.21/0.50    $false | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_12 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f280,f63])).
% 0.21/0.50  fof(f280,plain,(
% 0.21/0.50    ~r1_tarski(sK4,sK4) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_12 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f278,f180])).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    ~r1_tarski(sK4,u1_struct_0(sK3)) | ~r1_tarski(sK4,sK4) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_12 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_20)),
% 0.21/0.50    inference(resolution,[],[f275,f196])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~r1_tarski(sK4,X0)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_12 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_20)),
% 0.21/0.50    inference(resolution,[],[f274,f238])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_connsp_2(X0,sK1,sK5) | ~r1_tarski(X0,u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_14 | ~spl9_15 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f273,f210])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    r1_tmap_1(sK1,sK0,sK2,sK5) | ~spl9_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f209])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK5)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_14 | ~spl9_15 | ~spl9_17 | ~spl9_18 | spl9_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f272,f185])).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_tmap_1(sK1,sK0,sK2,sK5)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_15 | ~spl9_17 | ~spl9_18 | spl9_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f271,f190])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_tmap_1(sK1,sK0,sK2,sK5)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_17 | ~spl9_18 | spl9_20)),
% 0.21/0.50    inference(resolution,[],[f268,f215])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | spl9_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f213])).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_tmap_1(sK1,sK0,sK2,X0)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_17 | ~spl9_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f267,f70])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(sK3) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK1,X0) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | ~r1_tmap_1(sK1,sK0,sK2,X0)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_17 | ~spl9_18)),
% 0.21/0.50    inference(resolution,[],[f253,f175])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_connsp_2(X2,sK1,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | ~r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_17 | ~spl9_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f252,f206])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_connsp_2(X2,sK1,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | ~r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_17)),
% 0.21/0.50    inference(subsumption_resolution,[],[f251,f100])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_connsp_2(X2,sK1,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | ~r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_8 | ~spl9_17)),
% 0.21/0.50    inference(subsumption_resolution,[],[f250,f95])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_connsp_2(X2,sK1,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | ~r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_8 | ~spl9_17)),
% 0.21/0.50    inference(subsumption_resolution,[],[f249,f90])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_connsp_2(X2,sK1,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | ~r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_17)),
% 0.21/0.50    inference(subsumption_resolution,[],[f248,f85])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_connsp_2(X2,sK1,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | ~r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | spl9_3 | ~spl9_8 | ~spl9_17)),
% 0.21/0.50    inference(subsumption_resolution,[],[f247,f80])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_connsp_2(X2,sK1,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | ~r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | ~spl9_8 | ~spl9_17)),
% 0.21/0.50    inference(subsumption_resolution,[],[f246,f105])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_connsp_2(X2,sK1,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | ~r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | ~spl9_17)),
% 0.21/0.50    inference(resolution,[],[f110,f201])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(X5)) | ~l1_pre_topc(X5) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X5)))) | v2_struct_0(X7) | ~m1_pre_topc(X7,X6) | ~m1_subset_1(X9,u1_struct_0(X6)) | ~m1_subset_1(X9,u1_struct_0(X7)) | ~r1_tarski(X8,u1_struct_0(X7)) | ~m1_connsp_2(X8,X6,X9) | r1_tmap_1(X7,X5,k2_tmap_1(X6,X5,sK2,X7),X9) | ~r1_tmap_1(X6,X5,sK2,X9)) ) | ~spl9_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f108,f53])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    ( ! [X6,X8,X7,X5,X9] : (~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(X5) | ~v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(X5)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X5)))) | v2_struct_0(X7) | ~m1_pre_topc(X7,X6) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6))) | ~m1_subset_1(X9,u1_struct_0(X6)) | ~m1_subset_1(X9,u1_struct_0(X7)) | ~r1_tarski(X8,u1_struct_0(X7)) | ~m1_connsp_2(X8,X6,X9) | r1_tmap_1(X7,X5,k2_tmap_1(X6,X5,sK2,X7),X9) | ~r1_tmap_1(X6,X5,sK2,X9)) ) | ~spl9_2),
% 0.21/0.50    inference(resolution,[],[f75,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6)) )),
% 0.21/0.50    inference(equality_resolution,[],[f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    spl9_19 | spl9_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f219,f213,f209])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    r1_tmap_1(sK1,sK0,sK2,sK5) | spl9_20),
% 0.21/0.50    inference(subsumption_resolution,[],[f66,f215])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.50    inference(forward_demodulation,[],[f23,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    sK5 = sK6),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f8])).
% 0.21/0.50  fof(f8,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    ~spl9_19 | ~spl9_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f65,f213,f209])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.50    inference(forward_demodulation,[],[f24,f29])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    spl9_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f36,f204])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    spl9_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f35,f199])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    spl9_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f31,f194])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    spl9_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f64,f188])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.50    inference(forward_demodulation,[],[f25,f29])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    spl9_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f183])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    spl9_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f178])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    r1_tarski(sK4,u1_struct_0(sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    spl9_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f173])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    m1_pre_topc(sK3,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    spl9_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f163])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    r2_hidden(sK5,sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    spl9_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f26,f158])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    v3_pre_topc(sK4,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl9_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f103])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl9_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f98])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ~spl9_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f40,f93])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl9_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f39,f88])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    l1_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    spl9_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f83])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    v2_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ~spl9_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f37,f78])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl9_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f73])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ~spl9_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f32,f68])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ~v2_struct_0(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (28921)------------------------------
% 0.21/0.50  % (28921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28921)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (28921)Memory used [KB]: 11129
% 0.21/0.50  % (28921)Time elapsed: 0.087 s
% 0.21/0.50  % (28921)------------------------------
% 0.21/0.50  % (28921)------------------------------
% 0.21/0.50  % (28900)Success in time 0.137 s
%------------------------------------------------------------------------------
