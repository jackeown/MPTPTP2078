%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:55 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 206 expanded)
%              Number of leaves         :   22 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  423 ( 825 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f219,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f78,f88,f93,f98,f105,f120,f139,f146,f162,f203,f218])).

fof(f218,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl5_17 ),
    inference(resolution,[],[f206,f48])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f206,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK2,sK3))
    | spl5_17 ),
    inference(resolution,[],[f202,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f202,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl5_17
  <=> r1_tarski(sK2,k2_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f203,plain,
    ( ~ spl5_17
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_12
    | spl5_13 ),
    inference(avatar_split_clause,[],[f195,f159,f136,f95,f60,f200])).

fof(f60,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f95,plain,
    ( spl5_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f136,plain,
    ( spl5_12
  <=> m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f159,plain,
    ( spl5_13
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f195,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3))
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_12
    | spl5_13 ),
    inference(subsumption_resolution,[],[f194,f62])).

fof(f62,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f194,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_8
    | ~ spl5_12
    | spl5_13 ),
    inference(subsumption_resolution,[],[f193,f137])).

fof(f137,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f193,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_8
    | spl5_13 ),
    inference(subsumption_resolution,[],[f191,f97])).

fof(f97,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f191,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3))
    | ~ l1_pre_topc(sK0)
    | spl5_13 ),
    inference(resolution,[],[f161,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f161,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f162,plain,
    ( ~ spl5_13
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f154,f133,f85,f75,f60,f55,f50,f159])).

fof(f50,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f55,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f75,plain,
    ( spl5_4
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f85,plain,
    ( spl5_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f133,plain,
    ( spl5_11
  <=> ! [X1] :
        ( ~ r2_hidden(sK1,X1)
        | ~ r1_tarski(X1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f154,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(resolution,[],[f151,f77])).

fof(f77,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | ~ r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(resolution,[],[f134,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,k1_tops_1(sK0,X0))
        | ~ m1_connsp_2(X0,sK0,sK1) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(resolution,[],[f73,f87])).

fof(f87,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f73,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_hidden(X4,k1_tops_1(sK0,X5))
        | ~ m1_connsp_2(X5,sK0,X4) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f72,f68])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f67,f62])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_connsp_2(X1,sK0,X0)
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f64,f52])).

fof(f52,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_connsp_2(X1,sK0,X0)
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2 ),
    inference(resolution,[],[f57,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f57,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f72,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X4,k1_tops_1(sK0,X5))
        | ~ m1_connsp_2(X5,sK0,X4) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f71,f62])).

fof(f71,plain,
    ( ! [X4,X5] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X4,k1_tops_1(sK0,X5))
        | ~ m1_connsp_2(X5,sK0,X4) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f66,f52])).

fof(f66,plain,
    ( ! [X4,X5] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X4,k1_tops_1(sK0,X5))
        | ~ m1_connsp_2(X5,sK0,X4) )
    | ~ spl5_2 ),
    inference(resolution,[],[f57,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f134,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,X1)
        | ~ r1_tarski(X1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f146,plain,
    ( ~ spl5_7
    | ~ spl5_8
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_8
    | spl5_12 ),
    inference(subsumption_resolution,[],[f143,f92])).

fof(f92,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f143,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8
    | spl5_12 ),
    inference(resolution,[],[f138,f115])).

fof(f115,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f113,f97])).

fof(f113,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_8 ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_8 ),
    inference(superposition,[],[f45,f100])).

fof(f100,plain,
    ( ! [X0] :
        ( k4_subset_1(u1_struct_0(sK0),sK2,X0) = k2_xboole_0(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_8 ),
    inference(resolution,[],[f97,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f138,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f139,plain,
    ( spl5_11
    | ~ spl5_12
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_10 ),
    inference(avatar_split_clause,[],[f128,f117,f85,f60,f55,f50,f136,f133])).

fof(f117,plain,
    ( spl5_10
  <=> m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f128,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X1)
        | ~ r1_tarski(X1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_10 ),
    inference(resolution,[],[f125,f119])).

fof(f119,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f125,plain,
    ( ! [X2,X1] :
        ( m1_connsp_2(X1,sK0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X2)
        | ~ r1_tarski(X2,k1_tops_1(sK0,X1)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(resolution,[],[f121,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f121,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_connsp_2(X0,sK0,sK1) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(resolution,[],[f70,f87])).

fof(f70,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,k1_tops_1(sK0,X3))
        | m1_connsp_2(X3,sK0,X2) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f69,f62])).

fof(f69,plain,
    ( ! [X2,X3] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,k1_tops_1(sK0,X3))
        | m1_connsp_2(X3,sK0,X2) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f65,f52])).

fof(f65,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,k1_tops_1(sK0,X3))
        | m1_connsp_2(X3,sK0,X2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f57,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f120,plain,
    ( ~ spl5_10
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f114,f102,f95,f90,f117])).

fof(f102,plain,
    ( spl5_9
  <=> m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f114,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(subsumption_resolution,[],[f111,f92])).

fof(f111,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8
    | spl5_9 ),
    inference(superposition,[],[f104,f100])).

fof(f104,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f105,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f28,f102])).

fof(f28,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                     => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                   => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_connsp_2)).

fof(f98,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f29,f95])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f93,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f25,f90])).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f88,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f30,f85])).

fof(f30,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f26,f75])).

fof(f26,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f33,f60])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f32,f55])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f31,f50])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:24:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (17910)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (17907)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (17894)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (17896)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (17885)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (17886)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (17901)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (17900)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (17890)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (17908)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (17891)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.54  % (17913)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.54  % (17888)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.54  % (17889)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.54  % (17902)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.54  % (17914)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.32/0.54  % (17892)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.32/0.54  % (17906)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.32/0.55  % (17909)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.55  % (17905)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.55  % (17893)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.32/0.55  % (17897)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.55  % (17911)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.55  % (17898)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.32/0.55  % (17899)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.55  % (17905)Refutation found. Thanks to Tanya!
% 1.32/0.55  % SZS status Theorem for theBenchmark
% 1.32/0.56  % (17912)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.56  % (17904)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.51/0.57  % (17895)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.51/0.57  % (17902)Refutation not found, incomplete strategy% (17902)------------------------------
% 1.51/0.57  % (17902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (17902)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (17902)Memory used [KB]: 10618
% 1.51/0.57  % (17902)Time elapsed: 0.159 s
% 1.51/0.57  % (17902)------------------------------
% 1.51/0.57  % (17902)------------------------------
% 1.51/0.57  % SZS output start Proof for theBenchmark
% 1.51/0.57  fof(f219,plain,(
% 1.51/0.57    $false),
% 1.51/0.57    inference(avatar_sat_refutation,[],[f53,f58,f63,f78,f88,f93,f98,f105,f120,f139,f146,f162,f203,f218])).
% 1.51/0.57  fof(f218,plain,(
% 1.51/0.57    spl5_17),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f214])).
% 1.51/0.57  fof(f214,plain,(
% 1.51/0.57    $false | spl5_17),
% 1.51/0.57    inference(resolution,[],[f206,f48])).
% 1.51/0.57  fof(f48,plain,(
% 1.51/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.51/0.57    inference(equality_resolution,[],[f38])).
% 1.51/0.57  fof(f38,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.51/0.57    inference(cnf_transformation,[],[f2])).
% 1.51/0.57  fof(f2,axiom,(
% 1.51/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.51/0.57  fof(f206,plain,(
% 1.51/0.57    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK2,sK3))) ) | spl5_17),
% 1.51/0.57    inference(resolution,[],[f202,f44])).
% 1.51/0.57  fof(f44,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f20])).
% 1.51/0.57  fof(f20,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.51/0.57    inference(ennf_transformation,[],[f3])).
% 1.51/0.57  fof(f3,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.51/0.57  fof(f202,plain,(
% 1.51/0.57    ~r1_tarski(sK2,k2_xboole_0(sK2,sK3)) | spl5_17),
% 1.51/0.57    inference(avatar_component_clause,[],[f200])).
% 1.51/0.57  fof(f200,plain,(
% 1.51/0.57    spl5_17 <=> r1_tarski(sK2,k2_xboole_0(sK2,sK3))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.51/0.57  fof(f203,plain,(
% 1.51/0.57    ~spl5_17 | ~spl5_3 | ~spl5_8 | ~spl5_12 | spl5_13),
% 1.51/0.57    inference(avatar_split_clause,[],[f195,f159,f136,f95,f60,f200])).
% 1.51/0.57  fof(f60,plain,(
% 1.51/0.57    spl5_3 <=> l1_pre_topc(sK0)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.51/0.57  fof(f95,plain,(
% 1.51/0.57    spl5_8 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.51/0.57  fof(f136,plain,(
% 1.51/0.57    spl5_12 <=> m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.51/0.57  fof(f159,plain,(
% 1.51/0.57    spl5_13 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.51/0.57  fof(f195,plain,(
% 1.51/0.57    ~r1_tarski(sK2,k2_xboole_0(sK2,sK3)) | (~spl5_3 | ~spl5_8 | ~spl5_12 | spl5_13)),
% 1.51/0.57    inference(subsumption_resolution,[],[f194,f62])).
% 1.51/0.57  fof(f62,plain,(
% 1.51/0.57    l1_pre_topc(sK0) | ~spl5_3),
% 1.51/0.57    inference(avatar_component_clause,[],[f60])).
% 1.51/0.57  fof(f194,plain,(
% 1.51/0.57    ~r1_tarski(sK2,k2_xboole_0(sK2,sK3)) | ~l1_pre_topc(sK0) | (~spl5_8 | ~spl5_12 | spl5_13)),
% 1.51/0.57    inference(subsumption_resolution,[],[f193,f137])).
% 1.51/0.57  fof(f137,plain,(
% 1.51/0.57    m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_12),
% 1.51/0.57    inference(avatar_component_clause,[],[f136])).
% 1.51/0.57  fof(f193,plain,(
% 1.51/0.57    ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,k2_xboole_0(sK2,sK3)) | ~l1_pre_topc(sK0) | (~spl5_8 | spl5_13)),
% 1.51/0.57    inference(subsumption_resolution,[],[f191,f97])).
% 1.51/0.57  fof(f97,plain,(
% 1.51/0.57    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_8),
% 1.51/0.57    inference(avatar_component_clause,[],[f95])).
% 1.51/0.57  fof(f191,plain,(
% 1.51/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,k2_xboole_0(sK2,sK3)) | ~l1_pre_topc(sK0) | spl5_13),
% 1.51/0.57    inference(resolution,[],[f161,f34])).
% 1.51/0.57  fof(f34,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f14])).
% 1.51/0.57  fof(f14,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.51/0.57    inference(flattening,[],[f13])).
% 1.51/0.57  fof(f13,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.51/0.57    inference(ennf_transformation,[],[f6])).
% 1.51/0.57  fof(f6,axiom,(
% 1.51/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 1.51/0.57  fof(f161,plain,(
% 1.51/0.57    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | spl5_13),
% 1.51/0.57    inference(avatar_component_clause,[],[f159])).
% 1.51/0.57  fof(f162,plain,(
% 1.51/0.57    ~spl5_13 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_11),
% 1.51/0.57    inference(avatar_split_clause,[],[f154,f133,f85,f75,f60,f55,f50,f159])).
% 1.51/0.57  fof(f50,plain,(
% 1.51/0.57    spl5_1 <=> v2_struct_0(sK0)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.51/0.57  fof(f55,plain,(
% 1.51/0.57    spl5_2 <=> v2_pre_topc(sK0)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.51/0.57  fof(f75,plain,(
% 1.51/0.57    spl5_4 <=> m1_connsp_2(sK2,sK0,sK1)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.51/0.57  fof(f85,plain,(
% 1.51/0.57    spl5_6 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.51/0.57  fof(f133,plain,(
% 1.51/0.57    spl5_11 <=> ! [X1] : (~r2_hidden(sK1,X1) | ~r1_tarski(X1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.51/0.57  fof(f154,plain,(
% 1.51/0.57    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_11)),
% 1.51/0.57    inference(resolution,[],[f151,f77])).
% 1.51/0.57  fof(f77,plain,(
% 1.51/0.57    m1_connsp_2(sK2,sK0,sK1) | ~spl5_4),
% 1.51/0.57    inference(avatar_component_clause,[],[f75])).
% 1.51/0.57  fof(f151,plain,(
% 1.51/0.57    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | ~spl5_11)),
% 1.51/0.57    inference(resolution,[],[f134,f107])).
% 1.51/0.57  fof(f107,plain,(
% 1.51/0.57    ( ! [X0] : (r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,sK1)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6)),
% 1.51/0.57    inference(resolution,[],[f73,f87])).
% 1.51/0.57  fof(f87,plain,(
% 1.51/0.57    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_6),
% 1.51/0.57    inference(avatar_component_clause,[],[f85])).
% 1.51/0.57  fof(f73,plain,(
% 1.51/0.57    ( ! [X4,X5] : (~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X4)) ) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.51/0.57    inference(subsumption_resolution,[],[f72,f68])).
% 1.51/0.57  fof(f68,plain,(
% 1.51/0.57    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.51/0.57    inference(subsumption_resolution,[],[f67,f62])).
% 1.51/0.57  fof(f67,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2)),
% 1.51/0.57    inference(subsumption_resolution,[],[f64,f52])).
% 1.51/0.57  fof(f52,plain,(
% 1.51/0.57    ~v2_struct_0(sK0) | spl5_1),
% 1.51/0.57    inference(avatar_component_clause,[],[f50])).
% 1.51/0.57  fof(f64,plain,(
% 1.51/0.57    ( ! [X0,X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_2),
% 1.51/0.57    inference(resolution,[],[f57,f37])).
% 1.51/0.57  fof(f37,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f18])).
% 1.51/0.57  fof(f18,plain,(
% 1.51/0.57    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.51/0.57    inference(flattening,[],[f17])).
% 1.51/0.57  fof(f17,plain,(
% 1.51/0.57    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f8])).
% 1.51/0.57  fof(f8,axiom,(
% 1.51/0.57    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 1.51/0.57  fof(f57,plain,(
% 1.51/0.57    v2_pre_topc(sK0) | ~spl5_2),
% 1.51/0.57    inference(avatar_component_clause,[],[f55])).
% 1.51/0.57  fof(f72,plain,(
% 1.51/0.57    ( ! [X4,X5] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X4,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X4)) ) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.51/0.57    inference(subsumption_resolution,[],[f71,f62])).
% 1.51/0.57  fof(f71,plain,(
% 1.51/0.57    ( ! [X4,X5] : (~l1_pre_topc(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X4,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X4)) ) | (spl5_1 | ~spl5_2)),
% 1.51/0.57    inference(subsumption_resolution,[],[f66,f52])).
% 1.51/0.57  fof(f66,plain,(
% 1.51/0.57    ( ! [X4,X5] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X4,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X4)) ) | ~spl5_2),
% 1.51/0.57    inference(resolution,[],[f57,f36])).
% 1.51/0.57  fof(f36,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f16])).
% 1.51/0.57  fof(f16,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.51/0.57    inference(flattening,[],[f15])).
% 1.51/0.57  fof(f15,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f7])).
% 1.51/0.57  fof(f7,axiom,(
% 1.51/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 1.51/0.57  fof(f134,plain,(
% 1.51/0.57    ( ! [X1] : (~r2_hidden(sK1,X1) | ~r1_tarski(X1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))) ) | ~spl5_11),
% 1.51/0.57    inference(avatar_component_clause,[],[f133])).
% 1.51/0.57  fof(f146,plain,(
% 1.51/0.57    ~spl5_7 | ~spl5_8 | spl5_12),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f145])).
% 1.51/0.57  fof(f145,plain,(
% 1.51/0.57    $false | (~spl5_7 | ~spl5_8 | spl5_12)),
% 1.51/0.57    inference(subsumption_resolution,[],[f143,f92])).
% 1.51/0.57  fof(f92,plain,(
% 1.51/0.57    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_7),
% 1.51/0.57    inference(avatar_component_clause,[],[f90])).
% 1.51/0.57  fof(f90,plain,(
% 1.51/0.57    spl5_7 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.51/0.57  fof(f143,plain,(
% 1.51/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_8 | spl5_12)),
% 1.51/0.57    inference(resolution,[],[f138,f115])).
% 1.51/0.57  fof(f115,plain,(
% 1.51/0.57    ( ! [X0] : (m1_subset_1(k2_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_8),
% 1.51/0.57    inference(subsumption_resolution,[],[f113,f97])).
% 1.51/0.57  fof(f113,plain,(
% 1.51/0.57    ( ! [X0] : (m1_subset_1(k2_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_8),
% 1.51/0.57    inference(duplicate_literal_removal,[],[f112])).
% 1.51/0.57  fof(f112,plain,(
% 1.51/0.57    ( ! [X0] : (m1_subset_1(k2_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_8),
% 1.51/0.57    inference(superposition,[],[f45,f100])).
% 1.51/0.57  fof(f100,plain,(
% 1.51/0.57    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),sK2,X0) = k2_xboole_0(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_8),
% 1.51/0.57    inference(resolution,[],[f97,f46])).
% 1.51/0.57  fof(f46,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f24])).
% 1.51/0.57  fof(f24,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.51/0.57    inference(flattening,[],[f23])).
% 1.51/0.57  fof(f23,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.51/0.57    inference(ennf_transformation,[],[f5])).
% 1.51/0.57  fof(f5,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.51/0.57  fof(f45,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f22])).
% 1.51/0.57  fof(f22,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.51/0.57    inference(flattening,[],[f21])).
% 1.51/0.57  fof(f21,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.51/0.57    inference(ennf_transformation,[],[f4])).
% 1.51/0.57  fof(f4,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 1.51/0.57  fof(f138,plain,(
% 1.51/0.57    ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_12),
% 1.51/0.57    inference(avatar_component_clause,[],[f136])).
% 1.51/0.57  fof(f139,plain,(
% 1.51/0.57    spl5_11 | ~spl5_12 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | spl5_10),
% 1.51/0.57    inference(avatar_split_clause,[],[f128,f117,f85,f60,f55,f50,f136,f133])).
% 1.51/0.57  fof(f117,plain,(
% 1.51/0.57    spl5_10 <=> m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.51/0.57  fof(f128,plain,(
% 1.51/0.57    ( ! [X1] : (~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X1) | ~r1_tarski(X1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6 | spl5_10)),
% 1.51/0.57    inference(resolution,[],[f125,f119])).
% 1.51/0.57  fof(f119,plain,(
% 1.51/0.57    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) | spl5_10),
% 1.51/0.57    inference(avatar_component_clause,[],[f117])).
% 1.51/0.57  fof(f125,plain,(
% 1.51/0.57    ( ! [X2,X1] : (m1_connsp_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X2) | ~r1_tarski(X2,k1_tops_1(sK0,X1))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6)),
% 1.51/0.57    inference(resolution,[],[f121,f41])).
% 1.51/0.57  fof(f41,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f19])).
% 1.51/0.57  fof(f19,plain,(
% 1.51/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f1])).
% 1.51/0.57  fof(f1,axiom,(
% 1.51/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.51/0.57  fof(f121,plain,(
% 1.51/0.57    ( ! [X0] : (~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X0,sK0,sK1)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6)),
% 1.51/0.57    inference(resolution,[],[f70,f87])).
% 1.51/0.57  fof(f70,plain,(
% 1.51/0.57    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,k1_tops_1(sK0,X3)) | m1_connsp_2(X3,sK0,X2)) ) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 1.51/0.57    inference(subsumption_resolution,[],[f69,f62])).
% 1.51/0.57  fof(f69,plain,(
% 1.51/0.57    ( ! [X2,X3] : (~l1_pre_topc(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,k1_tops_1(sK0,X3)) | m1_connsp_2(X3,sK0,X2)) ) | (spl5_1 | ~spl5_2)),
% 1.51/0.57    inference(subsumption_resolution,[],[f65,f52])).
% 1.51/0.57  fof(f65,plain,(
% 1.51/0.57    ( ! [X2,X3] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,k1_tops_1(sK0,X3)) | m1_connsp_2(X3,sK0,X2)) ) | ~spl5_2),
% 1.51/0.57    inference(resolution,[],[f57,f35])).
% 1.51/0.57  fof(f35,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f16])).
% 1.51/0.57  fof(f120,plain,(
% 1.51/0.57    ~spl5_10 | ~spl5_7 | ~spl5_8 | spl5_9),
% 1.51/0.57    inference(avatar_split_clause,[],[f114,f102,f95,f90,f117])).
% 1.51/0.57  fof(f102,plain,(
% 1.51/0.57    spl5_9 <=> m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.51/0.57  fof(f114,plain,(
% 1.51/0.57    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) | (~spl5_7 | ~spl5_8 | spl5_9)),
% 1.51/0.57    inference(subsumption_resolution,[],[f111,f92])).
% 1.51/0.57  fof(f111,plain,(
% 1.51/0.57    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_8 | spl5_9)),
% 1.51/0.57    inference(superposition,[],[f104,f100])).
% 1.51/0.57  fof(f104,plain,(
% 1.51/0.57    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | spl5_9),
% 1.51/0.57    inference(avatar_component_clause,[],[f102])).
% 1.51/0.57  fof(f105,plain,(
% 1.51/0.57    ~spl5_9),
% 1.51/0.57    inference(avatar_split_clause,[],[f28,f102])).
% 1.51/0.57  fof(f28,plain,(
% 1.51/0.57    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)),
% 1.51/0.57    inference(cnf_transformation,[],[f12])).
% 1.51/0.57  fof(f12,plain,(
% 1.51/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.51/0.57    inference(flattening,[],[f11])).
% 1.51/0.57  fof(f11,plain,(
% 1.51/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f10])).
% 1.51/0.57  fof(f10,negated_conjecture,(
% 1.51/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 1.51/0.57    inference(negated_conjecture,[],[f9])).
% 1.51/0.57  fof(f9,conjecture,(
% 1.51/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_connsp_2)).
% 1.51/0.57  fof(f98,plain,(
% 1.51/0.57    spl5_8),
% 1.51/0.57    inference(avatar_split_clause,[],[f29,f95])).
% 1.51/0.57  fof(f29,plain,(
% 1.51/0.57    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.51/0.57    inference(cnf_transformation,[],[f12])).
% 1.51/0.57  fof(f93,plain,(
% 1.51/0.57    spl5_7),
% 1.51/0.57    inference(avatar_split_clause,[],[f25,f90])).
% 1.51/0.57  fof(f25,plain,(
% 1.51/0.57    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.51/0.57    inference(cnf_transformation,[],[f12])).
% 1.51/0.57  fof(f88,plain,(
% 1.51/0.57    spl5_6),
% 1.51/0.57    inference(avatar_split_clause,[],[f30,f85])).
% 1.51/0.57  fof(f30,plain,(
% 1.51/0.57    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.51/0.57    inference(cnf_transformation,[],[f12])).
% 1.51/0.57  fof(f78,plain,(
% 1.51/0.57    spl5_4),
% 1.51/0.57    inference(avatar_split_clause,[],[f26,f75])).
% 1.51/0.57  fof(f26,plain,(
% 1.51/0.57    m1_connsp_2(sK2,sK0,sK1)),
% 1.51/0.57    inference(cnf_transformation,[],[f12])).
% 1.51/0.57  fof(f63,plain,(
% 1.51/0.57    spl5_3),
% 1.51/0.57    inference(avatar_split_clause,[],[f33,f60])).
% 1.51/0.57  fof(f33,plain,(
% 1.51/0.57    l1_pre_topc(sK0)),
% 1.51/0.57    inference(cnf_transformation,[],[f12])).
% 1.51/0.57  fof(f58,plain,(
% 1.51/0.57    spl5_2),
% 1.51/0.57    inference(avatar_split_clause,[],[f32,f55])).
% 1.51/0.57  fof(f32,plain,(
% 1.51/0.57    v2_pre_topc(sK0)),
% 1.51/0.57    inference(cnf_transformation,[],[f12])).
% 1.51/0.57  fof(f53,plain,(
% 1.51/0.57    ~spl5_1),
% 1.51/0.57    inference(avatar_split_clause,[],[f31,f50])).
% 1.51/0.57  fof(f31,plain,(
% 1.51/0.57    ~v2_struct_0(sK0)),
% 1.51/0.57    inference(cnf_transformation,[],[f12])).
% 1.51/0.57  % SZS output end Proof for theBenchmark
% 1.51/0.57  % (17905)------------------------------
% 1.51/0.57  % (17905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (17905)Termination reason: Refutation
% 1.51/0.57  
% 1.51/0.57  % (17905)Memory used [KB]: 10874
% 1.51/0.57  % (17905)Time elapsed: 0.146 s
% 1.51/0.57  % (17905)------------------------------
% 1.51/0.57  % (17905)------------------------------
% 1.51/0.58  % (17884)Success in time 0.21 s
%------------------------------------------------------------------------------
