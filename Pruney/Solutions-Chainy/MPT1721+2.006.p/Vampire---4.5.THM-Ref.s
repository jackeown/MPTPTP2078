%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 295 expanded)
%              Number of leaves         :   32 ( 147 expanded)
%              Depth                    :   11
%              Number of atoms          :  570 (2490 expanded)
%              Number of equality atoms :   28 (  39 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f59,f63,f67,f71,f75,f79,f83,f87,f91,f95,f99,f103,f125,f136,f142,f145,f150,f217,f224,f235,f238])).

fof(f238,plain,
    ( spl4_13
    | ~ spl4_11
    | spl4_10
    | ~ spl4_9
    | spl4_8
    | ~ spl4_7
    | spl4_34 ),
    inference(avatar_split_clause,[],[f236,f232,f77,f81,f85,f89,f93,f101])).

fof(f101,plain,
    ( spl4_13
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f93,plain,
    ( spl4_11
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f89,plain,
    ( spl4_10
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f85,plain,
    ( spl4_9
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f81,plain,
    ( spl4_8
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f77,plain,
    ( spl4_7
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f232,plain,
    ( spl4_34
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f236,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_34 ),
    inference(resolution,[],[f233,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f233,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_34 ),
    inference(avatar_component_clause,[],[f232])).

fof(f235,plain,
    ( ~ spl4_34
    | ~ spl4_11
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f230,f221,f97,f69,f93,f232])).

fof(f69,plain,
    ( spl4_5
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f97,plain,
    ( spl4_12
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f221,plain,
    ( spl4_32
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f230,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl4_12
    | ~ spl4_32 ),
    inference(resolution,[],[f222,f98])).

fof(f98,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) )
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f221])).

fof(f224,plain,
    ( spl4_32
    | spl4_1
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f218,f215,f53,f221])).

fof(f53,plain,
    ( spl4_1
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f215,plain,
    ( spl4_31
  <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f218,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_31 ),
    inference(resolution,[],[f216,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f216,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f215])).

fof(f217,plain,
    ( spl4_6
    | spl4_10
    | ~ spl4_4
    | spl4_8
    | ~ spl4_3
    | spl4_31
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f213,f147,f133,f215,f61,f81,f65,f89,f73])).

fof(f73,plain,
    ( spl4_6
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f65,plain,
    ( spl4_4
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f61,plain,
    ( spl4_3
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f133,plain,
    ( spl4_17
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f147,plain,
    ( spl4_19
  <=> u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f213,plain,
    ( ~ l1_pre_topc(sK3)
    | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ spl4_19 ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,
    ( ~ l1_pre_topc(sK3)
    | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl4_19 ),
    inference(resolution,[],[f156,f50])).

fof(f156,plain,
    ( ! [X7] :
        ( ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X7)
        | ~ l1_pre_topc(X7)
        | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X7)) )
    | ~ spl4_19 ),
    inference(superposition,[],[f107,f148])).

fof(f148,plain,
    ( u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f147])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f41,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f150,plain,
    ( spl4_19
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f149,f138,f129,f147])).

fof(f129,plain,
    ( spl4_16
  <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f138,plain,
    ( spl4_18
  <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f149,plain,
    ( u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f130,f139])).

fof(f139,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f138])).

fof(f130,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f129])).

fof(f145,plain,
    ( ~ spl4_11
    | ~ spl4_5
    | spl4_17 ),
    inference(avatar_split_clause,[],[f144,f133,f69,f93])).

fof(f144,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_5
    | spl4_17 ),
    inference(resolution,[],[f143,f70])).

fof(f70,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl4_17 ),
    inference(resolution,[],[f134,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f134,plain,
    ( ~ l1_pre_topc(sK3)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f133])).

fof(f142,plain,
    ( spl4_18
    | ~ spl4_9
    | ~ spl4_11
    | spl4_13
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f127,f123,f77,f101,f93,f85,f138])).

fof(f123,plain,
    ( spl4_15
  <=> ! [X0] :
        ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f127,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(resolution,[],[f124,f78])).

fof(f78,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2)) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f136,plain,
    ( spl4_16
    | ~ spl4_4
    | ~ spl4_17
    | spl4_6
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f126,f123,f61,f73,f133,f65,f129])).

fof(f126,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ m1_pre_topc(sK1,sK3)
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2))
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(resolution,[],[f124,f62])).

fof(f62,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f125,plain,
    ( spl4_10
    | spl4_8
    | spl4_15
    | spl4_2 ),
    inference(avatar_split_clause,[],[f119,f57,f123,f81,f89])).

fof(f57,plain,
    ( spl4_2
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f119,plain,
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
    inference(cnf_transformation,[],[f18])).

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
    inference(cnf_transformation,[],[f18])).

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
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(avatar_split_clause,[],[f27,f101])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f22,f21,f20,f19])).

fof(f19,plain,
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

fof(f20,plain,
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

fof(f21,plain,
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

fof(f22,plain,
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
    inference(avatar_split_clause,[],[f28,f97])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f95,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f29,f93])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f91,plain,(
    ~ spl4_10 ),
    inference(avatar_split_clause,[],[f30,f89])).

fof(f30,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f87,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f31,f85])).

fof(f31,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f32,f81])).

fof(f32,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f34,f73])).

fof(f34,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f35,f69])).

fof(f35,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f36,f65])).

fof(f36,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f37,f61])).

fof(f37,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f38,f57])).

fof(f38,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f39,f53])).

fof(f39,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:17:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (26334)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (26345)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (26335)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (26343)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (26335)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f239,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f55,f59,f63,f67,f71,f75,f79,f83,f87,f91,f95,f99,f103,f125,f136,f142,f145,f150,f217,f224,f235,f238])).
% 0.22/0.49  fof(f238,plain,(
% 0.22/0.49    spl4_13 | ~spl4_11 | spl4_10 | ~spl4_9 | spl4_8 | ~spl4_7 | spl4_34),
% 0.22/0.49    inference(avatar_split_clause,[],[f236,f232,f77,f81,f85,f89,f93,f101])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    spl4_13 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl4_11 <=> l1_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl4_10 <=> v2_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl4_9 <=> m1_pre_topc(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    spl4_8 <=> v2_struct_0(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl4_7 <=> m1_pre_topc(sK2,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.49  fof(f232,plain,(
% 0.22/0.49    spl4_34 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.22/0.49  fof(f236,plain,(
% 0.22/0.49    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_34),
% 0.22/0.49    inference(resolution,[],[f233,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | spl4_34),
% 0.22/0.49    inference(avatar_component_clause,[],[f232])).
% 0.22/0.49  fof(f235,plain,(
% 0.22/0.49    ~spl4_34 | ~spl4_11 | ~spl4_5 | ~spl4_12 | ~spl4_32),
% 0.22/0.49    inference(avatar_split_clause,[],[f230,f221,f97,f69,f93,f232])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl4_5 <=> m1_pre_topc(sK3,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    spl4_12 <=> v2_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    spl4_32 <=> ! [X0] : (~m1_pre_topc(sK3,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | (~spl4_12 | ~spl4_32)),
% 0.22/0.49    inference(resolution,[],[f222,f98])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    v2_pre_topc(sK0) | ~spl4_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f97])).
% 0.22/0.49  fof(f222,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)) ) | ~spl4_32),
% 0.22/0.49    inference(avatar_component_clause,[],[f221])).
% 0.22/0.49  fof(f224,plain,(
% 0.22/0.49    spl4_32 | spl4_1 | ~spl4_31),
% 0.22/0.49    inference(avatar_split_clause,[],[f218,f215,f53,f221])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    spl4_1 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    spl4_31 <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    ( ! [X0] : (m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl4_31),
% 0.22/0.49    inference(resolution,[],[f216,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) | ~spl4_31),
% 0.22/0.49    inference(avatar_component_clause,[],[f215])).
% 0.22/0.49  fof(f217,plain,(
% 0.22/0.49    spl4_6 | spl4_10 | ~spl4_4 | spl4_8 | ~spl4_3 | spl4_31 | ~spl4_17 | ~spl4_19),
% 0.22/0.49    inference(avatar_split_clause,[],[f213,f147,f133,f215,f61,f81,f65,f89,f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl4_6 <=> v2_struct_0(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl4_4 <=> m1_pre_topc(sK1,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl4_3 <=> m1_pre_topc(sK2,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    spl4_17 <=> l1_pre_topc(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    spl4_19 <=> u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    ~l1_pre_topc(sK3) | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK3) | v2_struct_0(sK1) | v2_struct_0(sK3) | ~spl4_19),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f212])).
% 0.22/0.49  fof(f212,plain,(
% 0.22/0.49    ~l1_pre_topc(sK3) | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK3) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~spl4_19),
% 0.22/0.49    inference(resolution,[],[f156,f50])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    ( ! [X7] : (~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X7) | ~l1_pre_topc(X7) | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(X7))) ) | ~spl4_19),
% 0.22/0.49    inference(superposition,[],[f107,f148])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl4_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f147])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.49    inference(resolution,[],[f41,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.49    inference(nnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    spl4_19 | ~spl4_16 | ~spl4_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f149,f138,f129,f147])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    spl4_16 <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    spl4_18 <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | (~spl4_16 | ~spl4_18)),
% 0.22/0.49    inference(forward_demodulation,[],[f130,f139])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl4_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f138])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) | ~spl4_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f129])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    ~spl4_11 | ~spl4_5 | spl4_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f144,f133,f69,f93])).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | (~spl4_5 | spl4_17)),
% 0.22/0.49    inference(resolution,[],[f143,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    m1_pre_topc(sK3,sK0) | ~spl4_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f69])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl4_17),
% 0.22/0.49    inference(resolution,[],[f134,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    ~l1_pre_topc(sK3) | spl4_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f133])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    spl4_18 | ~spl4_9 | ~spl4_11 | spl4_13 | ~spl4_7 | ~spl4_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f127,f123,f77,f101,f93,f85,f138])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    spl4_15 <=> ! [X0] : (k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2)) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK2,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | (~spl4_7 | ~spl4_15)),
% 0.22/0.49    inference(resolution,[],[f124,f78])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    m1_pre_topc(sK2,sK0) | ~spl4_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f77])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_pre_topc(sK2,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2))) ) | ~spl4_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f123])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    spl4_16 | ~spl4_4 | ~spl4_17 | spl4_6 | ~spl4_3 | ~spl4_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f126,f123,f61,f73,f133,f65,f129])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    v2_struct_0(sK3) | ~l1_pre_topc(sK3) | ~m1_pre_topc(sK1,sK3) | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) | (~spl4_3 | ~spl4_15)),
% 0.22/0.49    inference(resolution,[],[f124,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    m1_pre_topc(sK2,sK3) | ~spl4_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f61])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    spl4_10 | spl4_8 | spl4_15 | spl4_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f119,f57,f123,f81,f89])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    spl4_2 <=> r1_tsep_1(sK1,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    ( ! [X0] : (k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2)) | ~m1_pre_topc(sK2,X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | spl4_2),
% 0.22/0.49    inference(resolution,[],[f106,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ~r1_tsep_1(sK1,sK2) | spl4_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f57])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f105,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f104,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f51,f50])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ~spl4_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f27,f101])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    (((~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f22,f21,f20,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f7])).
% 0.22/0.49  fof(f7,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl4_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f97])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    v2_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl4_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f93])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ~spl4_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f89])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ~v2_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    spl4_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f85])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    m1_pre_topc(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ~spl4_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f81])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ~v2_struct_0(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl4_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f77])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    m1_pre_topc(sK2,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ~spl4_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f73])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ~v2_struct_0(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl4_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f69])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    m1_pre_topc(sK3,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    spl4_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f65])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    m1_pre_topc(sK1,sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    spl4_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f61])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ~spl4_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f38,f57])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ~r1_tsep_1(sK1,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ~spl4_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f39,f53])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (26335)------------------------------
% 0.22/0.49  % (26335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (26335)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (26335)Memory used [KB]: 10746
% 0.22/0.49  % (26335)Time elapsed: 0.014 s
% 0.22/0.49  % (26335)------------------------------
% 0.22/0.49  % (26335)------------------------------
% 0.22/0.49  % (26328)Success in time 0.13 s
%------------------------------------------------------------------------------
