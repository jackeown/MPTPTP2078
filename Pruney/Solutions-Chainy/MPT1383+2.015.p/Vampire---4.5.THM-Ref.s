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
% DateTime   : Thu Dec  3 13:15:05 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 330 expanded)
%              Number of leaves         :   33 ( 154 expanded)
%              Depth                    :   10
%              Number of atoms          :  591 (2443 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f423,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f102,f107,f112,f117,f122,f129,f153,f169,f183,f214,f244,f251,f314,f344,f417])).

fof(f417,plain,
    ( spl4_42
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f416,f311,f341])).

fof(f341,plain,
    ( spl4_42
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f311,plain,
    ( spl4_37
  <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f416,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_37 ),
    inference(unit_resulting_resolution,[],[f313,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f313,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f311])).

fof(f344,plain,
    ( ~ spl4_18
    | ~ spl4_23
    | ~ spl4_42
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f339,f180,f75,f341,f200,f166])).

fof(f166,plain,
    ( spl4_18
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f200,plain,
    ( spl4_23
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f75,plain,
    ( spl4_2
  <=> ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f180,plain,
    ( spl4_20
  <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f339,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(resolution,[],[f182,f76])).

fof(f76,plain,
    ( ! [X3] :
        ( ~ v3_pre_topc(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X3)
        | ~ r1_tarski(X3,sK2) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f182,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f180])).

fof(f314,plain,
    ( spl4_37
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f297,f166,f126,f311])).

fof(f126,plain,
    ( spl4_12
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f297,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f128,f168,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f168,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f128,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f251,plain,
    ( spl4_23
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f249,f119,f114,f109,f104,f99,f71,f200])).

fof(f71,plain,
    ( spl4_1
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f99,plain,
    ( spl4_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f104,plain,
    ( spl4_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f109,plain,
    ( spl4_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f114,plain,
    ( spl4_10
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f119,plain,
    ( spl4_11
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f249,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f121,f116,f111,f106,f101,f72,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f72,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f101,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f106,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f111,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f116,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f121,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f119])).

fof(f244,plain,
    ( ~ spl4_25
    | spl4_1
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | spl4_11
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f243,f150,f119,f114,f109,f104,f99,f94,f71,f211])).

fof(f211,plain,
    ( spl4_25
  <=> m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f94,plain,
    ( spl4_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f150,plain,
    ( spl4_16
  <=> sK3 = k3_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f243,plain,
    ( ~ m1_connsp_2(sK3,sK0,sK1)
    | spl4_1
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | spl4_11
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f242,f152])).

fof(f152,plain,
    ( sK3 = k3_xboole_0(sK3,sK2)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f242,plain,
    ( ~ m1_connsp_2(k3_xboole_0(sK3,sK2),sK0,sK1)
    | spl4_1
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | spl4_11 ),
    inference(forward_demodulation,[],[f238,f176])).

fof(f176,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f101,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f238,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK3,sK2),sK0,sK1)
    | spl4_1
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f121,f116,f111,f73,f106,f96,f101,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_connsp_2(X3,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                      | ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                    & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                      | ~ m1_connsp_2(X3,X0,X1)
                      | ~ m1_connsp_2(X2,X0,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                      | ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                    & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                      | ~ m1_connsp_2(X3,X0,X1)
                      | ~ m1_connsp_2(X2,X0,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_connsp_2)).

fof(f96,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f73,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f214,plain,
    ( spl4_25
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f208,f119,f114,f109,f104,f94,f89,f79,f211])).

fof(f79,plain,
    ( spl4_3
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f89,plain,
    ( spl4_5
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f208,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f121,f116,f111,f81,f106,f91,f96,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f91,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f81,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f183,plain,
    ( spl4_20
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f178,f114,f109,f99,f180])).

fof(f178,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f116,f111,f101,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f169,plain,
    ( spl4_18
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f164,f109,f99,f166])).

fof(f164,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f111,f101,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f153,plain,
    ( spl4_16
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f142,f84,f150])).

fof(f84,plain,
    ( spl4_4
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f142,plain,
    ( sK3 = k3_xboole_0(sK3,sK2)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f86,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f86,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f129,plain,
    ( spl4_12
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f124,f99,f126])).

fof(f124,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f101,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f122,plain,(
    ~ spl4_11 ),
    inference(avatar_split_clause,[],[f45,f119])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK1,X3)
          | ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ m1_connsp_2(sK2,sK0,sK1) )
    & ( ( r2_hidden(sK1,sK3)
        & r1_tarski(sK3,sK2)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | m1_connsp_2(sK2,sK0,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f39,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | m1_connsp_2(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,sK0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ m1_connsp_2(X2,sK0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,sK0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                | m1_connsp_2(X2,sK0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,sK0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              | ~ m1_connsp_2(X2,sK0,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,sK0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
              | m1_connsp_2(X2,sK0,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(sK1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ m1_connsp_2(X2,sK0,sK1) )
          & ( ? [X4] :
                ( r2_hidden(sK1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,sK0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | m1_connsp_2(X2,sK0,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ( ! [X3] :
              ( ~ r2_hidden(sK1,X3)
              | ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ m1_connsp_2(X2,sK0,sK1) )
        & ( ? [X4] :
              ( r2_hidden(sK1,X4)
              & r1_tarski(X4,X2)
              & v3_pre_topc(X4,sK0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          | m1_connsp_2(X2,sK0,sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(sK1,X3)
            | ~ r1_tarski(X3,sK2)
            | ~ v3_pre_topc(X3,sK0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ m1_connsp_2(sK2,sK0,sK1) )
      & ( ? [X4] :
            ( r2_hidden(sK1,X4)
            & r1_tarski(X4,sK2)
            & v3_pre_topc(X4,sK0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        | m1_connsp_2(sK2,sK0,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X4] :
        ( r2_hidden(sK1,X4)
        & r1_tarski(X4,sK2)
        & v3_pre_topc(X4,sK0)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( r2_hidden(sK1,sK3)
      & r1_tarski(sK3,sK2)
      & v3_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m1_connsp_2(X2,X0,X1)
                <=> ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f117,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f46,f114])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f112,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f47,f109])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f107,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f48,f104])).

fof(f48,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f102,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f49,f99])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f97,plain,
    ( spl4_1
    | spl4_6 ),
    inference(avatar_split_clause,[],[f50,f94,f71])).

fof(f50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,
    ( spl4_1
    | spl4_5 ),
    inference(avatar_split_clause,[],[f51,f89,f71])).

fof(f51,plain,
    ( v3_pre_topc(sK3,sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,
    ( spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f52,f84,f71])).

fof(f52,plain,
    ( r1_tarski(sK3,sK2)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f53,f79,f71])).

fof(f53,plain,
    ( r2_hidden(sK1,sK3)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f54,f75,f71])).

fof(f54,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:57:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (5865)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.53  % (5864)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.53  % (5874)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.54  % (5863)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.54  % (5882)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.54  % (5867)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.54  % (5870)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.54  % (5885)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.54  % (5871)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.55  % (5873)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.55  % (5877)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.55  % (5872)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.55  % (5875)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.55  % (5878)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.56  % (5879)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.56  % (5862)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.56  % (5883)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.56  % (5869)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (5868)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.57  % (5880)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.57  % (5881)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.57  % (5866)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.71/0.59  % (5876)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.71/0.59  % (5868)Refutation found. Thanks to Tanya!
% 1.71/0.59  % SZS status Theorem for theBenchmark
% 1.71/0.59  % SZS output start Proof for theBenchmark
% 1.71/0.59  fof(f423,plain,(
% 1.71/0.59    $false),
% 1.71/0.59    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f102,f107,f112,f117,f122,f129,f153,f169,f183,f214,f244,f251,f314,f344,f417])).
% 1.71/0.59  fof(f417,plain,(
% 1.71/0.59    spl4_42 | ~spl4_37),
% 1.71/0.59    inference(avatar_split_clause,[],[f416,f311,f341])).
% 1.71/0.59  fof(f341,plain,(
% 1.71/0.59    spl4_42 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.71/0.59  fof(f311,plain,(
% 1.71/0.59    spl4_37 <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.71/0.59  fof(f416,plain,(
% 1.71/0.59    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_37),
% 1.71/0.59    inference(unit_resulting_resolution,[],[f313,f61])).
% 1.71/0.59  fof(f61,plain,(
% 1.71/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f42])).
% 1.71/0.59  fof(f42,plain,(
% 1.71/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.71/0.59    inference(nnf_transformation,[],[f4])).
% 1.71/0.59  fof(f4,axiom,(
% 1.71/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.71/0.59  fof(f313,plain,(
% 1.71/0.59    r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | ~spl4_37),
% 1.71/0.59    inference(avatar_component_clause,[],[f311])).
% 1.71/0.59  fof(f344,plain,(
% 1.71/0.59    ~spl4_18 | ~spl4_23 | ~spl4_42 | ~spl4_2 | ~spl4_20),
% 1.71/0.59    inference(avatar_split_clause,[],[f339,f180,f75,f341,f200,f166])).
% 1.71/0.59  fof(f166,plain,(
% 1.71/0.59    spl4_18 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.71/0.59  fof(f200,plain,(
% 1.71/0.59    spl4_23 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.71/0.59  fof(f75,plain,(
% 1.71/0.59    spl4_2 <=> ! [X3] : (~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2))),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.71/0.59  fof(f180,plain,(
% 1.71/0.59    spl4_20 <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.71/0.59  fof(f339,plain,(
% 1.71/0.59    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl4_2 | ~spl4_20)),
% 1.71/0.59    inference(resolution,[],[f182,f76])).
% 1.71/0.59  fof(f76,plain,(
% 1.71/0.59    ( ! [X3] : (~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2)) ) | ~spl4_2),
% 1.71/0.59    inference(avatar_component_clause,[],[f75])).
% 1.71/0.59  fof(f182,plain,(
% 1.71/0.59    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~spl4_20),
% 1.71/0.59    inference(avatar_component_clause,[],[f180])).
% 1.71/0.59  fof(f314,plain,(
% 1.71/0.59    spl4_37 | ~spl4_12 | ~spl4_18),
% 1.71/0.59    inference(avatar_split_clause,[],[f297,f166,f126,f311])).
% 1.71/0.59  fof(f126,plain,(
% 1.71/0.59    spl4_12 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.71/0.59  fof(f297,plain,(
% 1.71/0.59    r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | (~spl4_12 | ~spl4_18)),
% 1.71/0.59    inference(unit_resulting_resolution,[],[f128,f168,f59])).
% 1.71/0.59  fof(f59,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f23])).
% 1.71/0.59  fof(f23,plain,(
% 1.71/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.71/0.59    inference(flattening,[],[f22])).
% 1.71/0.59  fof(f22,plain,(
% 1.71/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.71/0.59    inference(ennf_transformation,[],[f1])).
% 1.71/0.59  fof(f1,axiom,(
% 1.71/0.59    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.71/0.59  fof(f168,plain,(
% 1.71/0.59    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl4_18),
% 1.71/0.59    inference(avatar_component_clause,[],[f166])).
% 1.71/0.59  fof(f128,plain,(
% 1.71/0.59    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl4_12),
% 1.71/0.59    inference(avatar_component_clause,[],[f126])).
% 1.71/0.59  fof(f251,plain,(
% 1.71/0.59    spl4_23 | ~spl4_1 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | spl4_11),
% 1.71/0.59    inference(avatar_split_clause,[],[f249,f119,f114,f109,f104,f99,f71,f200])).
% 1.71/0.59  fof(f71,plain,(
% 1.71/0.59    spl4_1 <=> m1_connsp_2(sK2,sK0,sK1)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.71/0.59  fof(f99,plain,(
% 1.71/0.59    spl4_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.71/0.59  fof(f104,plain,(
% 1.71/0.59    spl4_8 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.71/0.59  fof(f109,plain,(
% 1.71/0.59    spl4_9 <=> l1_pre_topc(sK0)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.71/0.59  fof(f114,plain,(
% 1.71/0.59    spl4_10 <=> v2_pre_topc(sK0)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.71/0.59  fof(f119,plain,(
% 1.71/0.59    spl4_11 <=> v2_struct_0(sK0)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.71/0.59  fof(f249,plain,(
% 1.71/0.59    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | (~spl4_1 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | spl4_11)),
% 1.71/0.59    inference(unit_resulting_resolution,[],[f121,f116,f111,f106,f101,f72,f57])).
% 1.71/0.59  fof(f57,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f41])).
% 1.71/0.59  fof(f41,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.71/0.59    inference(nnf_transformation,[],[f21])).
% 1.71/0.59  fof(f21,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.71/0.59    inference(flattening,[],[f20])).
% 1.71/0.59  fof(f20,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.71/0.59    inference(ennf_transformation,[],[f8])).
% 1.71/0.59  fof(f8,axiom,(
% 1.71/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 1.71/0.59  fof(f72,plain,(
% 1.71/0.59    m1_connsp_2(sK2,sK0,sK1) | ~spl4_1),
% 1.71/0.59    inference(avatar_component_clause,[],[f71])).
% 1.71/0.59  fof(f101,plain,(
% 1.71/0.59    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_7),
% 1.71/0.59    inference(avatar_component_clause,[],[f99])).
% 1.71/0.59  fof(f106,plain,(
% 1.71/0.59    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_8),
% 1.71/0.59    inference(avatar_component_clause,[],[f104])).
% 1.71/0.59  fof(f111,plain,(
% 1.71/0.59    l1_pre_topc(sK0) | ~spl4_9),
% 1.71/0.59    inference(avatar_component_clause,[],[f109])).
% 1.71/0.59  fof(f116,plain,(
% 1.71/0.59    v2_pre_topc(sK0) | ~spl4_10),
% 1.71/0.59    inference(avatar_component_clause,[],[f114])).
% 1.71/0.59  fof(f121,plain,(
% 1.71/0.59    ~v2_struct_0(sK0) | spl4_11),
% 1.71/0.59    inference(avatar_component_clause,[],[f119])).
% 1.71/0.59  fof(f244,plain,(
% 1.71/0.59    ~spl4_25 | spl4_1 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | spl4_11 | ~spl4_16),
% 1.71/0.59    inference(avatar_split_clause,[],[f243,f150,f119,f114,f109,f104,f99,f94,f71,f211])).
% 1.71/0.59  fof(f211,plain,(
% 1.71/0.59    spl4_25 <=> m1_connsp_2(sK3,sK0,sK1)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.71/0.59  fof(f94,plain,(
% 1.71/0.59    spl4_6 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.71/0.59  fof(f150,plain,(
% 1.71/0.59    spl4_16 <=> sK3 = k3_xboole_0(sK3,sK2)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.71/0.59  fof(f243,plain,(
% 1.71/0.59    ~m1_connsp_2(sK3,sK0,sK1) | (spl4_1 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | spl4_11 | ~spl4_16)),
% 1.71/0.59    inference(forward_demodulation,[],[f242,f152])).
% 1.71/0.59  fof(f152,plain,(
% 1.71/0.59    sK3 = k3_xboole_0(sK3,sK2) | ~spl4_16),
% 1.71/0.59    inference(avatar_component_clause,[],[f150])).
% 1.71/0.59  fof(f242,plain,(
% 1.71/0.59    ~m1_connsp_2(k3_xboole_0(sK3,sK2),sK0,sK1) | (spl4_1 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | spl4_11)),
% 1.71/0.59    inference(forward_demodulation,[],[f238,f176])).
% 1.71/0.59  fof(f176,plain,(
% 1.71/0.59    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2)) ) | ~spl4_7),
% 1.71/0.59    inference(unit_resulting_resolution,[],[f101,f69])).
% 1.71/0.59  fof(f69,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f32])).
% 1.71/0.59  fof(f32,plain,(
% 1.71/0.59    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.71/0.59    inference(ennf_transformation,[],[f3])).
% 1.71/0.59  fof(f3,axiom,(
% 1.71/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.71/0.59  fof(f238,plain,(
% 1.71/0.59    ~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK3,sK2),sK0,sK1) | (spl4_1 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | spl4_11)),
% 1.71/0.59    inference(unit_resulting_resolution,[],[f121,f116,f111,f73,f106,f96,f101,f68])).
% 1.71/0.59  fof(f68,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_connsp_2(X3,X0,X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f44])).
% 1.71/0.59  fof(f44,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) | ~m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | ~m1_connsp_2(X3,X0,X1) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.71/0.59    inference(flattening,[],[f43])).
% 1.71/0.59  fof(f43,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) | ~m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | (~m1_connsp_2(X3,X0,X1) | ~m1_connsp_2(X2,X0,X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.71/0.59    inference(nnf_transformation,[],[f31])).
% 1.71/0.59  fof(f31,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.71/0.59    inference(flattening,[],[f30])).
% 1.71/0.59  fof(f30,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.71/0.59    inference(ennf_transformation,[],[f10])).
% 1.71/0.59  fof(f10,axiom,(
% 1.71/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_connsp_2)).
% 1.71/0.59  fof(f96,plain,(
% 1.71/0.59    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 1.71/0.59    inference(avatar_component_clause,[],[f94])).
% 1.71/0.59  fof(f73,plain,(
% 1.71/0.59    ~m1_connsp_2(sK2,sK0,sK1) | spl4_1),
% 1.71/0.59    inference(avatar_component_clause,[],[f71])).
% 1.71/0.59  fof(f214,plain,(
% 1.71/0.59    spl4_25 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_9 | ~spl4_10 | spl4_11),
% 1.71/0.59    inference(avatar_split_clause,[],[f208,f119,f114,f109,f104,f94,f89,f79,f211])).
% 1.71/0.59  fof(f79,plain,(
% 1.71/0.59    spl4_3 <=> r2_hidden(sK1,sK3)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.71/0.59  fof(f89,plain,(
% 1.71/0.59    spl4_5 <=> v3_pre_topc(sK3,sK0)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.71/0.59  fof(f208,plain,(
% 1.71/0.59    m1_connsp_2(sK3,sK0,sK1) | (~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_9 | ~spl4_10 | spl4_11)),
% 1.71/0.59    inference(unit_resulting_resolution,[],[f121,f116,f111,f81,f106,f91,f96,f56])).
% 1.71/0.59  fof(f56,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_connsp_2(X1,X0,X2)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f19])).
% 1.71/0.59  fof(f19,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.71/0.59    inference(flattening,[],[f18])).
% 1.71/0.59  fof(f18,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.71/0.59    inference(ennf_transformation,[],[f11])).
% 1.71/0.59  fof(f11,axiom,(
% 1.71/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 1.71/0.59  fof(f91,plain,(
% 1.71/0.59    v3_pre_topc(sK3,sK0) | ~spl4_5),
% 1.71/0.59    inference(avatar_component_clause,[],[f89])).
% 1.71/0.59  fof(f81,plain,(
% 1.71/0.59    r2_hidden(sK1,sK3) | ~spl4_3),
% 1.71/0.59    inference(avatar_component_clause,[],[f79])).
% 1.71/0.59  fof(f183,plain,(
% 1.71/0.59    spl4_20 | ~spl4_7 | ~spl4_9 | ~spl4_10),
% 1.71/0.59    inference(avatar_split_clause,[],[f178,f114,f109,f99,f180])).
% 1.71/0.59  fof(f178,plain,(
% 1.71/0.59    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | (~spl4_7 | ~spl4_9 | ~spl4_10)),
% 1.71/0.59    inference(unit_resulting_resolution,[],[f116,f111,f101,f64])).
% 1.71/0.59  fof(f64,plain,(
% 1.71/0.59    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f27])).
% 1.71/0.59  fof(f27,plain,(
% 1.71/0.59    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.71/0.59    inference(flattening,[],[f26])).
% 1.71/0.59  fof(f26,plain,(
% 1.71/0.59    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.71/0.59    inference(ennf_transformation,[],[f6])).
% 1.71/0.59  fof(f6,axiom,(
% 1.71/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.71/0.59  fof(f169,plain,(
% 1.71/0.59    spl4_18 | ~spl4_7 | ~spl4_9),
% 1.71/0.59    inference(avatar_split_clause,[],[f164,f109,f99,f166])).
% 1.71/0.59  fof(f164,plain,(
% 1.71/0.59    r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl4_7 | ~spl4_9)),
% 1.71/0.59    inference(unit_resulting_resolution,[],[f111,f101,f63])).
% 1.71/0.59  fof(f63,plain,(
% 1.71/0.59    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f25])).
% 1.71/0.59  fof(f25,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.71/0.59    inference(ennf_transformation,[],[f7])).
% 1.71/0.59  fof(f7,axiom,(
% 1.71/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.71/0.59  fof(f153,plain,(
% 1.71/0.59    spl4_16 | ~spl4_4),
% 1.71/0.59    inference(avatar_split_clause,[],[f142,f84,f150])).
% 1.71/0.59  fof(f84,plain,(
% 1.71/0.59    spl4_4 <=> r1_tarski(sK3,sK2)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.71/0.59  fof(f142,plain,(
% 1.71/0.59    sK3 = k3_xboole_0(sK3,sK2) | ~spl4_4),
% 1.71/0.59    inference(unit_resulting_resolution,[],[f86,f62])).
% 1.71/0.59  fof(f62,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f24])).
% 1.71/0.59  fof(f24,plain,(
% 1.71/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.71/0.59    inference(ennf_transformation,[],[f2])).
% 1.71/0.59  fof(f2,axiom,(
% 1.71/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.71/0.59  fof(f86,plain,(
% 1.71/0.59    r1_tarski(sK3,sK2) | ~spl4_4),
% 1.71/0.59    inference(avatar_component_clause,[],[f84])).
% 1.71/0.59  fof(f129,plain,(
% 1.71/0.59    spl4_12 | ~spl4_7),
% 1.71/0.59    inference(avatar_split_clause,[],[f124,f99,f126])).
% 1.71/0.59  fof(f124,plain,(
% 1.71/0.59    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl4_7),
% 1.71/0.59    inference(unit_resulting_resolution,[],[f101,f60])).
% 1.71/0.59  fof(f60,plain,(
% 1.71/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f42])).
% 1.71/0.59  fof(f122,plain,(
% 1.71/0.59    ~spl4_11),
% 1.71/0.59    inference(avatar_split_clause,[],[f45,f119])).
% 1.71/0.59  fof(f45,plain,(
% 1.71/0.59    ~v2_struct_0(sK0)),
% 1.71/0.59    inference(cnf_transformation,[],[f40])).
% 1.71/0.59  fof(f40,plain,(
% 1.71/0.59    (((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(sK2,sK0,sK1)) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(sK2,sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.71/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f39,f38,f37,f36])).
% 1.71/0.59  fof(f36,plain,(
% 1.71/0.59    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(X2,sK0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(X2,sK0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.71/0.59    introduced(choice_axiom,[])).
% 1.71/0.59  fof(f37,plain,(
% 1.71/0.59    ? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(X2,sK0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(X2,sK0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(X2,sK0,sK1)) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(X2,sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.71/0.59    introduced(choice_axiom,[])).
% 1.71/0.59  fof(f38,plain,(
% 1.71/0.59    ? [X2] : ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(X2,sK0,sK1)) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(X2,sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(sK2,sK0,sK1)) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(sK2,sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.71/0.59    introduced(choice_axiom,[])).
% 1.71/0.59  fof(f39,plain,(
% 1.71/0.59    ? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) => (r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.71/0.59    introduced(choice_axiom,[])).
% 1.71/0.59  fof(f35,plain,(
% 1.71/0.59    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.71/0.59    inference(rectify,[],[f34])).
% 1.71/0.59  fof(f34,plain,(
% 1.71/0.59    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.71/0.59    inference(flattening,[],[f33])).
% 1.71/0.59  fof(f33,plain,(
% 1.71/0.59    ? [X0] : (? [X1] : (? [X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.71/0.59    inference(nnf_transformation,[],[f15])).
% 1.71/0.59  fof(f15,plain,(
% 1.71/0.59    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.71/0.59    inference(flattening,[],[f14])).
% 1.71/0.59  fof(f14,plain,(
% 1.71/0.59    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.71/0.59    inference(ennf_transformation,[],[f13])).
% 1.71/0.59  fof(f13,negated_conjecture,(
% 1.71/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.71/0.59    inference(negated_conjecture,[],[f12])).
% 1.71/0.59  fof(f12,conjecture,(
% 1.71/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.71/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).
% 1.71/0.59  fof(f117,plain,(
% 1.71/0.59    spl4_10),
% 1.71/0.59    inference(avatar_split_clause,[],[f46,f114])).
% 1.71/0.59  fof(f46,plain,(
% 1.71/0.59    v2_pre_topc(sK0)),
% 1.71/0.59    inference(cnf_transformation,[],[f40])).
% 1.71/0.59  fof(f112,plain,(
% 1.71/0.59    spl4_9),
% 1.71/0.59    inference(avatar_split_clause,[],[f47,f109])).
% 1.71/0.59  fof(f47,plain,(
% 1.71/0.59    l1_pre_topc(sK0)),
% 1.71/0.59    inference(cnf_transformation,[],[f40])).
% 1.71/0.59  fof(f107,plain,(
% 1.71/0.59    spl4_8),
% 1.71/0.59    inference(avatar_split_clause,[],[f48,f104])).
% 1.71/0.59  fof(f48,plain,(
% 1.71/0.59    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.71/0.59    inference(cnf_transformation,[],[f40])).
% 1.71/0.59  fof(f102,plain,(
% 1.71/0.59    spl4_7),
% 1.71/0.59    inference(avatar_split_clause,[],[f49,f99])).
% 1.71/0.60  fof(f49,plain,(
% 1.71/0.60    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.71/0.60    inference(cnf_transformation,[],[f40])).
% 1.71/0.60  fof(f97,plain,(
% 1.71/0.60    spl4_1 | spl4_6),
% 1.71/0.60    inference(avatar_split_clause,[],[f50,f94,f71])).
% 1.71/0.60  fof(f50,plain,(
% 1.71/0.60    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK2,sK0,sK1)),
% 1.71/0.60    inference(cnf_transformation,[],[f40])).
% 1.71/0.60  fof(f92,plain,(
% 1.71/0.60    spl4_1 | spl4_5),
% 1.71/0.60    inference(avatar_split_clause,[],[f51,f89,f71])).
% 1.71/0.60  fof(f51,plain,(
% 1.71/0.60    v3_pre_topc(sK3,sK0) | m1_connsp_2(sK2,sK0,sK1)),
% 1.71/0.60    inference(cnf_transformation,[],[f40])).
% 1.71/0.60  fof(f87,plain,(
% 1.71/0.60    spl4_1 | spl4_4),
% 1.71/0.60    inference(avatar_split_clause,[],[f52,f84,f71])).
% 1.71/0.60  fof(f52,plain,(
% 1.71/0.60    r1_tarski(sK3,sK2) | m1_connsp_2(sK2,sK0,sK1)),
% 1.71/0.60    inference(cnf_transformation,[],[f40])).
% 1.71/0.60  fof(f82,plain,(
% 1.71/0.60    spl4_1 | spl4_3),
% 1.71/0.60    inference(avatar_split_clause,[],[f53,f79,f71])).
% 1.71/0.60  fof(f53,plain,(
% 1.71/0.60    r2_hidden(sK1,sK3) | m1_connsp_2(sK2,sK0,sK1)),
% 1.71/0.60    inference(cnf_transformation,[],[f40])).
% 1.71/0.60  fof(f77,plain,(
% 1.71/0.60    ~spl4_1 | spl4_2),
% 1.71/0.60    inference(avatar_split_clause,[],[f54,f75,f71])).
% 1.71/0.60  fof(f54,plain,(
% 1.71/0.60    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(sK2,sK0,sK1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f40])).
% 1.71/0.60  % SZS output end Proof for theBenchmark
% 1.71/0.60  % (5868)------------------------------
% 1.71/0.60  % (5868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.60  % (5868)Termination reason: Refutation
% 1.71/0.60  
% 1.71/0.60  % (5868)Memory used [KB]: 11001
% 1.71/0.60  % (5868)Time elapsed: 0.166 s
% 1.71/0.60  % (5868)------------------------------
% 1.71/0.60  % (5868)------------------------------
% 1.71/0.60  % (5884)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.71/0.61  % (5861)Success in time 0.237 s
%------------------------------------------------------------------------------
