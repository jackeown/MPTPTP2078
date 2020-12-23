%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 158 expanded)
%              Number of leaves         :   26 (  76 expanded)
%              Depth                    :    7
%              Number of atoms          :  293 ( 597 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f53,f57,f61,f65,f69,f73,f79,f89,f94,f99,f130,f136,f141,f144])).

fof(f144,plain,
    ( spl3_13
    | ~ spl3_23 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl3_13
    | ~ spl3_23 ),
    inference(resolution,[],[f140,f88])).

fof(f88,plain,
    ( ~ v2_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_13
  <=> v2_tops_2(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f140,plain,
    ( ! [X0] : v2_tops_2(k3_xboole_0(sK1,X0),sK0)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_23
  <=> ! [X0] : v2_tops_2(k3_xboole_0(sK1,X0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f141,plain,
    ( spl3_23
    | ~ spl3_9
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f137,f134,f67,f139])).

fof(f67,plain,
    ( spl3_9
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f134,plain,
    ( spl3_22
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f137,plain,
    ( ! [X0] : v2_tops_2(k3_xboole_0(sK1,X0),sK0)
    | ~ spl3_9
    | ~ spl3_22 ),
    inference(resolution,[],[f135,f68])).

fof(f68,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v2_tops_2(X0,sK0) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f134])).

fof(f136,plain,
    ( spl3_22
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f132,f128,f45,f35,f134])).

fof(f35,plain,
    ( spl3_2
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f128,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( ~ v2_tops_2(X0,sK0)
        | ~ r1_tarski(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v2_tops_2(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f131,f47])).

fof(f47,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_21 ),
    inference(resolution,[],[f129,f37])).

fof(f37,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ v2_tops_2(X0,sK0)
        | ~ r1_tarski(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X1,sK0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f128])).

fof(f130,plain,
    ( spl3_21
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f126,f97,f63,f50,f128])).

fof(f50,plain,
    ( spl3_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f63,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( v2_tops_2(X1,X0)
        | ~ v2_tops_2(X2,X0)
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f97,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ v2_tops_2(X0,sK0)
        | ~ r1_tarski(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X1,sK0) )
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f125,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f97])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ v2_tops_2(X0,sK0)
        | ~ r1_tarski(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X1,sK0) )
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(resolution,[],[f64,f52])).

fof(f52,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_tops_2(X2,X0)
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | v2_tops_2(X1,X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f99,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f95,f92,f50,f97])).

fof(f92,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
        | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
        | ~ l1_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X1,X0) )
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(resolution,[],[f93,f52])).

fof(f93,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
        | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,
    ( spl3_14
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f90,f59,f55,f92])).

fof(f55,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ r1_tarski(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f59,plain,
    ( spl3_7
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
        | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
        | ~ l1_pre_topc(X2) )
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(resolution,[],[f56,f60])).

fof(f60,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f56,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_struct_0(X0)
        | ~ r1_tarski(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f89,plain,
    ( ~ spl3_13
    | spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f84,f77,f30,f86])).

fof(f30,plain,
    ( spl3_1
  <=> v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f77,plain,
    ( spl3_11
  <=> ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f84,plain,
    ( ~ v2_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | spl3_1
    | ~ spl3_11 ),
    inference(superposition,[],[f32,f78])).

fof(f78,plain,
    ( ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f32,plain,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f79,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f74,f71,f40,f77])).

fof(f40,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f71,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f74,plain,
    ( ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(resolution,[],[f72,f42])).

fof(f42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f72,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f73,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f28,f71])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f69,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f65,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v2_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v2_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).

fof(f61,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f57,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f24,f55])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ r1_tarski(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( r1_tarski(X2,X1)
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_tops_2)).

fof(f53,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f50])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v2_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v2_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v2_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
            & v2_tops_2(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
          & v2_tops_2(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v2_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v2_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v2_tops_2(X1,X0)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X1,X0)
               => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).

fof(f48,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f35])).

fof(f22,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f30])).

fof(f23,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (14921)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (14920)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.41  % (14922)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.41  % (14921)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f145,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f53,f57,f61,f65,f69,f73,f79,f89,f94,f99,f130,f136,f141,f144])).
% 0.21/0.41  fof(f144,plain,(
% 0.21/0.41    spl3_13 | ~spl3_23),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f142])).
% 0.21/0.41  fof(f142,plain,(
% 0.21/0.41    $false | (spl3_13 | ~spl3_23)),
% 0.21/0.41    inference(resolution,[],[f140,f88])).
% 0.21/0.41  fof(f88,plain,(
% 0.21/0.41    ~v2_tops_2(k3_xboole_0(sK1,sK2),sK0) | spl3_13),
% 0.21/0.41    inference(avatar_component_clause,[],[f86])).
% 0.21/0.41  fof(f86,plain,(
% 0.21/0.41    spl3_13 <=> v2_tops_2(k3_xboole_0(sK1,sK2),sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.41  fof(f140,plain,(
% 0.21/0.41    ( ! [X0] : (v2_tops_2(k3_xboole_0(sK1,X0),sK0)) ) | ~spl3_23),
% 0.21/0.41    inference(avatar_component_clause,[],[f139])).
% 0.21/0.41  fof(f139,plain,(
% 0.21/0.41    spl3_23 <=> ! [X0] : v2_tops_2(k3_xboole_0(sK1,X0),sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.41  fof(f141,plain,(
% 0.21/0.41    spl3_23 | ~spl3_9 | ~spl3_22),
% 0.21/0.41    inference(avatar_split_clause,[],[f137,f134,f67,f139])).
% 0.21/0.41  fof(f67,plain,(
% 0.21/0.41    spl3_9 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.41  fof(f134,plain,(
% 0.21/0.41    spl3_22 <=> ! [X0] : (~r1_tarski(X0,sK1) | v2_tops_2(X0,sK0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.41  fof(f137,plain,(
% 0.21/0.41    ( ! [X0] : (v2_tops_2(k3_xboole_0(sK1,X0),sK0)) ) | (~spl3_9 | ~spl3_22)),
% 0.21/0.41    inference(resolution,[],[f135,f68])).
% 0.21/0.41  fof(f68,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_9),
% 0.21/0.41    inference(avatar_component_clause,[],[f67])).
% 0.21/0.41  fof(f135,plain,(
% 0.21/0.41    ( ! [X0] : (~r1_tarski(X0,sK1) | v2_tops_2(X0,sK0)) ) | ~spl3_22),
% 0.21/0.41    inference(avatar_component_clause,[],[f134])).
% 0.21/0.41  fof(f136,plain,(
% 0.21/0.41    spl3_22 | ~spl3_2 | ~spl3_4 | ~spl3_21),
% 0.21/0.41    inference(avatar_split_clause,[],[f132,f128,f45,f35,f134])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    spl3_2 <=> v2_tops_2(sK1,sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.41  fof(f45,plain,(
% 0.21/0.41    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.41  fof(f128,plain,(
% 0.21/0.41    spl3_21 <=> ! [X1,X0] : (~v2_tops_2(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X1,sK0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.41  fof(f132,plain,(
% 0.21/0.41    ( ! [X0] : (~r1_tarski(X0,sK1) | v2_tops_2(X0,sK0)) ) | (~spl3_2 | ~spl3_4 | ~spl3_21)),
% 0.21/0.41    inference(subsumption_resolution,[],[f131,f47])).
% 0.21/0.41  fof(f47,plain,(
% 0.21/0.41    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f45])).
% 0.21/0.41  fof(f131,plain,(
% 0.21/0.41    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | (~spl3_2 | ~spl3_21)),
% 0.21/0.41    inference(resolution,[],[f129,f37])).
% 0.21/0.41  fof(f37,plain,(
% 0.21/0.41    v2_tops_2(sK1,sK0) | ~spl3_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f35])).
% 0.21/0.41  fof(f129,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v2_tops_2(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X1,sK0)) ) | ~spl3_21),
% 0.21/0.41    inference(avatar_component_clause,[],[f128])).
% 0.21/0.41  fof(f130,plain,(
% 0.21/0.41    spl3_21 | ~spl3_5 | ~spl3_8 | ~spl3_15),
% 0.21/0.41    inference(avatar_split_clause,[],[f126,f97,f63,f50,f128])).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    spl3_5 <=> l1_pre_topc(sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.41  fof(f63,plain,(
% 0.21/0.41    spl3_8 <=> ! [X1,X0,X2] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.41  fof(f97,plain,(
% 0.21/0.41    spl3_15 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X1,X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.41  fof(f126,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v2_tops_2(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X1,sK0)) ) | (~spl3_5 | ~spl3_8 | ~spl3_15)),
% 0.21/0.41    inference(subsumption_resolution,[],[f125,f98])).
% 0.21/0.41  fof(f98,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(X1,X0) | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_15),
% 0.21/0.41    inference(avatar_component_clause,[],[f97])).
% 0.21/0.41  fof(f125,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v2_tops_2(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X1,sK0)) ) | (~spl3_5 | ~spl3_8)),
% 0.21/0.41    inference(resolution,[],[f64,f52])).
% 0.21/0.41  fof(f52,plain,(
% 0.21/0.41    l1_pre_topc(sK0) | ~spl3_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f50])).
% 0.21/0.41  fof(f64,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_2(X1,X0)) ) | ~spl3_8),
% 0.21/0.41    inference(avatar_component_clause,[],[f63])).
% 0.21/0.41  fof(f99,plain,(
% 0.21/0.41    spl3_15 | ~spl3_5 | ~spl3_14),
% 0.21/0.41    inference(avatar_split_clause,[],[f95,f92,f50,f97])).
% 0.21/0.41  fof(f92,plain,(
% 0.21/0.41    spl3_14 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~l1_pre_topc(X2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.41  fof(f95,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X1,X0)) ) | (~spl3_5 | ~spl3_14)),
% 0.21/0.41    inference(resolution,[],[f93,f52])).
% 0.21/0.41  fof(f93,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~l1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~r1_tarski(X0,X1)) ) | ~spl3_14),
% 0.21/0.41    inference(avatar_component_clause,[],[f92])).
% 0.21/0.41  fof(f94,plain,(
% 0.21/0.41    spl3_14 | ~spl3_6 | ~spl3_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f90,f59,f55,f92])).
% 0.21/0.41  fof(f55,plain,(
% 0.21/0.41    spl3_6 <=> ! [X1,X0,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.41  fof(f59,plain,(
% 0.21/0.41    spl3_7 <=> ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.41  fof(f90,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~l1_pre_topc(X2)) ) | (~spl3_6 | ~spl3_7)),
% 0.21/0.41    inference(resolution,[],[f56,f60])).
% 0.21/0.41  fof(f60,plain,(
% 0.21/0.41    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl3_7),
% 0.21/0.41    inference(avatar_component_clause,[],[f59])).
% 0.21/0.41  fof(f56,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) ) | ~spl3_6),
% 0.21/0.41    inference(avatar_component_clause,[],[f55])).
% 0.21/0.41  fof(f89,plain,(
% 0.21/0.41    ~spl3_13 | spl3_1 | ~spl3_11),
% 0.21/0.41    inference(avatar_split_clause,[],[f84,f77,f30,f86])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    spl3_1 <=> v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.41  fof(f77,plain,(
% 0.21/0.41    spl3_11 <=> ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.41  fof(f84,plain,(
% 0.21/0.41    ~v2_tops_2(k3_xboole_0(sK1,sK2),sK0) | (spl3_1 | ~spl3_11)),
% 0.21/0.41    inference(superposition,[],[f32,f78])).
% 0.21/0.41  fof(f78,plain,(
% 0.21/0.41    ( ! [X0] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)) ) | ~spl3_11),
% 0.21/0.41    inference(avatar_component_clause,[],[f77])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl3_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f30])).
% 0.21/0.41  fof(f79,plain,(
% 0.21/0.41    spl3_11 | ~spl3_3 | ~spl3_10),
% 0.21/0.41    inference(avatar_split_clause,[],[f74,f71,f40,f77])).
% 0.21/0.41  fof(f40,plain,(
% 0.21/0.41    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.41  fof(f71,plain,(
% 0.21/0.41    spl3_10 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.41  fof(f74,plain,(
% 0.21/0.41    ( ! [X0] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)) ) | (~spl3_3 | ~spl3_10)),
% 0.21/0.41    inference(resolution,[],[f72,f42])).
% 0.21/0.41  fof(f42,plain,(
% 0.21/0.41    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f40])).
% 0.21/0.41  fof(f72,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) ) | ~spl3_10),
% 0.21/0.41    inference(avatar_component_clause,[],[f71])).
% 0.21/0.41  fof(f73,plain,(
% 0.21/0.41    spl3_10),
% 0.21/0.41    inference(avatar_split_clause,[],[f28,f71])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.41  fof(f69,plain,(
% 0.21/0.41    spl3_9),
% 0.21/0.41    inference(avatar_split_clause,[],[f27,f67])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.41  fof(f65,plain,(
% 0.21/0.41    spl3_8),
% 0.21/0.41    inference(avatar_split_clause,[],[f26,f63])).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (! [X2] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.41    inference(flattening,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (! [X2] : ((v2_tops_2(X1,X0) | (~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).
% 0.21/0.41  fof(f61,plain,(
% 0.21/0.41    spl3_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f25,f59])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.41  fof(f57,plain,(
% 0.21/0.41    spl3_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f24,f55])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_struct_0(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (r1_tarski(X2,X1) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_tops_2)).
% 0.21/0.41  fof(f53,plain,(
% 0.21/0.41    spl3_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f19,f50])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    l1_pre_topc(sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f18])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16,f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.41    inference(flattening,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,negated_conjecture,(
% 0.21/0.41    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.21/0.41    inference(negated_conjecture,[],[f6])).
% 0.21/0.41  fof(f6,conjecture,(
% 0.21/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).
% 0.21/0.41  fof(f48,plain,(
% 0.21/0.41    spl3_4),
% 0.21/0.41    inference(avatar_split_clause,[],[f20,f45])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.41    inference(cnf_transformation,[],[f18])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    spl3_3),
% 0.21/0.41    inference(avatar_split_clause,[],[f21,f40])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.41    inference(cnf_transformation,[],[f18])).
% 0.21/0.41  fof(f38,plain,(
% 0.21/0.41    spl3_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f22,f35])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    v2_tops_2(sK1,sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f18])).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    ~spl3_1),
% 0.21/0.41    inference(avatar_split_clause,[],[f23,f30])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f18])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (14921)------------------------------
% 0.21/0.41  % (14921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (14921)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (14921)Memory used [KB]: 10618
% 0.21/0.41  % (14921)Time elapsed: 0.006 s
% 0.21/0.41  % (14921)------------------------------
% 0.21/0.41  % (14921)------------------------------
% 0.21/0.41  % (14915)Success in time 0.063 s
%------------------------------------------------------------------------------
