%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 172 expanded)
%              Number of leaves         :   28 (  83 expanded)
%              Depth                    :    7
%              Number of atoms          :  299 ( 613 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f54,f58,f62,f66,f70,f74,f78,f91,f98,f112,f169,f175,f181,f190,f196,f199])).

fof(f199,plain,
    ( spl3_17
    | ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl3_17
    | ~ spl3_33 ),
    inference(resolution,[],[f195,f111])).

fof(f111,plain,
    ( ~ v1_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_17
  <=> v1_tops_2(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f195,plain,
    ( ! [X0] : v1_tops_2(k3_xboole_0(sK1,X0),sK0)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl3_33
  <=> ! [X0] : v1_tops_2(k3_xboole_0(sK1,X0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f196,plain,
    ( spl3_33
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f192,f188,f88,f72,f194])).

fof(f72,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f88,plain,
    ( spl3_13
  <=> r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f188,plain,
    ( spl3_32
  <=> ! [X0] :
        ( v1_tops_2(k3_xboole_0(sK1,X0),sK0)
        | ~ r1_tarski(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f192,plain,
    ( ! [X0] : v1_tops_2(k3_xboole_0(sK1,X0),sK0)
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f191,f90])).

fof(f90,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f88])).

fof(f191,plain,
    ( ! [X0] :
        ( v1_tops_2(k3_xboole_0(sK1,X0),sK0)
        | ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_10
    | ~ spl3_32 ),
    inference(resolution,[],[f189,f73])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_2(k3_xboole_0(sK1,X0),sK0) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f188])).

fof(f190,plain,
    ( spl3_32
    | ~ spl3_8
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f186,f179,f64,f188])).

fof(f64,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f179,plain,
    ( spl3_30
  <=> ! [X0] :
        ( ~ m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(k3_xboole_0(sK1,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f186,plain,
    ( ! [X0] :
        ( v1_tops_2(k3_xboole_0(sK1,X0),sK0)
        | ~ r1_tarski(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_8
    | ~ spl3_30 ),
    inference(resolution,[],[f180,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(k3_xboole_0(sK1,X0),sK0) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f179])).

fof(f181,plain,
    ( spl3_30
    | ~ spl3_7
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f176,f173,f60,f179])).

fof(f60,plain,
    ( spl3_7
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f173,plain,
    ( spl3_29
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(k3_xboole_0(sK1,X0),sK0) )
    | ~ spl3_7
    | ~ spl3_29 ),
    inference(resolution,[],[f174,f61])).

fof(f61,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f173])).

fof(f175,plain,
    ( spl3_29
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f171,f167,f46,f36,f173])).

fof(f36,plain,
    ( spl3_2
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f46,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f167,plain,
    ( spl3_28
  <=> ! [X1,X0] :
        ( ~ v1_tops_2(X0,sK0)
        | ~ r1_tarski(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f170,f48])).

fof(f48,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_28 ),
    inference(resolution,[],[f168,f38])).

fof(f38,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ v1_tops_2(X0,sK0)
        | ~ r1_tarski(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X1,sK0) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f167])).

fof(f169,plain,
    ( spl3_28
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f165,f56,f51,f167])).

fof(f51,plain,
    ( spl3_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f56,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( v1_tops_2(X1,X0)
        | ~ v1_tops_2(X2,X0)
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( ~ v1_tops_2(X0,sK0)
        | ~ r1_tarski(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X1,sK0) )
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(resolution,[],[f57,f53])).

fof(f53,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f57,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v1_tops_2(X2,X0)
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | v1_tops_2(X1,X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f112,plain,
    ( ~ spl3_17
    | spl3_1
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f107,f96,f31,f109])).

fof(f31,plain,
    ( spl3_1
  <=> v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f96,plain,
    ( spl3_14
  <=> ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f107,plain,
    ( ~ v1_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | spl3_1
    | ~ spl3_14 ),
    inference(superposition,[],[f33,f97])).

fof(f97,plain,
    ( ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f96])).

fof(f33,plain,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f98,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f92,f76,f41,f96])).

fof(f41,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f76,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f92,plain,
    ( ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(resolution,[],[f77,f43])).

fof(f43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f77,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f91,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f80,f68,f46,f88])).

fof(f68,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f80,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(resolution,[],[f69,f48])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f78,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f29,f76])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f74,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f28,f72])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f70,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f26,f68])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f66,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f58,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f24,f56])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

fof(f54,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f51])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v1_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v1_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
            & v1_tops_2(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
          & v1_tops_2(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v1_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v1_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
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
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tops_2)).

fof(f49,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f36])).

fof(f22,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f31])).

fof(f23,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.43  % (7590)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.45  % (7588)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.45  % (7591)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.45  % (7592)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.45  % (7584)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.45  % (7588)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f200,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f54,f58,f62,f66,f70,f74,f78,f91,f98,f112,f169,f175,f181,f190,f196,f199])).
% 0.22/0.45  fof(f199,plain,(
% 0.22/0.45    spl3_17 | ~spl3_33),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f197])).
% 0.22/0.45  fof(f197,plain,(
% 0.22/0.45    $false | (spl3_17 | ~spl3_33)),
% 0.22/0.45    inference(resolution,[],[f195,f111])).
% 0.22/0.45  fof(f111,plain,(
% 0.22/0.45    ~v1_tops_2(k3_xboole_0(sK1,sK2),sK0) | spl3_17),
% 0.22/0.45    inference(avatar_component_clause,[],[f109])).
% 0.22/0.45  fof(f109,plain,(
% 0.22/0.45    spl3_17 <=> v1_tops_2(k3_xboole_0(sK1,sK2),sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.45  fof(f195,plain,(
% 0.22/0.45    ( ! [X0] : (v1_tops_2(k3_xboole_0(sK1,X0),sK0)) ) | ~spl3_33),
% 0.22/0.45    inference(avatar_component_clause,[],[f194])).
% 0.22/0.45  fof(f194,plain,(
% 0.22/0.45    spl3_33 <=> ! [X0] : v1_tops_2(k3_xboole_0(sK1,X0),sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.45  fof(f196,plain,(
% 0.22/0.45    spl3_33 | ~spl3_10 | ~spl3_13 | ~spl3_32),
% 0.22/0.45    inference(avatar_split_clause,[],[f192,f188,f88,f72,f194])).
% 0.22/0.45  fof(f72,plain,(
% 0.22/0.45    spl3_10 <=> ! [X1,X0,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.45  fof(f88,plain,(
% 0.22/0.45    spl3_13 <=> r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.45  fof(f188,plain,(
% 0.22/0.45    spl3_32 <=> ! [X0] : (v1_tops_2(k3_xboole_0(sK1,X0),sK0) | ~r1_tarski(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.45  fof(f192,plain,(
% 0.22/0.45    ( ! [X0] : (v1_tops_2(k3_xboole_0(sK1,X0),sK0)) ) | (~spl3_10 | ~spl3_13 | ~spl3_32)),
% 0.22/0.45    inference(subsumption_resolution,[],[f191,f90])).
% 0.22/0.45  fof(f90,plain,(
% 0.22/0.45    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_13),
% 0.22/0.45    inference(avatar_component_clause,[],[f88])).
% 0.22/0.45  fof(f191,plain,(
% 0.22/0.45    ( ! [X0] : (v1_tops_2(k3_xboole_0(sK1,X0),sK0) | ~r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_10 | ~spl3_32)),
% 0.22/0.45    inference(resolution,[],[f189,f73])).
% 0.22/0.45  fof(f73,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.22/0.45    inference(avatar_component_clause,[],[f72])).
% 0.22/0.45  fof(f189,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_2(k3_xboole_0(sK1,X0),sK0)) ) | ~spl3_32),
% 0.22/0.45    inference(avatar_component_clause,[],[f188])).
% 0.22/0.45  fof(f190,plain,(
% 0.22/0.45    spl3_32 | ~spl3_8 | ~spl3_30),
% 0.22/0.45    inference(avatar_split_clause,[],[f186,f179,f64,f188])).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    spl3_8 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.45  fof(f179,plain,(
% 0.22/0.45    spl3_30 <=> ! [X0] : (~m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(k3_xboole_0(sK1,X0),sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.45  fof(f186,plain,(
% 0.22/0.45    ( ! [X0] : (v1_tops_2(k3_xboole_0(sK1,X0),sK0) | ~r1_tarski(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_8 | ~spl3_30)),
% 0.22/0.45    inference(resolution,[],[f180,f65])).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f64])).
% 0.22/0.45  fof(f180,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(k3_xboole_0(sK1,X0),sK0)) ) | ~spl3_30),
% 0.22/0.45    inference(avatar_component_clause,[],[f179])).
% 0.22/0.45  fof(f181,plain,(
% 0.22/0.45    spl3_30 | ~spl3_7 | ~spl3_29),
% 0.22/0.45    inference(avatar_split_clause,[],[f176,f173,f60,f179])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    spl3_7 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.45  fof(f173,plain,(
% 0.22/0.45    spl3_29 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.45  fof(f176,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(k3_xboole_0(sK1,X0),sK0)) ) | (~spl3_7 | ~spl3_29)),
% 0.22/0.45    inference(resolution,[],[f174,f61])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f60])).
% 0.22/0.45  fof(f174,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) ) | ~spl3_29),
% 0.22/0.45    inference(avatar_component_clause,[],[f173])).
% 0.22/0.45  fof(f175,plain,(
% 0.22/0.45    spl3_29 | ~spl3_2 | ~spl3_4 | ~spl3_28),
% 0.22/0.45    inference(avatar_split_clause,[],[f171,f167,f46,f36,f173])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    spl3_2 <=> v1_tops_2(sK1,sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.45  fof(f167,plain,(
% 0.22/0.45    spl3_28 <=> ! [X1,X0] : (~v1_tops_2(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X1,sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.45  fof(f171,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) ) | (~spl3_2 | ~spl3_4 | ~spl3_28)),
% 0.22/0.45    inference(subsumption_resolution,[],[f170,f48])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f46])).
% 0.22/0.45  fof(f170,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) ) | (~spl3_2 | ~spl3_28)),
% 0.22/0.45    inference(resolution,[],[f168,f38])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    v1_tops_2(sK1,sK0) | ~spl3_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f36])).
% 0.22/0.45  fof(f168,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_tops_2(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X1,sK0)) ) | ~spl3_28),
% 0.22/0.45    inference(avatar_component_clause,[],[f167])).
% 0.22/0.45  fof(f169,plain,(
% 0.22/0.45    spl3_28 | ~spl3_5 | ~spl3_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f165,f56,f51,f167])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    spl3_5 <=> l1_pre_topc(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    spl3_6 <=> ! [X1,X0,X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.45  fof(f165,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_tops_2(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X1,sK0)) ) | (~spl3_5 | ~spl3_6)),
% 0.22/0.45    inference(resolution,[],[f57,f53])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    l1_pre_topc(sK0) | ~spl3_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f51])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(X1,X0)) ) | ~spl3_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f56])).
% 0.22/0.45  fof(f112,plain,(
% 0.22/0.45    ~spl3_17 | spl3_1 | ~spl3_14),
% 0.22/0.45    inference(avatar_split_clause,[],[f107,f96,f31,f109])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    spl3_1 <=> v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f96,plain,(
% 0.22/0.45    spl3_14 <=> ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.45  fof(f107,plain,(
% 0.22/0.45    ~v1_tops_2(k3_xboole_0(sK1,sK2),sK0) | (spl3_1 | ~spl3_14)),
% 0.22/0.45    inference(superposition,[],[f33,f97])).
% 0.22/0.45  fof(f97,plain,(
% 0.22/0.45    ( ! [X0] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)) ) | ~spl3_14),
% 0.22/0.45    inference(avatar_component_clause,[],[f96])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl3_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f31])).
% 0.22/0.45  fof(f98,plain,(
% 0.22/0.45    spl3_14 | ~spl3_3 | ~spl3_11),
% 0.22/0.45    inference(avatar_split_clause,[],[f92,f76,f41,f96])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    spl3_11 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.45  fof(f92,plain,(
% 0.22/0.45    ( ! [X0] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)) ) | (~spl3_3 | ~spl3_11)),
% 0.22/0.45    inference(resolution,[],[f77,f43])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f41])).
% 0.22/0.45  fof(f77,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) ) | ~spl3_11),
% 0.22/0.45    inference(avatar_component_clause,[],[f76])).
% 0.22/0.45  fof(f91,plain,(
% 0.22/0.45    spl3_13 | ~spl3_4 | ~spl3_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f80,f68,f46,f88])).
% 0.22/0.45  fof(f68,plain,(
% 0.22/0.45    spl3_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.45  fof(f80,plain,(
% 0.22/0.45    r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_4 | ~spl3_9)),
% 0.22/0.45    inference(resolution,[],[f69,f48])).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f68])).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    spl3_11),
% 0.22/0.45    inference(avatar_split_clause,[],[f29,f76])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.45  fof(f74,plain,(
% 0.22/0.45    spl3_10),
% 0.22/0.45    inference(avatar_split_clause,[],[f28,f72])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    spl3_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f26,f68])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.45    inference(nnf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    spl3_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f27,f64])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    spl3_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f25,f60])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    spl3_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f24,f56])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.45    inference(flattening,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    spl3_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f19,f51])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    l1_pre_topc(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f16,f15,f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.45    inference(flattening,[],[f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,negated_conjecture,(
% 0.22/0.45    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.22/0.45    inference(negated_conjecture,[],[f6])).
% 0.22/0.45  fof(f6,conjecture,(
% 0.22/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tops_2)).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    spl3_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f20,f46])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    spl3_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f21,f41])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f22,f36])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    v1_tops_2(sK1,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ~spl3_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f23,f31])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (7588)------------------------------
% 0.22/0.45  % (7588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (7588)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (7588)Memory used [KB]: 10618
% 0.22/0.45  % (7588)Time elapsed: 0.006 s
% 0.22/0.45  % (7588)------------------------------
% 0.22/0.45  % (7588)------------------------------
% 0.22/0.45  % (7582)Success in time 0.092 s
%------------------------------------------------------------------------------
