%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 149 expanded)
%              Number of leaves         :   26 (  71 expanded)
%              Depth                    :    7
%              Number of atoms          :  265 ( 544 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f59,f63,f69,f75,f82,f87,f93,f105,f116,f132,f151,f153])).

fof(f153,plain,
    ( spl3_5
    | ~ spl3_14
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl3_5
    | ~ spl3_14
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f137,f150])).

fof(f150,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl3_21
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f137,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | spl3_5
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f134,f104])).

fof(f104,plain,
    ( ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_14
  <=> ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f134,plain,
    ( ~ r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK1)
    | spl3_5
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f54,f131])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v2_tops_2(X0,sK0) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl3_18
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f54,plain,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_5
  <=> v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f151,plain,
    ( spl3_21
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f71,f67,f61,f149])).

fof(f61,plain,
    ( spl3_7
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f67,plain,
    ( spl3_8
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f71,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(superposition,[],[f62,f68])).

fof(f68,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f62,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f132,plain,
    ( ~ spl3_1
    | spl3_18
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f117,f114,f91,f42,f37,f130,f32])).

fof(f32,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f37,plain,
    ( spl3_2
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f42,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f91,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( v2_tops_2(X1,X0)
        | ~ v2_tops_2(X2,X0)
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f114,plain,
    ( spl3_16
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ v2_tops_2(sK1,sK0)
        | ~ r1_tarski(X0,sK1)
        | v2_tops_2(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f94,f115])).

fof(f115,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f114])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ v2_tops_2(sK1,sK0)
        | ~ r1_tarski(X0,sK1)
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(resolution,[],[f92,f44])).

fof(f44,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f92,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v2_tops_2(X2,X0)
        | ~ r1_tarski(X1,X2)
        | v2_tops_2(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f91])).

fof(f116,plain,
    ( ~ spl3_11
    | spl3_16
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f88,f80,f42,f114,f84])).

fof(f84,plain,
    ( spl3_11
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f80,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ r1_tarski(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_struct_0(sK0) )
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(resolution,[],[f81,f44])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ r1_tarski(X2,X1)
        | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_struct_0(X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f105,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f77,f73,f47,f103])).

fof(f47,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f73,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f77,plain,
    ( ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f49,f74])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f49,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f93,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f27,f91])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v2_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f87,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f64,f57,f32,f84])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f64,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f34,f58])).

fof(f58,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f34,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f82,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f25,f80])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ r1_tarski(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( r1_tarski(X2,X1)
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_tops_2)).

fof(f75,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f30,f73])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f69,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f29,f67])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f63,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f59,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f57])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f55,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v2_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17,f16])).

fof(f16,plain,
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

fof(f17,plain,
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

fof(f18,plain,
    ( ? [X2] :
        ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v2_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v2_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v2_tops_2(X1,X0)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X1,X0)
               => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).

fof(f50,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f37])).

fof(f23,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f32])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (11807)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (11807)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f154,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f59,f63,f69,f75,f82,f87,f93,f105,f116,f132,f151,f153])).
% 0.20/0.45  fof(f153,plain,(
% 0.20/0.45    spl3_5 | ~spl3_14 | ~spl3_18 | ~spl3_21),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f152])).
% 0.20/0.45  fof(f152,plain,(
% 0.20/0.45    $false | (spl3_5 | ~spl3_14 | ~spl3_18 | ~spl3_21)),
% 0.20/0.45    inference(subsumption_resolution,[],[f137,f150])).
% 0.20/0.45  fof(f150,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_21),
% 0.20/0.45    inference(avatar_component_clause,[],[f149])).
% 0.20/0.45  fof(f149,plain,(
% 0.20/0.45    spl3_21 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.45  fof(f137,plain,(
% 0.20/0.45    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | (spl3_5 | ~spl3_14 | ~spl3_18)),
% 0.20/0.45    inference(forward_demodulation,[],[f134,f104])).
% 0.20/0.45  fof(f104,plain,(
% 0.20/0.45    ( ! [X0] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)) ) | ~spl3_14),
% 0.20/0.45    inference(avatar_component_clause,[],[f103])).
% 0.20/0.45  fof(f103,plain,(
% 0.20/0.45    spl3_14 <=> ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.45  fof(f134,plain,(
% 0.20/0.45    ~r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK1) | (spl3_5 | ~spl3_18)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f54,f131])).
% 0.20/0.45  fof(f131,plain,(
% 0.20/0.45    ( ! [X0] : (~r1_tarski(X0,sK1) | v2_tops_2(X0,sK0)) ) | ~spl3_18),
% 0.20/0.45    inference(avatar_component_clause,[],[f130])).
% 0.20/0.45  fof(f130,plain,(
% 0.20/0.45    spl3_18 <=> ! [X0] : (~r1_tarski(X0,sK1) | v2_tops_2(X0,sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl3_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f52])).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    spl3_5 <=> v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.45  fof(f151,plain,(
% 0.20/0.45    spl3_21 | ~spl3_7 | ~spl3_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f71,f67,f61,f149])).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    spl3_7 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    spl3_8 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | (~spl3_7 | ~spl3_8)),
% 0.20/0.45    inference(superposition,[],[f62,f68])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) ) | ~spl3_8),
% 0.20/0.45    inference(avatar_component_clause,[],[f67])).
% 0.20/0.45  fof(f62,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f61])).
% 0.20/0.45  fof(f132,plain,(
% 0.20/0.45    ~spl3_1 | spl3_18 | ~spl3_2 | ~spl3_3 | ~spl3_12 | ~spl3_16),
% 0.20/0.45    inference(avatar_split_clause,[],[f117,f114,f91,f42,f37,f130,f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    spl3_1 <=> l1_pre_topc(sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    spl3_2 <=> v2_tops_2(sK1,sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.45  fof(f91,plain,(
% 0.20/0.45    spl3_12 <=> ! [X1,X0,X2] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.45  fof(f114,plain,(
% 0.20/0.45    spl3_16 <=> ! [X0] : (~r1_tarski(X0,sK1) | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.45  fof(f117,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_tops_2(sK1,sK0) | ~r1_tarski(X0,sK1) | v2_tops_2(X0,sK0) | ~l1_pre_topc(sK0)) ) | (~spl3_3 | ~spl3_12 | ~spl3_16)),
% 0.20/0.45    inference(subsumption_resolution,[],[f94,f115])).
% 0.20/0.45  fof(f115,plain,(
% 0.20/0.45    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,sK1)) ) | ~spl3_16),
% 0.20/0.45    inference(avatar_component_clause,[],[f114])).
% 0.20/0.45  fof(f94,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_tops_2(sK1,sK0) | ~r1_tarski(X0,sK1) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | (~spl3_3 | ~spl3_12)),
% 0.20/0.45    inference(resolution,[],[f92,f44])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f42])).
% 0.20/0.45  fof(f92,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl3_12),
% 0.20/0.45    inference(avatar_component_clause,[],[f91])).
% 0.20/0.45  fof(f116,plain,(
% 0.20/0.45    ~spl3_11 | spl3_16 | ~spl3_3 | ~spl3_10),
% 0.20/0.45    inference(avatar_split_clause,[],[f88,f80,f42,f114,f84])).
% 0.20/0.45  fof(f84,plain,(
% 0.20/0.45    spl3_11 <=> l1_struct_0(sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    spl3_10 <=> ! [X1,X0,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    ( ! [X0] : (~r1_tarski(X0,sK1) | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_struct_0(sK0)) ) | (~spl3_3 | ~spl3_10)),
% 0.20/0.45    inference(resolution,[],[f81,f44])).
% 0.20/0.45  fof(f81,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0)) ) | ~spl3_10),
% 0.20/0.45    inference(avatar_component_clause,[],[f80])).
% 0.20/0.45  fof(f105,plain,(
% 0.20/0.45    spl3_14 | ~spl3_4 | ~spl3_9),
% 0.20/0.45    inference(avatar_split_clause,[],[f77,f73,f47,f103])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    spl3_9 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.45  fof(f77,plain,(
% 0.20/0.45    ( ! [X0] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)) ) | (~spl3_4 | ~spl3_9)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f49,f74])).
% 0.20/0.45  fof(f74,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_9),
% 0.20/0.45    inference(avatar_component_clause,[],[f73])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f47])).
% 0.20/0.45  fof(f93,plain,(
% 0.20/0.45    spl3_12),
% 0.20/0.45    inference(avatar_split_clause,[],[f27,f91])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((v2_tops_2(X1,X0) | (~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    spl3_11 | ~spl3_1 | ~spl3_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f64,f57,f32,f84])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    spl3_6 <=> ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    l1_struct_0(sK0) | (~spl3_1 | ~spl3_6)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f34,f58])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) ) | ~spl3_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f57])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    l1_pre_topc(sK0) | ~spl3_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f32])).
% 0.20/0.45  fof(f82,plain,(
% 0.20/0.45    spl3_10),
% 0.20/0.45    inference(avatar_split_clause,[],[f25,f80])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_struct_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (r1_tarski(X2,X1) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_tops_2)).
% 0.20/0.45  fof(f75,plain,(
% 0.20/0.45    spl3_9),
% 0.20/0.45    inference(avatar_split_clause,[],[f30,f73])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    spl3_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f29,f67])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    spl3_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f28,f61])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    spl3_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f26,f57])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ~spl3_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f24,f52])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17,f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.20/0.45    inference(negated_conjecture,[],[f7])).
% 0.20/0.45  fof(f7,conjecture,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    spl3_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f22,f47])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    spl3_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f21,f42])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    spl3_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f23,f37])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    v2_tops_2(sK1,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    spl3_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f20,f32])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    l1_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (11807)------------------------------
% 0.20/0.45  % (11807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (11807)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (11807)Memory used [KB]: 6140
% 0.20/0.45  % (11807)Time elapsed: 0.012 s
% 0.20/0.45  % (11807)------------------------------
% 0.20/0.45  % (11807)------------------------------
% 0.20/0.45  % (11798)Success in time 0.094 s
%------------------------------------------------------------------------------
