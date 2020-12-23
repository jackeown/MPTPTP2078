%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 410 expanded)
%              Number of leaves         :   36 ( 148 expanded)
%              Depth                    :   12
%              Number of atoms          :  517 (2064 expanded)
%              Number of equality atoms :   46 (  89 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f493,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f157,f160,f168,f190,f220,f240,f262,f264,f267,f284,f309,f311,f313,f316,f354,f379,f492])).

fof(f492,plain,
    ( ~ spl3_20
    | spl3_9
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f268,f260,f217,f187,f278])).

fof(f278,plain,
    ( spl3_20
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f187,plain,
    ( spl3_9
  <=> v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f217,plain,
    ( spl3_12
  <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f260,plain,
    ( spl3_18
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f268,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(resolution,[],[f219,f261])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f260])).

fof(f219,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f217])).

fof(f379,plain,
    ( ~ spl3_3
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(resolution,[],[f376,f317])).

fof(f317,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f51,f236])).

fof(f236,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl3_15
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    & v3_tex_2(sK1,sK0)
    & ( v4_pre_topc(sK1,sK0)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_subset_1(X1,u1_struct_0(X0))
            & v3_tex_2(X1,X0)
            & ( v4_pre_topc(X1,X0)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(sK0))
          & v3_tex_2(X1,sK0)
          & ( v4_pre_topc(X1,sK0)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( v1_subset_1(X1,u1_struct_0(sK0))
        & v3_tex_2(X1,sK0)
        & ( v4_pre_topc(X1,sK0)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( v1_subset_1(sK1,u1_struct_0(sK0))
      & v3_tex_2(sK1,sK0)
      & ( v4_pre_topc(sK1,sK0)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( v1_subset_1(X1,u1_struct_0(X0))
                & v3_tex_2(X1,X0)
                & ( v4_pre_topc(X1,X0)
                  | v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( v1_subset_1(X1,u1_struct_0(X0))
              & v3_tex_2(X1,X0)
              & ( v4_pre_topc(X1,X0)
                | v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

fof(f376,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(resolution,[],[f356,f318])).

fof(f318,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f54,f236])).

fof(f54,plain,(
    v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f356,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) )
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(resolution,[],[f355,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f355,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f148,f236])).

fof(f148,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_3
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f354,plain,
    ( spl3_5
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | spl3_5
    | ~ spl3_15 ),
    inference(resolution,[],[f342,f55])).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f342,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_5
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f323,f103])).

fof(f103,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(backward_demodulation,[],[f95,f102])).

fof(f102,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f99,f78])).

fof(f78,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f57,f77])).

fof(f77,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f59,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f59,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f74,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f95,plain,(
    ! [X2] : k4_xboole_0(X2,X2) = k3_subset_1(X2,X2) ),
    inference(resolution,[],[f91,f93])).

fof(f93,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f72,f92])).

fof(f92,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f90,f78])).

fof(f90,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f73,f58])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f91,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2) ) ),
    inference(resolution,[],[f73,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f323,plain,
    ( ~ v1_xboole_0(k4_xboole_0(sK1,sK1))
    | spl3_5
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f156,f236])).

fof(f156,plain,
    ( ~ v1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl3_5
  <=> v1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f316,plain,
    ( ~ spl3_13
    | ~ spl3_4
    | spl3_15
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f315,f231,f165,f235,f150,f227])).

fof(f227,plain,
    ( spl3_13
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f150,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f165,plain,
    ( spl3_6
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f231,plain,
    ( spl3_14
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f315,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f314,f167])).

fof(f167,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f165])).

fof(f314,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_14 ),
    inference(resolution,[],[f233,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f233,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f231])).

fof(f313,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | spl3_14
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f312,f307,f231,f150,f80])).

fof(f80,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f307,plain,
    ( spl3_24
  <=> ! [X0] :
        ( ~ v3_tex_2(X0,sK0)
        | v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f312,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_24 ),
    inference(resolution,[],[f308,f53])).

fof(f53,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f308,plain,
    ( ! [X0] :
        ( ~ v3_tex_2(X0,sK0)
        | v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f307])).

fof(f311,plain,(
    ~ spl3_23 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | ~ spl3_23 ),
    inference(resolution,[],[f305,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f305,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl3_23
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f309,plain,
    ( spl3_23
    | ~ spl3_13
    | spl3_24 ),
    inference(avatar_split_clause,[],[f301,f307,f227,f303])).

fof(f301,plain,(
    ! [X0] :
      ( ~ v3_tex_2(X0,sK0)
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v1_tops_1(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f67,f48])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

fof(f284,plain,(
    spl3_20 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | spl3_20 ),
    inference(resolution,[],[f282,f72])).

fof(f282,plain,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl3_20 ),
    inference(resolution,[],[f280,f76])).

fof(f280,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f278])).

fof(f267,plain,
    ( ~ spl3_4
    | spl3_1
    | ~ spl3_2
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f266,f260,f84,f80,f150])).

fof(f84,plain,
    ( spl3_2
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f266,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_18 ),
    inference(resolution,[],[f261,f86])).

fof(f86,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f264,plain,(
    spl3_17 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | spl3_17 ),
    inference(resolution,[],[f258,f48])).

fof(f258,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl3_17
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f262,plain,
    ( ~ spl3_17
    | ~ spl3_13
    | spl3_18 ),
    inference(avatar_split_clause,[],[f254,f260,f227,f256])).

fof(f254,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f68,f49])).

fof(f49,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ v3_tdlat_3(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK2(X0),X0)
            & v4_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0),X0)
        & v4_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f240,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | spl3_13 ),
    inference(resolution,[],[f229,f50])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f229,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f227])).

fof(f220,plain,
    ( spl3_12
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f212,f80,f217])).

fof(f212,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f196,f114])).

fof(f114,plain,(
    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[],[f94,f101])).

fof(f101,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f98,f89])).

fof(f89,plain,(
    k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f73,f51])).

fof(f98,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f74,f51])).

fof(f94,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[],[f91,f72])).

fof(f196,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0)
      | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) ) ),
    inference(forward_demodulation,[],[f192,f94])).

fof(f192,plain,(
    ! [X0] :
      ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0) ) ),
    inference(resolution,[],[f174,f72])).

fof(f174,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | v4_pre_topc(X0,sK0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f171,f76])).

fof(f171,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | v4_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f65,f50])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f190,plain,
    ( spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f175,f187,f84])).

fof(f175,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f172,f89])).

fof(f172,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f171,f51])).

fof(f168,plain,
    ( spl3_6
    | ~ spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f162,f84,f150,f165])).

fof(f162,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f161,f86])).

fof(f161,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(resolution,[],[f60,f50])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f160,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f152,f51])).

fof(f152,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f150])).

fof(f157,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f144,f154,f150,f146])).

fof(f144,plain,
    ( ~ v1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f143,f89])).

fof(f143,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f75,f54])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(k3_subset_1(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & v1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tex_2)).

fof(f87,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f52,f84,f80])).

fof(f52,plain,
    ( v4_pre_topc(sK1,sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:06:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (19574)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (19576)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (19575)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (19572)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (19583)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (19583)Refutation not found, incomplete strategy% (19583)------------------------------
% 0.21/0.49  % (19583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19583)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (19583)Memory used [KB]: 10874
% 0.21/0.49  % (19583)Time elapsed: 0.060 s
% 0.21/0.49  % (19583)------------------------------
% 0.21/0.49  % (19583)------------------------------
% 0.21/0.49  % (19587)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (19579)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (19588)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (19582)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (19577)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (19574)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f493,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f87,f157,f160,f168,f190,f220,f240,f262,f264,f267,f284,f309,f311,f313,f316,f354,f379,f492])).
% 0.21/0.50  fof(f492,plain,(
% 0.21/0.50    ~spl3_20 | spl3_9 | ~spl3_12 | ~spl3_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f268,f260,f217,f187,f278])).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    spl3_20 <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    spl3_9 <=> v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    spl3_12 <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    spl3_18 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_12 | ~spl3_18)),
% 0.21/0.50    inference(resolution,[],[f219,f261])).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_pre_topc(X0,sK0) | v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f260])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~spl3_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f217])).
% 0.21/0.50  fof(f379,plain,(
% 0.21/0.50    ~spl3_3 | ~spl3_15),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f377])).
% 0.21/0.50  fof(f377,plain,(
% 0.21/0.50    $false | (~spl3_3 | ~spl3_15)),
% 0.21/0.50    inference(resolution,[],[f376,f317])).
% 0.21/0.50  fof(f317,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl3_15),
% 0.21/0.50    inference(backward_demodulation,[],[f51,f236])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    u1_struct_0(sK0) = sK1 | ~spl3_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f235])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    spl3_15 <=> u1_struct_0(sK0) = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    (v1_subset_1(sK1,u1_struct_0(sK0)) & v3_tex_2(sK1,sK0) & (v4_pre_topc(sK1,sK0) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f39,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v1_subset_1(X1,u1_struct_0(sK0)) & v3_tex_2(X1,sK0) & (v4_pre_topc(X1,sK0) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ? [X1] : (v1_subset_1(X1,u1_struct_0(sK0)) & v3_tex_2(X1,sK0) & (v4_pre_topc(X1,sK0) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (v1_subset_1(sK1,u1_struct_0(sK0)) & v3_tex_2(sK1,sK0) & (v4_pre_topc(sK1,sK0) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f18])).
% 0.21/0.50  fof(f18,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).
% 0.21/0.50  fof(f376,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl3_3 | ~spl3_15)),
% 0.21/0.50    inference(resolution,[],[f356,f318])).
% 0.21/0.50  fof(f318,plain,(
% 0.21/0.50    v1_subset_1(sK1,sK1) | ~spl3_15),
% 0.21/0.50    inference(backward_demodulation,[],[f54,f236])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f356,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_subset_1(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(sK1))) ) | (~spl3_3 | ~spl3_15)),
% 0.21/0.50    inference(resolution,[],[f355,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).
% 0.21/0.50  fof(f355,plain,(
% 0.21/0.50    v1_xboole_0(sK1) | (~spl3_3 | ~spl3_15)),
% 0.21/0.50    inference(forward_demodulation,[],[f148,f236])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK0)) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f146])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    spl3_3 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f354,plain,(
% 0.21/0.50    spl3_5 | ~spl3_15),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f353])).
% 0.21/0.50  fof(f353,plain,(
% 0.21/0.50    $false | (spl3_5 | ~spl3_15)),
% 0.21/0.50    inference(resolution,[],[f342,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f342,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_xboole_0) | (spl3_5 | ~spl3_15)),
% 0.21/0.50    inference(forward_demodulation,[],[f323,f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f95,f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f99,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(definition_unfolding,[],[f57,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f59,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 0.21/0.50    inference(resolution,[],[f74,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ( ! [X2] : (k4_xboole_0(X2,X2) = k3_subset_1(X2,X2)) )),
% 0.21/0.50    inference(resolution,[],[f91,f93])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.50    inference(superposition,[],[f72,f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(forward_demodulation,[],[f90,f78])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(resolution,[],[f73,f58])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2)) )),
% 0.21/0.50    inference(resolution,[],[f73,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.50    inference(unused_predicate_definition_removal,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f323,plain,(
% 0.21/0.50    ~v1_xboole_0(k4_xboole_0(sK1,sK1)) | (spl3_5 | ~spl3_15)),
% 0.21/0.50    inference(backward_demodulation,[],[f156,f236])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    ~v1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1)) | spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f154])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    spl3_5 <=> v1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f316,plain,(
% 0.21/0.50    ~spl3_13 | ~spl3_4 | spl3_15 | ~spl3_6 | ~spl3_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f315,f231,f165,f235,f150,f227])).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    spl3_13 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    spl3_6 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    spl3_14 <=> v1_tops_1(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.50  fof(f315,plain,(
% 0.21/0.50    u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_6 | ~spl3_14)),
% 0.21/0.50    inference(forward_demodulation,[],[f314,f167])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f165])).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_14),
% 0.21/0.50    inference(resolution,[],[f233,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    v1_tops_1(sK1,sK0) | ~spl3_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f231])).
% 0.21/0.50  fof(f313,plain,(
% 0.21/0.50    ~spl3_1 | ~spl3_4 | spl3_14 | ~spl3_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f312,f307,f231,f150,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f307,plain,(
% 0.21/0.50    spl3_24 <=> ! [X0] : (~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.50  fof(f312,plain,(
% 0.21/0.50    v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~spl3_24),
% 0.21/0.50    inference(resolution,[],[f308,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    v3_tex_2(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f308,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0)) ) | ~spl3_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f307])).
% 0.21/0.50  fof(f311,plain,(
% 0.21/0.50    ~spl3_23),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f310])).
% 0.21/0.50  fof(f310,plain,(
% 0.21/0.50    $false | ~spl3_23),
% 0.21/0.50    inference(resolution,[],[f305,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f305,plain,(
% 0.21/0.50    v2_struct_0(sK0) | ~spl3_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f303])).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    spl3_23 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.50  fof(f309,plain,(
% 0.21/0.50    spl3_23 | ~spl3_13 | spl3_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f301,f307,f227,f303])).
% 0.21/0.50  fof(f301,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_tex_2(X0,sK0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(X0,sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f67,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_tops_1(X1,X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    spl3_20),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f283])).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    $false | spl3_20),
% 0.21/0.50    inference(resolution,[],[f282,f72])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl3_20),
% 0.21/0.50    inference(resolution,[],[f280,f76])).
% 0.21/0.50  fof(f280,plain,(
% 0.21/0.50    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f278])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    ~spl3_4 | spl3_1 | ~spl3_2 | ~spl3_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f266,f260,f84,f80,f150])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl3_2 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f266,plain,(
% 0.21/0.50    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_18)),
% 0.21/0.50    inference(resolution,[],[f261,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    v4_pre_topc(sK1,sK0) | ~spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f84])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    spl3_17),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f263])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    $false | spl3_17),
% 0.21/0.50    inference(resolution,[],[f258,f48])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | spl3_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f256])).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    spl3_17 <=> v2_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    ~spl3_17 | ~spl3_13 | spl3_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f254,f260,f227,f256])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f68,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    v3_tdlat_3(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~v3_tdlat_3(X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK2(X0),X0) & v4_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0),X0) & v4_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(rectify,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    spl3_13),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f239])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    $false | spl3_13),
% 0.21/0.50    inference(resolution,[],[f229,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | spl3_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f227])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    spl3_12 | ~spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f212,f80,f217])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    ~v3_pre_topc(sK1,sK0) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.50    inference(superposition,[],[f196,f114])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 0.21/0.50    inference(superposition,[],[f94,f101])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 0.21/0.50    inference(forward_demodulation,[],[f98,f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1)),
% 0.21/0.50    inference(resolution,[],[f73,f51])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.50    inference(resolution,[],[f74,f51])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(resolution,[],[f91,f72])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f192,f94])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    ( ! [X0] : (v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0)) )),
% 0.21/0.50    inference(resolution,[],[f174,f72])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | v4_pre_topc(X0,sK0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)) )),
% 0.21/0.50    inference(resolution,[],[f171,f76])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f65,f50])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    spl3_2 | ~spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f175,f187,f84])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(forward_demodulation,[],[f172,f89])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(resolution,[],[f171,f51])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    spl3_6 | ~spl3_4 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f162,f84,f150,f165])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | ~spl3_2),
% 0.21/0.50    inference(resolution,[],[f161,f86])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) )),
% 0.21/0.50    inference(resolution,[],[f60,f50])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    spl3_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f158])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    $false | spl3_4),
% 0.21/0.50    inference(resolution,[],[f152,f51])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f150])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    spl3_3 | ~spl3_4 | ~spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f144,f154,f150,f146])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ~v1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.50    inference(forward_demodulation,[],[f143,f89])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.50    inference(resolution,[],[f75,f54])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(k3_subset_1(X0,X1)) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & v1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k3_subset_1(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tex_2)).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl3_1 | spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f84,f80])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    v4_pre_topc(sK1,sK0) | v3_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (19574)------------------------------
% 0.21/0.50  % (19574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19574)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (19574)Memory used [KB]: 6268
% 0.21/0.50  % (19574)Time elapsed: 0.063 s
% 0.21/0.50  % (19574)------------------------------
% 0.21/0.50  % (19574)------------------------------
% 0.21/0.50  % (19573)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (19571)Success in time 0.136 s
%------------------------------------------------------------------------------
