%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:21 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 204 expanded)
%              Number of leaves         :   22 (  93 expanded)
%              Depth                    :    8
%              Number of atoms          :  272 ( 944 expanded)
%              Number of equality atoms :   32 (  58 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f62,f67,f72,f77,f103,f121,f139,f154,f173])).

fof(f173,plain,
    ( spl3_17
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f172,f118,f64,f151])).

fof(f151,plain,
    ( spl3_17
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f64,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f118,plain,
    ( spl3_12
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f172,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f171,f36])).

fof(f36,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f33,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f171,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1)))
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f120,f82])).

fof(f82,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f66,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f66,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f120,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f154,plain,
    ( ~ spl3_17
    | ~ spl3_5
    | ~ spl3_7
    | spl3_15 ),
    inference(avatar_split_clause,[],[f144,f136,f69,f59,f151])).

fof(f59,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f69,plain,
    ( spl3_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f136,plain,
    ( spl3_15
  <=> v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f144,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))
    | ~ spl3_5
    | ~ spl3_7
    | spl3_15 ),
    inference(unit_resulting_resolution,[],[f71,f138,f133,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f133,plain,
    ( ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f78,f81])).

fof(f81,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f61,f37])).

fof(f61,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f78,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f61,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f138,plain,
    ( ~ v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f136])).

fof(f71,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f139,plain,
    ( ~ spl3_15
    | spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f132,f59,f39,f136])).

fof(f39,plain,
    ( spl3_1
  <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f132,plain,
    ( ~ v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | spl3_1
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f41,f81])).

fof(f41,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f121,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f116,f100,f74,f69,f64,f59,f54,f44,f118])).

fof(f44,plain,
    ( spl3_2
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f54,plain,
    ( spl3_4
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f74,plain,
    ( spl3_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f100,plain,
    ( spl3_10
  <=> k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f116,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f114,f102])).

fof(f102,plain,
    ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f114,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f76,f71,f46,f56,f66,f61,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

fof(f56,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f46,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f76,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f103,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f91,f69,f59,f49,f100])).

fof(f49,plain,
    ( spl3_3
  <=> v1_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f91,plain,
    ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f71,f51,f61,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,
    ( v1_tops_1(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f77,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f21,f74])).

fof(f21,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v1_tops_1(sK2,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_pre_topc(X2,X0)
                & v1_tops_1(X2,X0)
                & v1_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_pre_topc(X2,sK0)
              & v1_tops_1(X2,sK0)
              & v1_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v3_pre_topc(X2,sK0)
            & v1_tops_1(X2,sK0)
            & v1_tops_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v3_pre_topc(X2,sK0)
          & v1_tops_1(X2,sK0)
          & v1_tops_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v3_pre_topc(X2,sK0)
        & v1_tops_1(X2,sK0)
        & v1_tops_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v3_pre_topc(sK2,sK0)
      & v1_tops_1(sK2,sK0)
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v1_tops_1(X2,X0)
                    & v1_tops_1(X1,X0) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v1_tops_1(X2,X0)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).

fof(f72,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f22,f69])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f23,f64])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f24,f59])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f26,f49])).

fof(f26,plain,(
    v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f27,f44])).

fof(f27,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f28,f39])).

fof(f28,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 10:17:59 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.23/0.47  % (23961)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.47  % (23961)Refutation found. Thanks to Tanya!
% 0.23/0.47  % SZS status Theorem for theBenchmark
% 0.23/0.47  % SZS output start Proof for theBenchmark
% 0.23/0.47  fof(f174,plain,(
% 0.23/0.47    $false),
% 0.23/0.47    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f62,f67,f72,f77,f103,f121,f139,f154,f173])).
% 0.23/0.47  fof(f173,plain,(
% 0.23/0.47    spl3_17 | ~spl3_6 | ~spl3_12),
% 0.23/0.47    inference(avatar_split_clause,[],[f172,f118,f64,f151])).
% 0.23/0.47  fof(f151,plain,(
% 0.23/0.47    spl3_17 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))),
% 0.23/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.23/0.47  fof(f64,plain,(
% 0.23/0.47    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.23/0.47  fof(f118,plain,(
% 0.23/0.47    spl3_12 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))),
% 0.23/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.23/0.47  fof(f172,plain,(
% 0.23/0.47    k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) | (~spl3_6 | ~spl3_12)),
% 0.23/0.47    inference(forward_demodulation,[],[f171,f36])).
% 0.23/0.47  fof(f36,plain,(
% 0.23/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.23/0.47    inference(definition_unfolding,[],[f32,f33,f33])).
% 0.23/0.47  fof(f33,plain,(
% 0.23/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.23/0.47    inference(cnf_transformation,[],[f4])).
% 0.23/0.47  fof(f4,axiom,(
% 0.23/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.23/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.23/0.47  fof(f32,plain,(
% 0.23/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.47    inference(cnf_transformation,[],[f1])).
% 0.23/0.47  fof(f1,axiom,(
% 0.23/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.47  fof(f171,plain,(
% 0.23/0.47    k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1))) | (~spl3_6 | ~spl3_12)),
% 0.23/0.47    inference(forward_demodulation,[],[f120,f82])).
% 0.23/0.47  fof(f82,plain,(
% 0.23/0.47    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))) ) | ~spl3_6),
% 0.23/0.47    inference(unit_resulting_resolution,[],[f66,f37])).
% 0.23/0.47  fof(f37,plain,(
% 0.23/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.23/0.47    inference(definition_unfolding,[],[f35,f33])).
% 0.23/0.47  fof(f35,plain,(
% 0.23/0.47    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.23/0.47    inference(cnf_transformation,[],[f15])).
% 0.23/0.47  fof(f15,plain,(
% 0.23/0.47    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.23/0.47    inference(ennf_transformation,[],[f3])).
% 0.23/0.47  fof(f3,axiom,(
% 0.23/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.23/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.23/0.47  fof(f66,plain,(
% 0.23/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.23/0.47    inference(avatar_component_clause,[],[f64])).
% 0.23/0.47  fof(f120,plain,(
% 0.23/0.47    k2_struct_0(sK0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) | ~spl3_12),
% 0.23/0.47    inference(avatar_component_clause,[],[f118])).
% 0.23/0.47  fof(f154,plain,(
% 0.23/0.47    ~spl3_17 | ~spl3_5 | ~spl3_7 | spl3_15),
% 0.23/0.47    inference(avatar_split_clause,[],[f144,f136,f69,f59,f151])).
% 0.23/0.47  fof(f59,plain,(
% 0.23/0.47    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.23/0.47  fof(f69,plain,(
% 0.23/0.47    spl3_7 <=> l1_pre_topc(sK0)),
% 0.23/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.23/0.47  fof(f136,plain,(
% 0.23/0.47    spl3_15 <=> v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.23/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.23/0.47  fof(f144,plain,(
% 0.23/0.47    k2_struct_0(sK0) != k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) | (~spl3_5 | ~spl3_7 | spl3_15)),
% 0.23/0.47    inference(unit_resulting_resolution,[],[f71,f138,f133,f30])).
% 0.23/0.47  fof(f30,plain,(
% 0.23/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(X1,X0)) )),
% 0.23/0.47    inference(cnf_transformation,[],[f20])).
% 0.23/0.47  fof(f20,plain,(
% 0.23/0.47    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.47    inference(nnf_transformation,[],[f11])).
% 0.23/0.47  fof(f11,plain,(
% 0.23/0.47    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.47    inference(ennf_transformation,[],[f5])).
% 0.23/0.47  fof(f5,axiom,(
% 0.23/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 0.23/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.23/0.47  fof(f133,plain,(
% 0.23/0.47    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_5),
% 0.23/0.47    inference(backward_demodulation,[],[f78,f81])).
% 0.23/0.47  fof(f81,plain,(
% 0.23/0.47    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))) ) | ~spl3_5),
% 0.23/0.47    inference(unit_resulting_resolution,[],[f61,f37])).
% 0.23/0.47  fof(f61,plain,(
% 0.23/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.23/0.47    inference(avatar_component_clause,[],[f59])).
% 0.23/0.47  fof(f78,plain,(
% 0.23/0.47    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_5),
% 0.23/0.47    inference(unit_resulting_resolution,[],[f61,f34])).
% 0.23/0.47  fof(f34,plain,(
% 0.23/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.23/0.47    inference(cnf_transformation,[],[f14])).
% 0.23/0.47  fof(f14,plain,(
% 0.23/0.47    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.23/0.47    inference(ennf_transformation,[],[f2])).
% 0.23/0.47  fof(f2,axiom,(
% 0.23/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.23/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.23/0.47  fof(f138,plain,(
% 0.23/0.47    ~v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | spl3_15),
% 0.23/0.47    inference(avatar_component_clause,[],[f136])).
% 0.23/0.47  fof(f71,plain,(
% 0.23/0.47    l1_pre_topc(sK0) | ~spl3_7),
% 0.23/0.47    inference(avatar_component_clause,[],[f69])).
% 0.23/0.47  fof(f139,plain,(
% 0.23/0.47    ~spl3_15 | spl3_1 | ~spl3_5),
% 0.23/0.47    inference(avatar_split_clause,[],[f132,f59,f39,f136])).
% 0.23/0.47  fof(f39,plain,(
% 0.23/0.47    spl3_1 <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.23/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.47  fof(f132,plain,(
% 0.23/0.47    ~v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | (spl3_1 | ~spl3_5)),
% 0.23/0.47    inference(backward_demodulation,[],[f41,f81])).
% 0.23/0.47  fof(f41,plain,(
% 0.23/0.47    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_1),
% 0.23/0.47    inference(avatar_component_clause,[],[f39])).
% 0.23/0.47  fof(f121,plain,(
% 0.23/0.47    spl3_12 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_10),
% 0.23/0.47    inference(avatar_split_clause,[],[f116,f100,f74,f69,f64,f59,f54,f44,f118])).
% 0.23/0.47  fof(f44,plain,(
% 0.23/0.47    spl3_2 <=> v3_pre_topc(sK2,sK0)),
% 0.23/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.47  fof(f54,plain,(
% 0.23/0.47    spl3_4 <=> v1_tops_1(sK1,sK0)),
% 0.23/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.23/0.47  fof(f74,plain,(
% 0.23/0.47    spl3_8 <=> v2_pre_topc(sK0)),
% 0.23/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.23/0.47  fof(f100,plain,(
% 0.23/0.47    spl3_10 <=> k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)),
% 0.23/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.23/0.47  fof(f116,plain,(
% 0.23/0.47    k2_struct_0(sK0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) | (~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_10)),
% 0.23/0.47    inference(forward_demodulation,[],[f114,f102])).
% 0.23/0.47  fof(f102,plain,(
% 0.23/0.47    k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) | ~spl3_10),
% 0.23/0.47    inference(avatar_component_clause,[],[f100])).
% 0.23/0.47  fof(f114,plain,(
% 0.23/0.47    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) | (~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.23/0.47    inference(unit_resulting_resolution,[],[f76,f71,f46,f56,f66,f61,f31])).
% 0.23/0.47  fof(f31,plain,(
% 0.23/0.47    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))) )),
% 0.23/0.47    inference(cnf_transformation,[],[f13])).
% 0.23/0.47  fof(f13,plain,(
% 0.23/0.47    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.47    inference(flattening,[],[f12])).
% 0.23/0.47  fof(f12,plain,(
% 0.23/0.47    ! [X0] : (! [X1] : ((! [X2] : ((k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.47    inference(ennf_transformation,[],[f6])).
% 0.23/0.47  fof(f6,axiom,(
% 0.23/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.23/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).
% 0.23/0.47  fof(f56,plain,(
% 0.23/0.47    v1_tops_1(sK1,sK0) | ~spl3_4),
% 0.23/0.47    inference(avatar_component_clause,[],[f54])).
% 0.23/0.47  fof(f46,plain,(
% 0.23/0.47    v3_pre_topc(sK2,sK0) | ~spl3_2),
% 0.23/0.47    inference(avatar_component_clause,[],[f44])).
% 0.23/0.47  fof(f76,plain,(
% 0.23/0.47    v2_pre_topc(sK0) | ~spl3_8),
% 0.23/0.47    inference(avatar_component_clause,[],[f74])).
% 0.23/0.47  fof(f103,plain,(
% 0.23/0.47    spl3_10 | ~spl3_3 | ~spl3_5 | ~spl3_7),
% 0.23/0.47    inference(avatar_split_clause,[],[f91,f69,f59,f49,f100])).
% 0.23/0.47  fof(f49,plain,(
% 0.23/0.47    spl3_3 <=> v1_tops_1(sK2,sK0)),
% 0.23/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.47  fof(f91,plain,(
% 0.23/0.47    k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) | (~spl3_3 | ~spl3_5 | ~spl3_7)),
% 0.23/0.47    inference(unit_resulting_resolution,[],[f71,f51,f61,f29])).
% 0.23/0.47  fof(f29,plain,(
% 0.23/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0)) )),
% 0.23/0.47    inference(cnf_transformation,[],[f20])).
% 0.23/0.47  fof(f51,plain,(
% 0.23/0.47    v1_tops_1(sK2,sK0) | ~spl3_3),
% 0.23/0.47    inference(avatar_component_clause,[],[f49])).
% 0.23/0.47  fof(f77,plain,(
% 0.23/0.47    spl3_8),
% 0.23/0.47    inference(avatar_split_clause,[],[f21,f74])).
% 0.23/0.47  fof(f21,plain,(
% 0.23/0.47    v2_pre_topc(sK0)),
% 0.23/0.47    inference(cnf_transformation,[],[f19])).
% 0.23/0.47  fof(f19,plain,(
% 0.23/0.47    ((~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.23/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17,f16])).
% 0.23/0.47  fof(f16,plain,(
% 0.23/0.47    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.23/0.47    introduced(choice_axiom,[])).
% 0.23/0.47  fof(f17,plain,(
% 0.23/0.47    ? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.47    introduced(choice_axiom,[])).
% 0.23/0.47  fof(f18,plain,(
% 0.23/0.47    ? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.47    introduced(choice_axiom,[])).
% 0.23/0.47  fof(f10,plain,(
% 0.23/0.47    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.47    inference(flattening,[],[f9])).
% 0.23/0.47  fof(f9,plain,(
% 0.23/0.47    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.23/0.47    inference(ennf_transformation,[],[f8])).
% 0.23/0.47  fof(f8,negated_conjecture,(
% 0.23/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.23/0.47    inference(negated_conjecture,[],[f7])).
% 0.23/0.47  fof(f7,conjecture,(
% 0.23/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.23/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).
% 0.23/0.47  fof(f72,plain,(
% 0.23/0.47    spl3_7),
% 0.23/0.47    inference(avatar_split_clause,[],[f22,f69])).
% 0.23/0.47  fof(f22,plain,(
% 0.23/0.47    l1_pre_topc(sK0)),
% 0.23/0.47    inference(cnf_transformation,[],[f19])).
% 0.23/0.47  fof(f67,plain,(
% 0.23/0.47    spl3_6),
% 0.23/0.47    inference(avatar_split_clause,[],[f23,f64])).
% 0.23/0.47  fof(f23,plain,(
% 0.23/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.47    inference(cnf_transformation,[],[f19])).
% 0.23/0.47  fof(f62,plain,(
% 0.23/0.47    spl3_5),
% 0.23/0.47    inference(avatar_split_clause,[],[f24,f59])).
% 0.23/0.47  fof(f24,plain,(
% 0.23/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.47    inference(cnf_transformation,[],[f19])).
% 0.23/0.47  fof(f57,plain,(
% 0.23/0.47    spl3_4),
% 0.23/0.47    inference(avatar_split_clause,[],[f25,f54])).
% 0.23/0.47  fof(f25,plain,(
% 0.23/0.47    v1_tops_1(sK1,sK0)),
% 0.23/0.47    inference(cnf_transformation,[],[f19])).
% 0.23/0.47  fof(f52,plain,(
% 0.23/0.47    spl3_3),
% 0.23/0.47    inference(avatar_split_clause,[],[f26,f49])).
% 0.23/0.47  fof(f26,plain,(
% 0.23/0.47    v1_tops_1(sK2,sK0)),
% 0.23/0.47    inference(cnf_transformation,[],[f19])).
% 0.23/0.47  fof(f47,plain,(
% 0.23/0.47    spl3_2),
% 0.23/0.47    inference(avatar_split_clause,[],[f27,f44])).
% 0.23/0.47  fof(f27,plain,(
% 0.23/0.47    v3_pre_topc(sK2,sK0)),
% 0.23/0.47    inference(cnf_transformation,[],[f19])).
% 0.23/0.47  fof(f42,plain,(
% 0.23/0.47    ~spl3_1),
% 0.23/0.47    inference(avatar_split_clause,[],[f28,f39])).
% 0.23/0.47  fof(f28,plain,(
% 0.23/0.47    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.23/0.47    inference(cnf_transformation,[],[f19])).
% 0.23/0.47  % SZS output end Proof for theBenchmark
% 0.23/0.47  % (23961)------------------------------
% 0.23/0.47  % (23961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.47  % (23961)Termination reason: Refutation
% 0.23/0.47  
% 0.23/0.47  % (23961)Memory used [KB]: 6268
% 0.23/0.47  % (23961)Time elapsed: 0.070 s
% 0.23/0.47  % (23961)------------------------------
% 0.23/0.47  % (23961)------------------------------
% 0.23/0.47  % (23954)Success in time 0.102 s
%------------------------------------------------------------------------------
