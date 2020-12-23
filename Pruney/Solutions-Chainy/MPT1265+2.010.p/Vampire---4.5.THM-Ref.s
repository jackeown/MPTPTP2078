%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 298 expanded)
%              Number of leaves         :   33 ( 134 expanded)
%              Depth                    :    9
%              Number of atoms          :  442 (1208 expanded)
%              Number of equality atoms :   50 ( 105 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f389,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f78,f83,f88,f96,f104,f145,f150,f155,f159,f191,f199,f214,f247,f268,f327,f388])).

fof(f388,plain,
    ( ~ spl3_14
    | spl3_28 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | ~ spl3_14
    | spl3_28 ),
    inference(unit_resulting_resolution,[],[f166,f324,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f324,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl3_28
  <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f166,plain,
    ( ! [X0] : r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),k2_struct_0(sK0))
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f139,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f41])).

fof(f41,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f139,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl3_14
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f327,plain,
    ( ~ spl3_7
    | spl3_19
    | ~ spl3_28
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f326,f265,f100,f322,f196,f80])).

fof(f80,plain,
    ( spl3_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f196,plain,
    ( spl3_19
  <=> v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f100,plain,
    ( spl3_10
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f265,plain,
    ( spl3_24
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f326,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f319,f102])).

fof(f102,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f319,plain,
    ( v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_24 ),
    inference(trivial_inequality_removal,[],[f318])).

fof(f318,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_24 ),
    inference(superposition,[],[f39,f267])).

fof(f267,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f265])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f268,plain,
    ( spl3_24
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f263,f238,f210,f189,f152,f147,f65,f55,f265])).

fof(f55,plain,
    ( spl3_2
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f65,plain,
    ( spl3_4
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f147,plain,
    ( spl3_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f152,plain,
    ( spl3_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f189,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
        | ~ v1_tops_1(X1,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f210,plain,
    ( spl3_20
  <=> k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f238,plain,
    ( spl3_21
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f263,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f262,f240])).

fof(f240,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f238])).

fof(f262,plain,
    ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f261,f212])).

fof(f212,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f261,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1)))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f251,f174])).

fof(f174,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f149,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f45,f41])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f149,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f147])).

fof(f251,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f57,f67,f149,f154,f190])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ v1_tops_1(X1,sK0)
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f189])).

fof(f154,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f152])).

fof(f67,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f57,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f247,plain,
    ( spl3_21
    | ~ spl3_17
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f235,f100,f80,f60,f152,f238])).

fof(f60,plain,
    ( spl3_3
  <=> v1_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f235,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK2)
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(resolution,[],[f181,f62])).

fof(f62,plain,
    ( v1_tops_1(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f180,f102])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl3_7 ),
    inference(resolution,[],[f38,f82])).

fof(f82,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f214,plain,
    ( spl3_20
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f208,f152,f147,f210])).

fof(f208,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1))
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(superposition,[],[f175,f200])).

fof(f200,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(X0,sK1))
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f168,f174])).

fof(f168,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK1) = k9_subset_1(k2_struct_0(sK0),sK1,X0)
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f149,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f175,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f154,f48])).

fof(f199,plain,
    ( ~ spl3_19
    | spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f194,f152,f142,f196])).

fof(f142,plain,
    ( spl3_15
  <=> v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f194,plain,
    ( ~ v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | spl3_15
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f144,f175])).

fof(f144,plain,
    ( ~ v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f191,plain,
    ( ~ spl3_7
    | spl3_18
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f187,f100,f85,f189,f80])).

fof(f85,plain,
    ( spl3_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v1_tops_1(X1,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f186,f102])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v1_tops_1(X1,sK0)
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f185,f102])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v1_tops_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f184,f102])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl3_8 ),
    inference(resolution,[],[f40,f87])).

fof(f87,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f159,plain,
    ( spl3_14
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f157,f147,f137])).

fof(f157,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_16 ),
    inference(resolution,[],[f149,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f155,plain,
    ( spl3_17
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f130,f100,f70,f152])).

fof(f70,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f130,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f72,f102])).

fof(f72,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f150,plain,
    ( spl3_16
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f129,f100,f75,f147])).

fof(f75,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f129,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f77,f102])).

fof(f77,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f145,plain,
    ( ~ spl3_15
    | spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f128,f100,f50,f142])).

fof(f50,plain,
    ( spl3_1
  <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f128,plain,
    ( ~ v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f52,f102])).

fof(f52,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f104,plain,
    ( spl3_10
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f98,f92,f100])).

fof(f92,plain,
    ( spl3_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f98,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(resolution,[],[f94,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f94,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f96,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f90,f80,f92])).

fof(f90,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f37,f82])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f88,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f85])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v1_tops_1(sK2,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24,f23,f22])).

fof(f22,plain,
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

fof(f23,plain,
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

fof(f24,plain,
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

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f83,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f29,f80])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f30,f75])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f31,f70])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f32,f65])).

fof(f32,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f33,f60])).

fof(f33,plain,(
    v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f34,f55])).

fof(f34,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f35,f50])).

fof(f35,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:36:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (30811)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (30813)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (30810)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (30815)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (30812)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (30819)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (30813)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f389,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f78,f83,f88,f96,f104,f145,f150,f155,f159,f191,f199,f214,f247,f268,f327,f388])).
% 0.21/0.47  fof(f388,plain,(
% 0.21/0.47    ~spl3_14 | spl3_28),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f383])).
% 0.21/0.47  fof(f383,plain,(
% 0.21/0.47    $false | (~spl3_14 | spl3_28)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f166,f324,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.47    inference(nnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.47  fof(f324,plain,(
% 0.21/0.47    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_28),
% 0.21/0.47    inference(avatar_component_clause,[],[f322])).
% 0.21/0.47  fof(f322,plain,(
% 0.21/0.47    spl3_28 <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),k2_struct_0(sK0))) ) | ~spl3_14),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f139,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f44,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    r1_tarski(sK1,k2_struct_0(sK0)) | ~spl3_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f137])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    spl3_14 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.47  fof(f327,plain,(
% 0.21/0.47    ~spl3_7 | spl3_19 | ~spl3_28 | ~spl3_10 | ~spl3_24),
% 0.21/0.47    inference(avatar_split_clause,[],[f326,f265,f100,f322,f196,f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl3_7 <=> l1_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f196,plain,(
% 0.21/0.47    spl3_19 <=> v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    spl3_10 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.47  fof(f265,plain,(
% 0.21/0.47    spl3_24 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.47  fof(f326,plain,(
% 0.21/0.47    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | ~l1_pre_topc(sK0) | (~spl3_10 | ~spl3_24)),
% 0.21/0.47    inference(forward_demodulation,[],[f319,f102])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f100])).
% 0.21/0.47  fof(f319,plain,(
% 0.21/0.47    v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_24),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f318])).
% 0.21/0.47  fof(f318,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_24),
% 0.21/0.47    inference(superposition,[],[f39,f267])).
% 0.21/0.47  fof(f267,plain,(
% 0.21/0.47    k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) | ~spl3_24),
% 0.21/0.47    inference(avatar_component_clause,[],[f265])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.21/0.47  fof(f268,plain,(
% 0.21/0.47    spl3_24 | ~spl3_2 | ~spl3_4 | ~spl3_16 | ~spl3_17 | ~spl3_18 | ~spl3_20 | ~spl3_21),
% 0.21/0.47    inference(avatar_split_clause,[],[f263,f238,f210,f189,f152,f147,f65,f55,f265])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl3_2 <=> v3_pre_topc(sK2,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl3_4 <=> v1_tops_1(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    spl3_16 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    spl3_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.47  fof(f189,plain,(
% 0.21/0.47    spl3_18 <=> ! [X1,X0] : (k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~v1_tops_1(X1,sK0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    spl3_20 <=> k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.47  fof(f238,plain,(
% 0.21/0.47    spl3_21 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.47  fof(f263,plain,(
% 0.21/0.47    k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) | (~spl3_2 | ~spl3_4 | ~spl3_16 | ~spl3_17 | ~spl3_18 | ~spl3_20 | ~spl3_21)),
% 0.21/0.47    inference(forward_demodulation,[],[f262,f240])).
% 0.21/0.47  fof(f240,plain,(
% 0.21/0.47    k2_struct_0(sK0) = k2_pre_topc(sK0,sK2) | ~spl3_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f238])).
% 0.21/0.47  fof(f262,plain,(
% 0.21/0.47    k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,sK2) | (~spl3_2 | ~spl3_4 | ~spl3_16 | ~spl3_17 | ~spl3_18 | ~spl3_20)),
% 0.21/0.47    inference(forward_demodulation,[],[f261,f212])).
% 0.21/0.47  fof(f212,plain,(
% 0.21/0.47    k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1)) | ~spl3_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f210])).
% 0.21/0.47  fof(f261,plain,(
% 0.21/0.47    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1))) | (~spl3_2 | ~spl3_4 | ~spl3_16 | ~spl3_17 | ~spl3_18)),
% 0.21/0.47    inference(forward_demodulation,[],[f251,f174])).
% 0.21/0.47  fof(f174,plain,(
% 0.21/0.47    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))) ) | ~spl3_16),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f149,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f45,f41])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f147])).
% 0.21/0.47  fof(f251,plain,(
% 0.21/0.47    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) | (~spl3_2 | ~spl3_4 | ~spl3_16 | ~spl3_17 | ~spl3_18)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f57,f67,f149,f154,f190])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~v1_tops_1(X1,sK0) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f189])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f152])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    v1_tops_1(sK1,sK0) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f65])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    v3_pre_topc(sK2,sK0) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f55])).
% 0.21/0.47  fof(f247,plain,(
% 0.21/0.47    spl3_21 | ~spl3_17 | ~spl3_3 | ~spl3_7 | ~spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f235,f100,f80,f60,f152,f238])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl3_3 <=> v1_tops_1(sK2,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f235,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK2) | (~spl3_3 | ~spl3_7 | ~spl3_10)),
% 0.21/0.47    inference(resolution,[],[f181,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    v1_tops_1(sK2,sK0) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f60])).
% 0.21/0.47  fof(f181,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | (~spl3_7 | ~spl3_10)),
% 0.21/0.47    inference(forward_demodulation,[],[f180,f102])).
% 0.21/0.47  fof(f180,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | ~spl3_7),
% 0.21/0.47    inference(resolution,[],[f38,f82])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    l1_pre_topc(sK0) | ~spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f80])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f214,plain,(
% 0.21/0.47    spl3_20 | ~spl3_16 | ~spl3_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f208,f152,f147,f210])).
% 0.21/0.47  fof(f208,plain,(
% 0.21/0.47    k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1)) | (~spl3_16 | ~spl3_17)),
% 0.21/0.47    inference(superposition,[],[f175,f200])).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(X0,sK1))) ) | ~spl3_16),
% 0.21/0.47    inference(forward_demodulation,[],[f168,f174])).
% 0.21/0.47  fof(f168,plain,(
% 0.21/0.47    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK1) = k9_subset_1(k2_struct_0(sK0),sK1,X0)) ) | ~spl3_16),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f149,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))) ) | ~spl3_17),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f154,f48])).
% 0.21/0.47  fof(f199,plain,(
% 0.21/0.47    ~spl3_19 | spl3_15 | ~spl3_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f194,f152,f142,f196])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    spl3_15 <=> v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.47  fof(f194,plain,(
% 0.21/0.47    ~v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | (spl3_15 | ~spl3_17)),
% 0.21/0.47    inference(backward_demodulation,[],[f144,f175])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    ~v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0) | spl3_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f142])).
% 0.21/0.47  fof(f191,plain,(
% 0.21/0.47    ~spl3_7 | spl3_18 | ~spl3_8 | ~spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f187,f100,f85,f189,f80])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    spl3_8 <=> v2_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.47  fof(f187,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v1_tops_1(X1,sK0) | ~l1_pre_topc(sK0)) ) | (~spl3_8 | ~spl3_10)),
% 0.21/0.47    inference(forward_demodulation,[],[f186,f102])).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v1_tops_1(X1,sK0) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | (~spl3_8 | ~spl3_10)),
% 0.21/0.47    inference(forward_demodulation,[],[f185,f102])).
% 0.21/0.47  fof(f185,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v1_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | (~spl3_8 | ~spl3_10)),
% 0.21/0.47    inference(forward_demodulation,[],[f184,f102])).
% 0.21/0.47  fof(f184,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | ~spl3_8),
% 0.21/0.47    inference(resolution,[],[f40,f87])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    v2_pre_topc(sK0) | ~spl3_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f85])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((! [X2] : ((k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    spl3_14 | ~spl3_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f157,f147,f137])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    r1_tarski(sK1,k2_struct_0(sK0)) | ~spl3_16),
% 0.21/0.47    inference(resolution,[],[f149,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    spl3_17 | ~spl3_5 | ~spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f130,f100,f70,f152])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_5 | ~spl3_10)),
% 0.21/0.47    inference(backward_demodulation,[],[f72,f102])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f70])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    spl3_16 | ~spl3_6 | ~spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f129,f100,f75,f147])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_6 | ~spl3_10)),
% 0.21/0.47    inference(backward_demodulation,[],[f77,f102])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f75])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    ~spl3_15 | spl3_1 | ~spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f128,f100,f50,f142])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl3_1 <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    ~v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0) | (spl3_1 | ~spl3_10)),
% 0.21/0.47    inference(backward_demodulation,[],[f52,f102])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    spl3_10 | ~spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f98,f92,f100])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl3_9 <=> l1_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.21/0.47    inference(resolution,[],[f94,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    l1_struct_0(sK0) | ~spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f92])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl3_9 | ~spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f90,f80,f92])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    l1_struct_0(sK0) | ~spl3_7),
% 0.21/0.47    inference(resolution,[],[f37,f82])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl3_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f85])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ((~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24,f23,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f10])).
% 0.21/0.47  fof(f10,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f80])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f75])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f70])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f65])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    v1_tops_1(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f60])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    v1_tops_1(sK2,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f34,f55])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    v3_pre_topc(sK2,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f35,f50])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (30813)------------------------------
% 0.21/0.48  % (30813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30813)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (30813)Memory used [KB]: 6396
% 0.21/0.48  % (30821)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (30813)Time elapsed: 0.062 s
% 0.21/0.48  % (30813)------------------------------
% 0.21/0.48  % (30813)------------------------------
% 0.21/0.48  % (30807)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (30806)Success in time 0.121 s
%------------------------------------------------------------------------------
