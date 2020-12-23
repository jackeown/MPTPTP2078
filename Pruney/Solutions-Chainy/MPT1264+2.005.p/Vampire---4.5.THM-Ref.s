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
% DateTime   : Thu Dec  3 13:12:17 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 238 expanded)
%              Number of leaves         :   31 ( 110 expanded)
%              Depth                    :   12
%              Number of atoms          :  367 ( 901 expanded)
%              Number of equality atoms :   69 ( 172 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f70,f75,f80,f86,f95,f103,f108,f113,f125,f138,f162,f170,f174,f194,f204])).

fof(f204,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f203,f190,f168,f158,f110,f105,f52,f133])).

fof(f133,plain,
    ( spl3_15
  <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f52,plain,
    ( spl3_2
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f105,plain,
    ( spl3_11
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f110,plain,
    ( spl3_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f158,plain,
    ( spl3_17
  <=> sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f168,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,X0))
        | ~ v3_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f190,plain,
    ( spl3_20
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f203,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f202,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f202,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f201,f128])).

fof(f128,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f112,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f112,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f201,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f200,f160])).

fof(f160,plain,
    ( sK2 = k3_xboole_0(sK2,k2_struct_0(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f158])).

fof(f200,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f199,f192])).

fof(f192,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f190])).

fof(f199,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k3_xboole_0(sK2,k2_pre_topc(sK0,sK1)))
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f198,f39])).

fof(f198,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k3_xboole_0(k2_pre_topc(sK0,sK1),sK2))
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f196,f152])).

fof(f152,plain,
    ( ! [X0] : k3_xboole_0(X0,sK2) = k9_subset_1(k2_struct_0(sK0),sK2,X0)
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f147,f127])).

fof(f127,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f107,f37])).

fof(f107,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f147,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK2) = k9_subset_1(k2_struct_0(sK0),sK2,X0)
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f107,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f196,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1)))
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f54,f112,f107,f169])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f168])).

fof(f54,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f194,plain,
    ( ~ spl3_12
    | spl3_20
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f188,f172,f62,f190,f110])).

fof(f62,plain,
    ( spl3_4
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f172,plain,
    ( spl3_19
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X2) = k2_struct_0(sK0)
        | ~ v1_tops_1(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f188,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(resolution,[],[f173,f64])).

fof(f64,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f173,plain,
    ( ! [X2] :
        ( ~ v1_tops_1(X2,sK0)
        | k2_pre_topc(sK0,X2) = k2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f172])).

fof(f174,plain,
    ( ~ spl3_6
    | spl3_19
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f166,f91,f172,f72])).

fof(f72,plain,
    ( spl3_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f91,plain,
    ( spl3_9
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f166,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v1_tops_1(X2,sK0)
        | k2_pre_topc(sK0,X2) = k2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_9 ),
    inference(superposition,[],[f41,f93])).

fof(f93,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f170,plain,
    ( ~ spl3_7
    | ~ spl3_6
    | spl3_18
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f165,f91,f168,f72,f77])).

fof(f77,plain,
    ( spl3_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X1,sK0)
        | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl3_9 ),
    inference(superposition,[],[f40,f93])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
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
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).

fof(f162,plain,
    ( spl3_17
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f156,f122,f158])).

fof(f122,plain,
    ( spl3_14
  <=> r1_tarski(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f156,plain,
    ( sK2 = k3_xboole_0(sK2,k2_struct_0(sK0))
    | ~ spl3_14 ),
    inference(resolution,[],[f124,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f124,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f138,plain,
    ( ~ spl3_12
    | ~ spl3_15
    | spl3_10 ),
    inference(avatar_split_clause,[],[f137,f100,f133,f110])).

fof(f100,plain,
    ( spl3_10
  <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f137,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_10 ),
    inference(forward_demodulation,[],[f129,f39])).

fof(f129,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_10 ),
    inference(superposition,[],[f102,f37])).

fof(f102,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f125,plain,
    ( spl3_14
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f114,f105,f122])).

% (12450)Refutation not found, incomplete strategy% (12450)------------------------------
% (12450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f114,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0))
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f107,f44])).

% (12450)Termination reason: Refutation not found, incomplete strategy

% (12450)Memory used [KB]: 10618
fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

% (12450)Time elapsed: 0.147 s
% (12450)------------------------------
% (12450)------------------------------
fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f113,plain,
    ( spl3_12
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f98,f91,f67,f110])).

fof(f67,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f69,f93])).

fof(f69,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f108,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f97,f91,f57,f105])).

fof(f57,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f97,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f59,f93])).

fof(f59,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f103,plain,
    ( ~ spl3_10
    | spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f96,f91,f47,f100])).

fof(f47,plain,
    ( spl3_1
  <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f96,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))
    | spl3_1
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f49,f93])).

fof(f49,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f95,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f89,f83,f91])).

fof(f83,plain,
    ( spl3_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f89,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f43,f85])).

fof(f85,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f86,plain,
    ( spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f81,f72,f83])).

fof(f81,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f74,f45])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f74,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f80,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f29,f77])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    & v3_pre_topc(sK2,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
                & v3_pre_topc(X2,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1))
              & v3_pre_topc(X2,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & v1_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1))
            & v3_pre_topc(X2,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & v1_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1))
          & v3_pre_topc(X2,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1))
        & v3_pre_topc(X2,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
      & v3_pre_topc(sK2,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
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
           => ( v1_tops_1(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( v3_pre_topc(X2,X0)
                   => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

fof(f75,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f30,f72])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f31,f67])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f32,f62])).

fof(f32,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f33,f57])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f34,f52])).

fof(f34,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f35,f47])).

fof(f35,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:47:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.23/0.55  % (12441)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.23/0.56  % (12445)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.23/0.56  % (12446)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.59/0.56  % (12463)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.59/0.57  % (12446)Refutation found. Thanks to Tanya!
% 1.59/0.57  % SZS status Theorem for theBenchmark
% 1.59/0.57  % (12443)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.59/0.57  % (12444)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.59/0.57  % (12440)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.59/0.57  % (12455)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.59/0.57  % (12443)Refutation not found, incomplete strategy% (12443)------------------------------
% 1.59/0.57  % (12443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (12443)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (12443)Memory used [KB]: 10618
% 1.59/0.57  % (12443)Time elapsed: 0.126 s
% 1.59/0.57  % (12443)------------------------------
% 1.59/0.57  % (12443)------------------------------
% 1.59/0.57  % (12463)Refutation not found, incomplete strategy% (12463)------------------------------
% 1.59/0.57  % (12463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (12463)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (12463)Memory used [KB]: 10618
% 1.59/0.57  % (12463)Time elapsed: 0.078 s
% 1.59/0.57  % (12463)------------------------------
% 1.59/0.57  % (12463)------------------------------
% 1.59/0.57  % (12454)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.59/0.57  % (12457)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.59/0.57  % (12451)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.59/0.57  % (12447)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.59/0.58  % (12456)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.59/0.58  % (12442)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.59/0.58  % (12449)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.59/0.58  % (12453)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.59/0.58  % (12450)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.59/0.58  % (12462)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.59/0.58  % SZS output start Proof for theBenchmark
% 1.59/0.58  fof(f220,plain,(
% 1.59/0.58    $false),
% 1.59/0.58    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f70,f75,f80,f86,f95,f103,f108,f113,f125,f138,f162,f170,f174,f194,f204])).
% 1.59/0.58  fof(f204,plain,(
% 1.59/0.58    spl3_15 | ~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_17 | ~spl3_18 | ~spl3_20),
% 1.59/0.58    inference(avatar_split_clause,[],[f203,f190,f168,f158,f110,f105,f52,f133])).
% 1.59/0.58  fof(f133,plain,(
% 1.59/0.58    spl3_15 <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.59/0.58  fof(f52,plain,(
% 1.59/0.58    spl3_2 <=> v3_pre_topc(sK2,sK0)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.59/0.58  fof(f105,plain,(
% 1.59/0.58    spl3_11 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.59/0.58  fof(f110,plain,(
% 1.59/0.58    spl3_12 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.59/0.58  fof(f158,plain,(
% 1.59/0.58    spl3_17 <=> sK2 = k3_xboole_0(sK2,k2_struct_0(sK0))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.59/0.58  fof(f168,plain,(
% 1.59/0.58    spl3_18 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,X0)) | ~v3_pre_topc(X1,sK0))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.59/0.58  fof(f190,plain,(
% 1.59/0.58    spl3_20 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.59/0.58  fof(f203,plain,(
% 1.59/0.58    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_17 | ~spl3_18 | ~spl3_20)),
% 1.59/0.58    inference(forward_demodulation,[],[f202,f39])).
% 1.59/0.58  fof(f39,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f1])).
% 1.59/0.58  fof(f1,axiom,(
% 1.59/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.59/0.58  fof(f202,plain,(
% 1.59/0.58    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) | (~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_17 | ~spl3_18 | ~spl3_20)),
% 1.59/0.58    inference(forward_demodulation,[],[f201,f128])).
% 1.59/0.58  fof(f128,plain,(
% 1.59/0.58    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)) ) | ~spl3_12),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f112,f37])).
% 1.59/0.58  fof(f37,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f16])).
% 1.59/0.58  fof(f16,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f4])).
% 1.59/0.58  fof(f4,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.59/0.58  fof(f112,plain,(
% 1.59/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_12),
% 1.59/0.58    inference(avatar_component_clause,[],[f110])).
% 1.59/0.58  fof(f201,plain,(
% 1.59/0.58    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) | (~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_17 | ~spl3_18 | ~spl3_20)),
% 1.59/0.58    inference(forward_demodulation,[],[f200,f160])).
% 1.59/0.58  fof(f160,plain,(
% 1.59/0.58    sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)) | ~spl3_17),
% 1.59/0.58    inference(avatar_component_clause,[],[f158])).
% 1.59/0.58  fof(f200,plain,(
% 1.59/0.58    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0))) | (~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_18 | ~spl3_20)),
% 1.59/0.58    inference(forward_demodulation,[],[f199,f192])).
% 1.59/0.58  fof(f192,plain,(
% 1.59/0.58    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~spl3_20),
% 1.59/0.58    inference(avatar_component_clause,[],[f190])).
% 1.59/0.58  fof(f199,plain,(
% 1.59/0.58    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k3_xboole_0(sK2,k2_pre_topc(sK0,sK1))) | (~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_18)),
% 1.59/0.58    inference(forward_demodulation,[],[f198,f39])).
% 1.59/0.58  fof(f198,plain,(
% 1.59/0.58    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k3_xboole_0(k2_pre_topc(sK0,sK1),sK2)) | (~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_18)),
% 1.59/0.58    inference(forward_demodulation,[],[f196,f152])).
% 1.59/0.58  fof(f152,plain,(
% 1.59/0.58    ( ! [X0] : (k3_xboole_0(X0,sK2) = k9_subset_1(k2_struct_0(sK0),sK2,X0)) ) | ~spl3_11),
% 1.59/0.58    inference(forward_demodulation,[],[f147,f127])).
% 1.59/0.58  fof(f127,plain,(
% 1.59/0.58    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2)) ) | ~spl3_11),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f107,f37])).
% 1.59/0.58  fof(f107,plain,(
% 1.59/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_11),
% 1.59/0.58    inference(avatar_component_clause,[],[f105])).
% 1.59/0.58  fof(f147,plain,(
% 1.59/0.58    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK2) = k9_subset_1(k2_struct_0(sK0),sK2,X0)) ) | ~spl3_11),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f107,f36])).
% 1.59/0.58  fof(f36,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f15])).
% 1.59/0.58  fof(f15,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f3])).
% 1.59/0.58  fof(f3,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 1.59/0.58  fof(f196,plain,(
% 1.59/0.58    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1))) | (~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_18)),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f54,f112,f107,f169])).
% 1.59/0.58  fof(f169,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_18),
% 1.59/0.58    inference(avatar_component_clause,[],[f168])).
% 1.59/0.58  fof(f54,plain,(
% 1.59/0.58    v3_pre_topc(sK2,sK0) | ~spl3_2),
% 1.59/0.58    inference(avatar_component_clause,[],[f52])).
% 1.59/0.58  fof(f194,plain,(
% 1.59/0.58    ~spl3_12 | spl3_20 | ~spl3_4 | ~spl3_19),
% 1.59/0.58    inference(avatar_split_clause,[],[f188,f172,f62,f190,f110])).
% 1.59/0.58  fof(f62,plain,(
% 1.59/0.58    spl3_4 <=> v1_tops_1(sK1,sK0)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.59/0.58  fof(f172,plain,(
% 1.59/0.58    spl3_19 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X2) = k2_struct_0(sK0) | ~v1_tops_1(X2,sK0))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.59/0.58  fof(f188,plain,(
% 1.59/0.58    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_4 | ~spl3_19)),
% 1.59/0.58    inference(resolution,[],[f173,f64])).
% 1.59/0.58  fof(f64,plain,(
% 1.59/0.58    v1_tops_1(sK1,sK0) | ~spl3_4),
% 1.59/0.58    inference(avatar_component_clause,[],[f62])).
% 1.59/0.58  fof(f173,plain,(
% 1.59/0.58    ( ! [X2] : (~v1_tops_1(X2,sK0) | k2_pre_topc(sK0,X2) = k2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_19),
% 1.59/0.58    inference(avatar_component_clause,[],[f172])).
% 1.59/0.58  fof(f174,plain,(
% 1.59/0.58    ~spl3_6 | spl3_19 | ~spl3_9),
% 1.59/0.58    inference(avatar_split_clause,[],[f166,f91,f172,f72])).
% 1.59/0.58  fof(f72,plain,(
% 1.59/0.58    spl3_6 <=> l1_pre_topc(sK0)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.59/0.58  fof(f91,plain,(
% 1.59/0.58    spl3_9 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.59/0.58  fof(f166,plain,(
% 1.59/0.58    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X2,sK0) | k2_pre_topc(sK0,X2) = k2_struct_0(sK0) | ~l1_pre_topc(sK0)) ) | ~spl3_9),
% 1.59/0.58    inference(superposition,[],[f41,f93])).
% 1.59/0.58  fof(f93,plain,(
% 1.59/0.58    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 1.59/0.58    inference(avatar_component_clause,[],[f91])).
% 1.59/0.58  fof(f41,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f28])).
% 1.59/0.58  fof(f28,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.59/0.58    inference(nnf_transformation,[],[f20])).
% 1.59/0.58  fof(f20,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.59/0.58    inference(ennf_transformation,[],[f8])).
% 1.59/0.58  fof(f8,axiom,(
% 1.59/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 1.59/0.58  fof(f170,plain,(
% 1.59/0.58    ~spl3_7 | ~spl3_6 | spl3_18 | ~spl3_9),
% 1.59/0.58    inference(avatar_split_clause,[],[f165,f91,f168,f72,f77])).
% 1.59/0.58  fof(f77,plain,(
% 1.59/0.58    spl3_7 <=> v2_pre_topc(sK0)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.59/0.58  fof(f165,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl3_9),
% 1.59/0.58    inference(superposition,[],[f40,f93])).
% 1.59/0.58  fof(f40,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f19])).
% 1.59/0.58  fof(f19,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.59/0.58    inference(flattening,[],[f18])).
% 1.59/0.58  fof(f18,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f9])).
% 1.59/0.58  fof(f9,axiom,(
% 1.59/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))))))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).
% 1.59/0.58  fof(f162,plain,(
% 1.59/0.58    spl3_17 | ~spl3_14),
% 1.59/0.58    inference(avatar_split_clause,[],[f156,f122,f158])).
% 1.59/0.58  fof(f122,plain,(
% 1.59/0.58    spl3_14 <=> r1_tarski(sK2,k2_struct_0(sK0))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.59/0.58  fof(f156,plain,(
% 1.59/0.58    sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)) | ~spl3_14),
% 1.59/0.58    inference(resolution,[],[f124,f38])).
% 1.59/0.58  fof(f38,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.59/0.58    inference(cnf_transformation,[],[f17])).
% 1.59/0.58  fof(f17,plain,(
% 1.59/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.59/0.58    inference(ennf_transformation,[],[f2])).
% 1.59/0.58  fof(f2,axiom,(
% 1.59/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.59/0.58  fof(f124,plain,(
% 1.59/0.58    r1_tarski(sK2,k2_struct_0(sK0)) | ~spl3_14),
% 1.59/0.58    inference(avatar_component_clause,[],[f122])).
% 1.59/0.58  fof(f138,plain,(
% 1.59/0.58    ~spl3_12 | ~spl3_15 | spl3_10),
% 1.59/0.58    inference(avatar_split_clause,[],[f137,f100,f133,f110])).
% 1.59/0.58  fof(f100,plain,(
% 1.59/0.58    spl3_10 <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.59/0.58  fof(f137,plain,(
% 1.59/0.58    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl3_10),
% 1.59/0.58    inference(forward_demodulation,[],[f129,f39])).
% 1.59/0.58  fof(f129,plain,(
% 1.59/0.58    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl3_10),
% 1.59/0.58    inference(superposition,[],[f102,f37])).
% 1.59/0.58  fof(f102,plain,(
% 1.59/0.58    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) | spl3_10),
% 1.59/0.58    inference(avatar_component_clause,[],[f100])).
% 1.59/0.58  fof(f125,plain,(
% 1.59/0.58    spl3_14 | ~spl3_11),
% 1.59/0.58    inference(avatar_split_clause,[],[f114,f105,f122])).
% 1.59/0.58  % (12450)Refutation not found, incomplete strategy% (12450)------------------------------
% 1.59/0.58  % (12450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  fof(f114,plain,(
% 1.59/0.58    r1_tarski(sK2,k2_struct_0(sK0)) | ~spl3_11),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f107,f44])).
% 1.59/0.58  % (12450)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (12450)Memory used [KB]: 10618
% 1.59/0.58  fof(f44,plain,(
% 1.59/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f22])).
% 1.59/0.58  % (12450)Time elapsed: 0.147 s
% 1.59/0.58  % (12450)------------------------------
% 1.59/0.58  % (12450)------------------------------
% 1.59/0.58  fof(f22,plain,(
% 1.59/0.58    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.59/0.58    inference(ennf_transformation,[],[f12])).
% 1.59/0.58  fof(f12,plain,(
% 1.59/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 1.59/0.58    inference(unused_predicate_definition_removal,[],[f5])).
% 1.59/0.58  fof(f5,axiom,(
% 1.59/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.59/0.58  fof(f113,plain,(
% 1.59/0.58    spl3_12 | ~spl3_5 | ~spl3_9),
% 1.59/0.58    inference(avatar_split_clause,[],[f98,f91,f67,f110])).
% 1.59/0.58  fof(f67,plain,(
% 1.59/0.58    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.59/0.58  fof(f98,plain,(
% 1.59/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_5 | ~spl3_9)),
% 1.59/0.58    inference(backward_demodulation,[],[f69,f93])).
% 1.59/0.58  fof(f69,plain,(
% 1.59/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 1.59/0.58    inference(avatar_component_clause,[],[f67])).
% 1.59/0.58  fof(f108,plain,(
% 1.59/0.58    spl3_11 | ~spl3_3 | ~spl3_9),
% 1.59/0.58    inference(avatar_split_clause,[],[f97,f91,f57,f105])).
% 1.59/0.58  fof(f57,plain,(
% 1.59/0.58    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.59/0.58  fof(f97,plain,(
% 1.59/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_3 | ~spl3_9)),
% 1.59/0.58    inference(backward_demodulation,[],[f59,f93])).
% 1.59/0.58  fof(f59,plain,(
% 1.59/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 1.59/0.58    inference(avatar_component_clause,[],[f57])).
% 1.59/0.58  fof(f103,plain,(
% 1.59/0.58    ~spl3_10 | spl3_1 | ~spl3_9),
% 1.59/0.58    inference(avatar_split_clause,[],[f96,f91,f47,f100])).
% 1.59/0.58  fof(f47,plain,(
% 1.59/0.58    spl3_1 <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.59/0.58  fof(f96,plain,(
% 1.59/0.58    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) | (spl3_1 | ~spl3_9)),
% 1.59/0.58    inference(backward_demodulation,[],[f49,f93])).
% 1.59/0.58  fof(f49,plain,(
% 1.59/0.58    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) | spl3_1),
% 1.59/0.58    inference(avatar_component_clause,[],[f47])).
% 1.59/0.58  fof(f95,plain,(
% 1.59/0.58    spl3_9 | ~spl3_8),
% 1.59/0.58    inference(avatar_split_clause,[],[f89,f83,f91])).
% 1.59/0.58  fof(f83,plain,(
% 1.59/0.58    spl3_8 <=> l1_struct_0(sK0)),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.59/0.58  fof(f89,plain,(
% 1.59/0.58    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_8),
% 1.59/0.58    inference(resolution,[],[f43,f85])).
% 1.59/0.58  fof(f85,plain,(
% 1.59/0.58    l1_struct_0(sK0) | ~spl3_8),
% 1.59/0.58    inference(avatar_component_clause,[],[f83])).
% 1.59/0.58  fof(f43,plain,(
% 1.59/0.58    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f21])).
% 1.59/0.58  fof(f21,plain,(
% 1.59/0.58    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.59/0.58    inference(ennf_transformation,[],[f6])).
% 1.59/0.58  fof(f6,axiom,(
% 1.59/0.58    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.59/0.58  fof(f86,plain,(
% 1.59/0.58    spl3_8 | ~spl3_6),
% 1.59/0.58    inference(avatar_split_clause,[],[f81,f72,f83])).
% 1.59/0.58  fof(f81,plain,(
% 1.59/0.58    l1_struct_0(sK0) | ~spl3_6),
% 1.59/0.58    inference(unit_resulting_resolution,[],[f74,f45])).
% 1.59/0.58  fof(f45,plain,(
% 1.59/0.58    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f23])).
% 1.59/0.58  fof(f23,plain,(
% 1.59/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.59/0.58    inference(ennf_transformation,[],[f7])).
% 1.59/0.58  fof(f7,axiom,(
% 1.59/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.59/0.58  fof(f74,plain,(
% 1.59/0.58    l1_pre_topc(sK0) | ~spl3_6),
% 1.59/0.58    inference(avatar_component_clause,[],[f72])).
% 1.59/0.58  fof(f80,plain,(
% 1.59/0.58    spl3_7),
% 1.59/0.58    inference(avatar_split_clause,[],[f29,f77])).
% 1.59/0.58  fof(f29,plain,(
% 1.59/0.58    v2_pre_topc(sK0)),
% 1.59/0.58    inference(cnf_transformation,[],[f27])).
% 1.59/0.58  fof(f27,plain,(
% 1.59/0.58    ((k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) & v3_pre_topc(sK2,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.59/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26,f25,f24])).
% 1.59/0.58  fof(f24,plain,(
% 1.59/0.58    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f25,plain,(
% 1.59/0.58    ? [X1] : (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f26,plain,(
% 1.59/0.58    ? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) & v3_pre_topc(sK2,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f14,plain,(
% 1.59/0.58    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.59/0.58    inference(flattening,[],[f13])).
% 1.59/0.58  fof(f13,plain,(
% 1.59/0.58    ? [X0] : (? [X1] : ((? [X2] : ((k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f11])).
% 1.59/0.58  fof(f11,negated_conjecture,(
% 1.59/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 1.59/0.58    inference(negated_conjecture,[],[f10])).
% 1.59/0.58  fof(f10,conjecture,(
% 1.59/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).
% 1.59/0.58  fof(f75,plain,(
% 1.59/0.58    spl3_6),
% 1.59/0.58    inference(avatar_split_clause,[],[f30,f72])).
% 1.59/0.58  fof(f30,plain,(
% 1.59/0.58    l1_pre_topc(sK0)),
% 1.59/0.58    inference(cnf_transformation,[],[f27])).
% 1.59/0.58  fof(f70,plain,(
% 1.59/0.58    spl3_5),
% 1.59/0.58    inference(avatar_split_clause,[],[f31,f67])).
% 1.59/0.58  fof(f31,plain,(
% 1.59/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.59/0.58    inference(cnf_transformation,[],[f27])).
% 1.59/0.58  fof(f65,plain,(
% 1.59/0.58    spl3_4),
% 1.59/0.58    inference(avatar_split_clause,[],[f32,f62])).
% 1.59/0.58  fof(f32,plain,(
% 1.59/0.58    v1_tops_1(sK1,sK0)),
% 1.59/0.58    inference(cnf_transformation,[],[f27])).
% 1.59/0.58  fof(f60,plain,(
% 1.59/0.58    spl3_3),
% 1.59/0.58    inference(avatar_split_clause,[],[f33,f57])).
% 1.59/0.58  fof(f33,plain,(
% 1.59/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.59/0.58    inference(cnf_transformation,[],[f27])).
% 1.59/0.58  fof(f55,plain,(
% 1.59/0.58    spl3_2),
% 1.59/0.58    inference(avatar_split_clause,[],[f34,f52])).
% 1.59/0.58  fof(f34,plain,(
% 1.59/0.58    v3_pre_topc(sK2,sK0)),
% 1.59/0.58    inference(cnf_transformation,[],[f27])).
% 1.59/0.58  fof(f50,plain,(
% 1.59/0.58    ~spl3_1),
% 1.59/0.58    inference(avatar_split_clause,[],[f35,f47])).
% 1.59/0.58  fof(f35,plain,(
% 1.59/0.58    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))),
% 1.59/0.58    inference(cnf_transformation,[],[f27])).
% 1.59/0.58  % SZS output end Proof for theBenchmark
% 1.59/0.58  % (12446)------------------------------
% 1.59/0.58  % (12446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (12446)Termination reason: Refutation
% 1.59/0.58  
% 1.59/0.58  % (12446)Memory used [KB]: 10746
% 1.59/0.58  % (12446)Time elapsed: 0.129 s
% 1.59/0.58  % (12446)------------------------------
% 1.59/0.58  % (12446)------------------------------
% 1.59/0.58  % (12461)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.59/0.58  % (12448)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.59/0.59  % (12439)Success in time 0.218 s
%------------------------------------------------------------------------------
