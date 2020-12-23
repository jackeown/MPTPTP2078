%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 232 expanded)
%              Number of leaves         :   30 ( 107 expanded)
%              Depth                    :    9
%              Number of atoms          :  362 ( 890 expanded)
%              Number of equality atoms :   63 ( 164 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f212,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f69,f74,f79,f86,f95,f103,f108,f113,f126,f138,f163,f175,f184,f193])).

fof(f193,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f192,f180,f172,f161,f110,f105,f51,f134])).

fof(f134,plain,
    ( spl3_15
  <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f51,plain,
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

fof(f161,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f172,plain,
    ( spl3_20
  <=> sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f180,plain,
    ( spl3_21
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f192,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f191,f130])).

fof(f130,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f112,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f112,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f191,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f190,f174])).

fof(f174,plain,
    ( sK2 = k3_xboole_0(sK2,k2_struct_0(sK0))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f172])).

fof(f190,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f189,f128])).

fof(f128,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(unit_resulting_resolution,[],[f80,f35])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f43,f41])).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f189,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f187,f182])).

fof(f182,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f180])).

fof(f187,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1)))
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f53,f107,f112,f162])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f107,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f53,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f184,plain,
    ( spl3_21
    | ~ spl3_12
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f178,f91,f71,f61,f110,f180])).

fof(f61,plain,
    ( spl3_4
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f71,plain,
    ( spl3_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f91,plain,
    ( spl3_9
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f178,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(resolution,[],[f147,f63])).

fof(f63,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f146,f93])).

fof(f93,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl3_6 ),
    inference(resolution,[],[f38,f73])).

fof(f73,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f175,plain,
    ( spl3_20
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f170,f123,f172])).

fof(f123,plain,
    ( spl3_14
  <=> r1_tarski(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f170,plain,
    ( sK2 = k3_xboole_0(sK2,k2_struct_0(sK0))
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f125,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f125,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f123])).

fof(f163,plain,
    ( ~ spl3_6
    | spl3_18
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f159,f91,f76,f161,f71])).

fof(f76,plain,
    ( spl3_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f158,f93])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f157,f93])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f156,f93])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl3_7 ),
    inference(resolution,[],[f37,f78])).

fof(f78,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

fof(f138,plain,
    ( ~ spl3_12
    | ~ spl3_15
    | spl3_10 ),
    inference(avatar_split_clause,[],[f131,f100,f134,f110])).

fof(f100,plain,
    ( spl3_10
  <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f131,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_10 ),
    inference(superposition,[],[f102,f35])).

fof(f102,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f126,plain,
    ( spl3_14
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f115,f105,f123])).

fof(f115,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0))
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f107,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f113,plain,
    ( spl3_12
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f98,f91,f66,f110])).

fof(f66,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f68,f93])).

fof(f68,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f108,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f97,f91,f56,f105])).

fof(f56,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f97,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f58,f93])).

fof(f58,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f103,plain,
    ( ~ spl3_10
    | spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f96,f91,f46,f100])).

fof(f46,plain,
    ( spl3_1
  <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f96,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))
    | spl3_1
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f48,f93])).

fof(f48,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

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
    inference(resolution,[],[f40,f85])).

fof(f85,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f86,plain,
    ( spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f81,f71,f83])).

fof(f81,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f73,f44])).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f79,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f28,f76])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    & v3_pre_topc(sK2,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25,f24,f23])).

fof(f23,plain,
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

fof(f24,plain,
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

fof(f25,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

fof(f74,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f30,f66])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f32,f56])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f33,f51])).

fof(f33,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f34,f46])).

fof(f34,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:28:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (16936)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.48  % (16936)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (16944)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f69,f74,f79,f86,f95,f103,f108,f113,f126,f138,f163,f175,f184,f193])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    spl3_15 | ~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_18 | ~spl3_20 | ~spl3_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f192,f180,f172,f161,f110,f105,f51,f134])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl3_15 <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl3_2 <=> v3_pre_topc(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl3_11 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl3_12 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    spl3_18 <=> ! [X1,X0] : (k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    spl3_20 <=> sK2 = k3_xboole_0(sK2,k2_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    spl3_21 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) | (~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_18 | ~spl3_20 | ~spl3_21)),
% 0.21/0.49    inference(forward_demodulation,[],[f191,f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)) ) | ~spl3_12),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f112,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f110])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) | (~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_18 | ~spl3_20 | ~spl3_21)),
% 0.21/0.49    inference(forward_demodulation,[],[f190,f174])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)) | ~spl3_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f172])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k3_xboole_0(sK2,k2_struct_0(sK0))) | (~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_18 | ~spl3_21)),
% 0.21/0.49    inference(forward_demodulation,[],[f189,f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f80,f35])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f43,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))) | (~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_18 | ~spl3_21)),
% 0.21/0.49    inference(forward_demodulation,[],[f187,f182])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~spl3_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f180])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1))) | (~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_18)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f53,f107,f112,f162])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f161])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f105])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    v3_pre_topc(sK2,sK0) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f51])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    spl3_21 | ~spl3_12 | ~spl3_4 | ~spl3_6 | ~spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f178,f91,f71,f61,f110,f180])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl3_4 <=> v1_tops_1(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl3_6 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl3_9 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl3_4 | ~spl3_6 | ~spl3_9)),
% 0.21/0.49    inference(resolution,[],[f147,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    v1_tops_1(sK1,sK0) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f61])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | (~spl3_6 | ~spl3_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f146,f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f91])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | ~spl3_6),
% 0.21/0.49    inference(resolution,[],[f38,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    spl3_20 | ~spl3_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f170,f123,f172])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl3_14 <=> r1_tarski(sK2,k2_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)) | ~spl3_14),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f125,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    r1_tarski(sK2,k2_struct_0(sK0)) | ~spl3_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f123])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ~spl3_6 | spl3_18 | ~spl3_7 | ~spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f159,f91,f76,f161,f71])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl3_7 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | (~spl3_7 | ~spl3_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f158,f93])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | (~spl3_7 | ~spl3_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f157,f93])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | (~spl3_7 | ~spl3_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f156,f93])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | ~spl3_7),
% 0.21/0.49    inference(resolution,[],[f37,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    v2_pre_topc(sK0) | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f76])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ~spl3_12 | ~spl3_15 | spl3_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f131,f100,f134,f110])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl3_10 <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl3_10),
% 0.21/0.49    inference(superposition,[],[f102,f35])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) | spl3_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f100])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl3_14 | ~spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f115,f105,f123])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    r1_tarski(sK2,k2_struct_0(sK0)) | ~spl3_11),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f107,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.49    inference(unused_predicate_definition_removal,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    spl3_12 | ~spl3_5 | ~spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f98,f91,f66,f110])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_5 | ~spl3_9)),
% 0.21/0.49    inference(backward_demodulation,[],[f68,f93])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl3_11 | ~spl3_3 | ~spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f97,f91,f56,f105])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_3 | ~spl3_9)),
% 0.21/0.49    inference(backward_demodulation,[],[f58,f93])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f56])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ~spl3_10 | spl3_1 | ~spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f96,f91,f46,f100])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    spl3_1 <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) | (spl3_1 | ~spl3_9)),
% 0.21/0.49    inference(backward_demodulation,[],[f48,f93])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f46])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl3_9 | ~spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f89,f83,f91])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl3_8 <=> l1_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_8),
% 0.21/0.49    inference(resolution,[],[f40,f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    l1_struct_0(sK0) | ~spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f83])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl3_8 | ~spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f81,f71,f83])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    l1_struct_0(sK0) | ~spl3_6),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f73,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl3_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f76])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ((k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) & v3_pre_topc(sK2,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25,f24,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) & v3_pre_topc(sK2,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((? [X2] : ((k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f71])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f66])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f61])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    v1_tops_1(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f56])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f51])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    v3_pre_topc(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ~spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f46])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (16936)------------------------------
% 0.21/0.49  % (16936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (16936)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (16936)Memory used [KB]: 10746
% 0.21/0.49  % (16936)Time elapsed: 0.068 s
% 0.21/0.49  % (16936)------------------------------
% 0.21/0.49  % (16936)------------------------------
% 0.21/0.49  % (16927)Success in time 0.133 s
%------------------------------------------------------------------------------
