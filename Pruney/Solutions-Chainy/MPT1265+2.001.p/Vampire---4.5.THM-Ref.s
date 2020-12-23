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
% DateTime   : Thu Dec  3 13:12:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 265 expanded)
%              Number of leaves         :   30 ( 120 expanded)
%              Depth                    :    9
%              Number of atoms          :  405 (1133 expanded)
%              Number of equality atoms :   44 (  90 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f304,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f67,f72,f77,f82,f90,f98,f106,f111,f116,f139,f158,f187,f208,f260,f303])).

fof(f303,plain,
    ( ~ spl3_12
    | spl3_25 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | ~ spl3_12
    | spl3_25 ),
    inference(unit_resulting_resolution,[],[f149,f257])).

fof(f257,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl3_25
  <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f149,plain,
    ( ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_12 ),
    inference(superposition,[],[f140,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f140,plain,
    ( ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(X0,sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f117,f119])).

fof(f119,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f110,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f110,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f117,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(k2_struct_0(sK0),X0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f110,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f260,plain,
    ( ~ spl3_7
    | spl3_16
    | ~ spl3_25
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f259,f205,f94,f255,f155,f74])).

fof(f74,plain,
    ( spl3_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f155,plain,
    ( spl3_16
  <=> v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f94,plain,
    ( spl3_10
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f205,plain,
    ( spl3_21
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f259,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f252,f96])).

fof(f96,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f252,plain,
    ( v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_21 ),
    inference(trivial_inequality_removal,[],[f251])).

fof(f251,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_21 ),
    inference(superposition,[],[f36,f207])).

fof(f207,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f205])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f208,plain,
    ( spl3_21
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f203,f178,f137,f113,f108,f59,f49,f205])).

fof(f49,plain,
    ( spl3_2
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f59,plain,
    ( spl3_4
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f113,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f137,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
        | ~ v1_tops_1(X1,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f178,plain,
    ( spl3_18
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f203,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f202,f180])).

fof(f180,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f178])).

fof(f202,plain,
    ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f201,f38])).

fof(f201,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1)))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f191,f119])).

fof(f191,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f51,f61,f110,f115,f138])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ v1_tops_1(X1,sK0)
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f137])).

fof(f115,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f113])).

fof(f61,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f51,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f187,plain,
    ( spl3_18
    | ~ spl3_13
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f175,f94,f74,f54,f113,f178])).

fof(f54,plain,
    ( spl3_3
  <=> v1_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f175,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK2)
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(resolution,[],[f125,f56])).

fof(f56,plain,
    ( v1_tops_1(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f124,f96])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl3_7 ),
    inference(resolution,[],[f35,f76])).

fof(f76,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f158,plain,
    ( ~ spl3_16
    | spl3_11
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f151,f113,f103,f155])).

fof(f103,plain,
    ( spl3_11
  <=> v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f151,plain,
    ( ~ v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | spl3_11
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f105,f120])).

fof(f120,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f115,f42])).

fof(f105,plain,
    ( ~ v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f139,plain,
    ( ~ spl3_7
    | spl3_14
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f135,f94,f79,f137,f74])).

fof(f79,plain,
    ( spl3_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v1_tops_1(X1,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f134,f96])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v1_tops_1(X1,sK0)
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f133,f96])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v1_tops_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f132,f96])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl3_8 ),
    inference(resolution,[],[f37,f81])).

fof(f81,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f116,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f101,f94,f64,f113])).

fof(f64,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f101,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f66,f96])).

fof(f66,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f111,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f100,f94,f69,f108])).

fof(f69,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f100,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f71,f96])).

fof(f71,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f106,plain,
    ( ~ spl3_11
    | spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f99,f94,f44,f103])).

fof(f44,plain,
    ( spl3_1
  <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f99,plain,
    ( ~ v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f46,f96])).

fof(f46,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f98,plain,
    ( spl3_10
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f92,f86,f94])).

fof(f86,plain,
    ( spl3_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f92,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(resolution,[],[f88,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f88,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f90,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f84,f74,f86])).

fof(f84,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f34,f76])).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f82,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f25,f79])).

fof(f25,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v1_tops_1(sK2,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22,f21,f20])).

fof(f20,plain,
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

fof(f21,plain,
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

fof(f22,plain,
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f77,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f74])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f27,f69])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f30,f54])).

fof(f30,plain,(
    v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f31,f49])).

fof(f31,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f32,f44])).

fof(f32,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (9025)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (9018)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (9016)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (9014)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (9022)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (9013)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (9016)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f304,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f67,f72,f77,f82,f90,f98,f106,f111,f116,f139,f158,f187,f208,f260,f303])).
% 0.20/0.50  fof(f303,plain,(
% 0.20/0.50    ~spl3_12 | spl3_25),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f298])).
% 0.20/0.50  fof(f298,plain,(
% 0.20/0.50    $false | (~spl3_12 | spl3_25)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f149,f257])).
% 0.20/0.50  fof(f257,plain,(
% 0.20/0.50    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_25),
% 0.20/0.50    inference(avatar_component_clause,[],[f255])).
% 0.20/0.50  fof(f255,plain,(
% 0.20/0.50    spl3_25 <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_12),
% 0.20/0.50    inference(superposition,[],[f140,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(X0,sK1)),k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_12),
% 0.20/0.50    inference(backward_demodulation,[],[f117,f119])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))) ) | ~spl3_12),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f110,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f41,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f108])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    spl3_12 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k9_subset_1(k2_struct_0(sK0),X0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_12),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f110,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.20/0.50  fof(f260,plain,(
% 0.20/0.50    ~spl3_7 | spl3_16 | ~spl3_25 | ~spl3_10 | ~spl3_21),
% 0.20/0.50    inference(avatar_split_clause,[],[f259,f205,f94,f255,f155,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    spl3_7 <=> l1_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    spl3_16 <=> v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    spl3_10 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    spl3_21 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.50  fof(f259,plain,(
% 0.20/0.50    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | ~l1_pre_topc(sK0) | (~spl3_10 | ~spl3_21)),
% 0.20/0.50    inference(forward_demodulation,[],[f252,f96])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f94])).
% 0.20/0.50  fof(f252,plain,(
% 0.20/0.50    v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_21),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f251])).
% 0.20/0.50  fof(f251,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_21),
% 0.20/0.50    inference(superposition,[],[f36,f207])).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) | ~spl3_21),
% 0.20/0.50    inference(avatar_component_clause,[],[f205])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.20/0.50  fof(f208,plain,(
% 0.20/0.50    spl3_21 | ~spl3_2 | ~spl3_4 | ~spl3_12 | ~spl3_13 | ~spl3_14 | ~spl3_18),
% 0.20/0.50    inference(avatar_split_clause,[],[f203,f178,f137,f113,f108,f59,f49,f205])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    spl3_2 <=> v3_pre_topc(sK2,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    spl3_4 <=> v1_tops_1(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    spl3_14 <=> ! [X1,X0] : (k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~v1_tops_1(X1,sK0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    spl3_18 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) | (~spl3_2 | ~spl3_4 | ~spl3_12 | ~spl3_13 | ~spl3_14 | ~spl3_18)),
% 0.20/0.50    inference(forward_demodulation,[],[f202,f180])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    k2_struct_0(sK0) = k2_pre_topc(sK0,sK2) | ~spl3_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f178])).
% 0.20/0.50  fof(f202,plain,(
% 0.20/0.50    k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,sK2) | (~spl3_2 | ~spl3_4 | ~spl3_12 | ~spl3_13 | ~spl3_14)),
% 0.20/0.50    inference(forward_demodulation,[],[f201,f38])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1))) | (~spl3_2 | ~spl3_4 | ~spl3_12 | ~spl3_13 | ~spl3_14)),
% 0.20/0.50    inference(forward_demodulation,[],[f191,f119])).
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) | (~spl3_2 | ~spl3_4 | ~spl3_12 | ~spl3_13 | ~spl3_14)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f51,f61,f110,f115,f138])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~v1_tops_1(X1,sK0) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f137])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f113])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    v1_tops_1(sK1,sK0) | ~spl3_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f59])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    v3_pre_topc(sK2,sK0) | ~spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f49])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    spl3_18 | ~spl3_13 | ~spl3_3 | ~spl3_7 | ~spl3_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f175,f94,f74,f54,f113,f178])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    spl3_3 <=> v1_tops_1(sK2,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f175,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK2) | (~spl3_3 | ~spl3_7 | ~spl3_10)),
% 0.20/0.50    inference(resolution,[],[f125,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    v1_tops_1(sK2,sK0) | ~spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f54])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | (~spl3_7 | ~spl3_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f124,f96])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | ~spl3_7),
% 0.20/0.50    inference(resolution,[],[f35,f76])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    l1_pre_topc(sK0) | ~spl3_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f74])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f158,plain,(
% 0.20/0.50    ~spl3_16 | spl3_11 | ~spl3_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f151,f113,f103,f155])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    spl3_11 <=> v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    ~v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | (spl3_11 | ~spl3_13)),
% 0.20/0.50    inference(backward_demodulation,[],[f105,f120])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))) ) | ~spl3_13),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f115,f42])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ~v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0) | spl3_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f103])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    ~spl3_7 | spl3_14 | ~spl3_8 | ~spl3_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f135,f94,f79,f137,f74])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    spl3_8 <=> v2_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v1_tops_1(X1,sK0) | ~l1_pre_topc(sK0)) ) | (~spl3_8 | ~spl3_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f134,f96])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v1_tops_1(X1,sK0) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | (~spl3_8 | ~spl3_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f133,f96])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v1_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | (~spl3_8 | ~spl3_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f132,f96])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | ~spl3_8),
% 0.20/0.50    inference(resolution,[],[f37,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    v2_pre_topc(sK0) | ~spl3_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f79])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((! [X2] : ((k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    spl3_13 | ~spl3_5 | ~spl3_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f101,f94,f64,f113])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_5 | ~spl3_10)),
% 0.20/0.50    inference(backward_demodulation,[],[f66,f96])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f64])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    spl3_12 | ~spl3_6 | ~spl3_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f100,f94,f69,f108])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_6 | ~spl3_10)),
% 0.20/0.50    inference(backward_demodulation,[],[f71,f96])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f69])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    ~spl3_11 | spl3_1 | ~spl3_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f99,f94,f44,f103])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    spl3_1 <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ~v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0) | (spl3_1 | ~spl3_10)),
% 0.20/0.50    inference(backward_demodulation,[],[f46,f96])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f44])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    spl3_10 | ~spl3_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f92,f86,f94])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    spl3_9 <=> l1_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.20/0.50    inference(resolution,[],[f88,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    l1_struct_0(sK0) | ~spl3_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f86])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    spl3_9 | ~spl3_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f84,f74,f86])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    l1_struct_0(sK0) | ~spl3_7),
% 0.20/0.50    inference(resolution,[],[f34,f76])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    spl3_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f25,f79])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ((~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22,f21,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f9])).
% 0.20/0.50  fof(f9,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    spl3_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f26,f74])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    spl3_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f27,f69])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f28,f64])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    spl3_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f29,f59])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    v1_tops_1(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f30,f54])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    v1_tops_1(sK2,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f31,f49])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    v3_pre_topc(sK2,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ~spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f32,f44])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (9016)------------------------------
% 0.20/0.50  % (9016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (9016)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (9016)Memory used [KB]: 6396
% 0.20/0.50  % (9016)Time elapsed: 0.059 s
% 0.20/0.50  % (9016)------------------------------
% 0.20/0.50  % (9016)------------------------------
% 0.20/0.50  % (9009)Success in time 0.139 s
%------------------------------------------------------------------------------
