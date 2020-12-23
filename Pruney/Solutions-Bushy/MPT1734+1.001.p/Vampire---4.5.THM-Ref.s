%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1734+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:27 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 361 expanded)
%              Number of leaves         :   48 ( 165 expanded)
%              Depth                    :   12
%              Number of atoms          :  833 (2073 expanded)
%              Number of equality atoms :   55 (  71 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f717,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f169,f174,f239,f269,f314,f319,f332,f347,f437,f471,f613,f646,f653,f657,f679,f691,f697,f716])).

fof(f716,plain,
    ( ~ spl4_10
    | ~ spl4_9
    | ~ spl4_7
    | spl4_101 ),
    inference(avatar_split_clause,[],[f715,f688,f117,f125,f129])).

fof(f129,plain,
    ( spl4_10
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f125,plain,
    ( spl4_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f117,plain,
    ( spl4_7
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f688,plain,
    ( spl4_101
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_101])])).

fof(f715,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_7
    | spl4_101 ),
    inference(resolution,[],[f698,f118])).

fof(f118,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f698,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl4_101 ),
    inference(resolution,[],[f689,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f689,plain,
    ( ~ v2_pre_topc(sK1)
    | spl4_101 ),
    inference(avatar_component_clause,[],[f688])).

fof(f697,plain,
    ( ~ spl4_7
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_10
    | spl4_11
    | spl4_2
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f696,f267,f97,f133,f129,f125,f105,f117])).

fof(f105,plain,
    ( spl4_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f133,plain,
    ( spl4_11
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f97,plain,
    ( spl4_2
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f267,plain,
    ( spl4_30
  <=> ! [X0] :
        ( m1_pre_topc(k2_tsep_1(X0,sK2,sK1),sK1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f696,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | spl4_2
    | ~ spl4_30 ),
    inference(resolution,[],[f98,f268])).

fof(f268,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(X0,sK2,sK1),sK1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f267])).

fof(f98,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f691,plain,
    ( ~ spl4_101
    | ~ spl4_24
    | ~ spl4_2
    | spl4_1
    | ~ spl4_99 ),
    inference(avatar_split_clause,[],[f681,f677,f94,f97,f231,f688])).

fof(f231,plain,
    ( spl4_24
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f94,plain,
    ( spl4_1
  <=> v1_borsuk_1(k2_tsep_1(sK0,sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f677,plain,
    ( spl4_99
  <=> v4_pre_topc(u1_struct_0(k2_tsep_1(sK0,sK2,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).

fof(f681,plain,
    ( v1_borsuk_1(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_99 ),
    inference(resolution,[],[f678,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(u1_struct_0(X1),X0)
      | v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f65,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f678,plain,
    ( v4_pre_topc(u1_struct_0(k2_tsep_1(sK0,sK2,sK1)),sK1)
    | ~ spl4_99 ),
    inference(avatar_component_clause,[],[f677])).

fof(f679,plain,
    ( ~ spl4_87
    | spl4_99
    | ~ spl4_41
    | ~ spl4_65 ),
    inference(avatar_split_clause,[],[f675,f469,f330,f677,f611])).

fof(f611,plain,
    ( spl4_87
  <=> m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f330,plain,
    ( spl4_41
  <=> u1_struct_0(k2_tsep_1(sK0,sK2,sK1)) = k3_xboole_0(k2_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f469,plain,
    ( spl4_65
  <=> v4_pre_topc(k9_subset_1(u1_struct_0(sK1),u1_struct_0(sK2),k2_struct_0(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f675,plain,
    ( v4_pre_topc(u1_struct_0(k2_tsep_1(sK0,sK2,sK1)),sK1)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_41
    | ~ spl4_65 ),
    inference(forward_demodulation,[],[f674,f331])).

fof(f331,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK2,sK1)) = k3_xboole_0(k2_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f330])).

fof(f674,plain,
    ( v4_pre_topc(k3_xboole_0(k2_struct_0(sK1),u1_struct_0(sK2)),sK1)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_65 ),
    inference(forward_demodulation,[],[f661,f80])).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f661,plain,
    ( v4_pre_topc(k3_xboole_0(u1_struct_0(sK2),k2_struct_0(sK1)),sK1)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_65 ),
    inference(superposition,[],[f470,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f470,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK1),u1_struct_0(sK2),k2_struct_0(sK1)),sK1)
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f469])).

fof(f657,plain,
    ( ~ spl4_95
    | spl4_94 ),
    inference(avatar_split_clause,[],[f655,f644,f649])).

fof(f649,plain,
    ( spl4_95
  <=> r1_tarski(k2_struct_0(sK1),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_95])])).

fof(f644,plain,
    ( spl4_94
  <=> m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f655,plain,
    ( ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(sK1))
    | spl4_94 ),
    inference(resolution,[],[f645,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f645,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))
    | spl4_94 ),
    inference(avatar_component_clause,[],[f644])).

fof(f653,plain,(
    spl4_95 ),
    inference(avatar_contradiction_clause,[],[f652])).

fof(f652,plain,
    ( $false
    | spl4_95 ),
    inference(resolution,[],[f650,f140])).

fof(f140,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f79,f78])).

fof(f78,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f650,plain,
    ( ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(sK1))
    | spl4_95 ),
    inference(avatar_component_clause,[],[f649])).

fof(f646,plain,
    ( ~ spl4_40
    | ~ spl4_94
    | spl4_87 ),
    inference(avatar_split_clause,[],[f634,f611,f644,f327])).

fof(f327,plain,
    ( spl4_40
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f634,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ l1_struct_0(sK1)
    | spl4_87 ),
    inference(superposition,[],[f612,f62])).

fof(f62,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f612,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl4_87 ),
    inference(avatar_component_clause,[],[f611])).

fof(f613,plain,
    ( ~ spl4_87
    | spl4_64 ),
    inference(avatar_split_clause,[],[f605,f466,f611])).

fof(f466,plain,
    ( spl4_64
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK1),u1_struct_0(sK2),k2_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f605,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl4_64 ),
    inference(resolution,[],[f467,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f467,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),u1_struct_0(sK2),k2_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl4_64 ),
    inference(avatar_component_clause,[],[f466])).

fof(f471,plain,
    ( ~ spl4_64
    | spl4_65
    | ~ spl4_7
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f455,f435,f117,f469,f466])).

fof(f435,plain,
    ( spl4_58
  <=> ! [X3] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X3),u1_struct_0(sK2),k2_struct_0(X3)),k1_zfmisc_1(u1_struct_0(X3)))
        | v4_pre_topc(k9_subset_1(u1_struct_0(X3),u1_struct_0(sK2),k2_struct_0(X3)),X3)
        | ~ m1_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f455,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK1),u1_struct_0(sK2),k2_struct_0(sK1)),sK1)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),u1_struct_0(sK2),k2_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_7
    | ~ spl4_58 ),
    inference(resolution,[],[f436,f118])).

fof(f436,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(X3),u1_struct_0(sK2),k2_struct_0(X3)),X3)
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(X3),u1_struct_0(sK2),k2_struct_0(X3)),k1_zfmisc_1(u1_struct_0(X3))) )
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f435])).

fof(f437,plain,
    ( spl4_58
    | ~ spl4_12
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f428,f166,f125,f163,f435])).

fof(f163,plain,
    ( spl4_12
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f166,plain,
    ( spl4_13
  <=> v4_pre_topc(u1_struct_0(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f428,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(X3),u1_struct_0(sK2),k2_struct_0(X3)),k1_zfmisc_1(u1_struct_0(X3)))
        | ~ m1_pre_topc(X3,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(X3),u1_struct_0(sK2),k2_struct_0(X3)),X3) )
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(resolution,[],[f385,f167])).

fof(f167,plain,
    ( v4_pre_topc(u1_struct_0(sK2),sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f166])).

fof(f385,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X0,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X1,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X0,k2_struct_0(X1)),X1) )
    | ~ spl4_9 ),
    inference(resolution,[],[f87,f126])).

fof(f126,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK3(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v4_pre_topc(sK3(X0,X1,X2),X0)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK3(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK3(X0,X1,X2),X0)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).

fof(f347,plain,
    ( ~ spl4_24
    | spl4_40 ),
    inference(avatar_split_clause,[],[f346,f327,f231])).

fof(f346,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_40 ),
    inference(resolution,[],[f328,f63])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f328,plain,
    ( ~ l1_struct_0(sK1)
    | spl4_40 ),
    inference(avatar_component_clause,[],[f327])).

fof(f332,plain,
    ( ~ spl4_40
    | spl4_41
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f320,f317,f330,f327])).

fof(f317,plain,
    ( spl4_39
  <=> u1_struct_0(k2_tsep_1(sK0,sK2,sK1)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f320,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK2,sK1)) = k3_xboole_0(k2_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_struct_0(sK1)
    | ~ spl4_39 ),
    inference(superposition,[],[f318,f62])).

fof(f318,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK2,sK1)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f317])).

fof(f319,plain,
    ( ~ spl4_7
    | spl4_39
    | ~ spl4_9
    | spl4_11
    | ~ spl4_4
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f315,f312,f105,f133,f125,f317,f117])).

fof(f312,plain,
    ( spl4_38
  <=> ! [X0] :
        ( u1_struct_0(k2_tsep_1(X0,sK2,sK1)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f315,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k2_tsep_1(sK0,sK2,sK1)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_4
    | ~ spl4_38 ),
    inference(resolution,[],[f313,f106])).

fof(f106,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f313,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | u1_struct_0(k2_tsep_1(X0,sK2,sK1)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ m1_pre_topc(sK1,X0) )
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f312])).

fof(f314,plain,
    ( spl4_6
    | spl4_8
    | spl4_38
    | spl4_3 ),
    inference(avatar_split_clause,[],[f310,f101,f312,f121,f113])).

fof(f113,plain,
    ( spl4_6
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f121,plain,
    ( spl4_8
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f101,plain,
    ( spl4_3
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f310,plain,
    ( ! [X0] :
        ( u1_struct_0(k2_tsep_1(X0,sK2,sK1)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl4_3 ),
    inference(forward_demodulation,[],[f309,f80])).

fof(f309,plain,
    ( ! [X0] :
        ( u1_struct_0(k2_tsep_1(X0,sK2,sK1)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl4_3 ),
    inference(resolution,[],[f139,f102])).

fof(f102,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f138,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f137,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f88,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f269,plain,
    ( spl4_6
    | spl4_8
    | spl4_30
    | spl4_3 ),
    inference(avatar_split_clause,[],[f265,f101,f267,f121,f113])).

fof(f265,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(X0,sK2,sK1),sK1)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl4_3 ),
    inference(resolution,[],[f71,f102])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                  & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tsep_1)).

fof(f239,plain,
    ( ~ spl4_9
    | ~ spl4_7
    | spl4_24 ),
    inference(avatar_split_clause,[],[f238,f231,f117,f125])).

fof(f238,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_7
    | spl4_24 ),
    inference(resolution,[],[f237,f118])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | spl4_24 ),
    inference(resolution,[],[f232,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f232,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_24 ),
    inference(avatar_component_clause,[],[f231])).

fof(f174,plain,
    ( ~ spl4_9
    | ~ spl4_4
    | spl4_12 ),
    inference(avatar_split_clause,[],[f170,f163,f105,f125])).

fof(f170,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_12 ),
    inference(resolution,[],[f164,f65])).

fof(f164,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f169,plain,
    ( ~ spl4_10
    | ~ spl4_9
    | ~ spl4_12
    | spl4_13
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f159,f109,f105,f166,f163,f125,f129])).

fof(f109,plain,
    ( spl4_5
  <=> v1_borsuk_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f159,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v4_pre_topc(u1_struct_0(sK2),sK0)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f92,f110])).

fof(f110,plain,
    ( v1_borsuk_1(sK2,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f135,plain,(
    ~ spl4_11 ),
    inference(avatar_split_clause,[],[f52,f133])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
      | ~ v1_borsuk_1(k2_tsep_1(sK0,sK2,sK1),sK1) )
    & ~ r1_tsep_1(sK2,sK1)
    & m1_pre_topc(sK2,sK0)
    & v1_borsuk_1(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                  | ~ v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1) )
                & ~ r1_tsep_1(X2,X1)
                & m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(k2_tsep_1(sK0,X2,X1),X1)
                | ~ v1_borsuk_1(k2_tsep_1(sK0,X2,X1),X1) )
              & ~ r1_tsep_1(X2,X1)
              & m1_pre_topc(X2,sK0)
              & v1_borsuk_1(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_pre_topc(k2_tsep_1(sK0,X2,X1),X1)
              | ~ v1_borsuk_1(k2_tsep_1(sK0,X2,X1),X1) )
            & ~ r1_tsep_1(X2,X1)
            & m1_pre_topc(X2,sK0)
            & v1_borsuk_1(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ m1_pre_topc(k2_tsep_1(sK0,X2,sK1),sK1)
            | ~ v1_borsuk_1(k2_tsep_1(sK0,X2,sK1),sK1) )
          & ~ r1_tsep_1(X2,sK1)
          & m1_pre_topc(X2,sK0)
          & v1_borsuk_1(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ( ~ m1_pre_topc(k2_tsep_1(sK0,X2,sK1),sK1)
          | ~ v1_borsuk_1(k2_tsep_1(sK0,X2,sK1),sK1) )
        & ~ r1_tsep_1(X2,sK1)
        & m1_pre_topc(X2,sK0)
        & v1_borsuk_1(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
        | ~ v1_borsuk_1(k2_tsep_1(sK0,sK2,sK1),sK1) )
      & ~ r1_tsep_1(sK2,sK1)
      & m1_pre_topc(sK2,sK0)
      & v1_borsuk_1(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                | ~ v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1) )
              & ~ r1_tsep_1(X2,X1)
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                | ~ v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1) )
              & ~ r1_tsep_1(X2,X1)
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X2,X1)
                 => ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                    & v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X2,X1)
               => ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                  & v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tmap_1)).

fof(f131,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f53,f129])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f127,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f54,f125])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f123,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f55,f121])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f119,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f56,f117])).

fof(f56,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f115,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f57,f113])).

fof(f57,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f111,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f58,f109])).

fof(f58,plain,(
    v1_borsuk_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f107,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f59,f105])).

fof(f59,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f103,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f60,f101])).

fof(f60,plain,(
    ~ r1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f99,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f61,f97,f94])).

fof(f61,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ v1_borsuk_1(k2_tsep_1(sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f44])).

%------------------------------------------------------------------------------
