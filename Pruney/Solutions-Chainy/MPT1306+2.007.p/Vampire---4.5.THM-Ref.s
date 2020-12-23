%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 195 expanded)
%              Number of leaves         :   27 (  80 expanded)
%              Depth                    :   10
%              Number of atoms          :  365 ( 824 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f78,f87,f93,f103,f110,f128,f134,f140,f143,f146])).

fof(f146,plain,
    ( ~ spl4_4
    | spl4_13 ),
    inference(avatar_split_clause,[],[f144,f123,f64])).

fof(f64,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f123,plain,
    ( spl4_13
  <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f144,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_13 ),
    inference(resolution,[],[f124,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f46,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_subset_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_subset_1)).

fof(f124,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f143,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | spl4_16 ),
    inference(resolution,[],[f139,f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f139,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_16
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f140,plain,
    ( ~ spl4_16
    | spl4_15 ),
    inference(avatar_split_clause,[],[f135,f132,f138])).

fof(f132,plain,
    ( spl4_15
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f135,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | spl4_15 ),
    inference(resolution,[],[f133,f72])).

fof(f72,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f43,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f133,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,
    ( ~ spl4_15
    | spl4_14 ),
    inference(avatar_split_clause,[],[f129,f126,f132])).

fof(f126,plain,
    ( spl4_14
  <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f129,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | spl4_14 ),
    inference(resolution,[],[f127,f80])).

fof(f127,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK1))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f128,plain,
    ( ~ spl4_13
    | ~ spl4_14
    | spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f112,f108,f76,f126,f123])).

fof(f76,plain,
    ( spl4_6
  <=> v2_tops_2(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f108,plain,
    ( spl4_10
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f112,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_6
    | ~ spl4_10 ),
    inference(resolution,[],[f109,f77])).

fof(f77,plain,
    ( ~ v2_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f109,plain,
    ( ! [X0] :
        ( v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f110,plain,
    ( ~ spl4_5
    | spl4_10
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f106,f101,f108,f68])).

fof(f68,plain,
    ( spl4_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f101,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_9 ),
    inference(resolution,[],[f102,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK3(X0,X1),X0)
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,
    ( ~ spl4_5
    | spl4_9
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f99,f91,f101,f68])).

fof(f91,plain,
    ( spl4_8
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(sK0,X0),sK1)
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_8 ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_8 ),
    inference(resolution,[],[f95,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1)) )
    | ~ spl4_8 ),
    inference(resolution,[],[f92,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f92,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK0,X0),sK1)
        | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,
    ( ~ spl4_4
    | spl4_8
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f88,f85,f56,f91,f64])).

fof(f56,plain,
    ( spl4_2
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f85,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),sK1)
        | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(resolution,[],[f86,f57])).

fof(f57,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f87,plain,
    ( ~ spl4_5
    | spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f82,f68,f85,f68])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_5 ),
    inference(resolution,[],[f81,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(sK3(X0,X1),X0)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_5 ),
    inference(resolution,[],[f38,f69])).

fof(f69,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v4_pre_topc(X3,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,
    ( ~ spl4_3
    | ~ spl4_6
    | spl4_1 ),
    inference(avatar_split_clause,[],[f73,f52,f76,f60])).

fof(f60,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f52,plain,
    ( spl4_1
  <=> v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f73,plain,
    ( ~ v2_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_1 ),
    inference(superposition,[],[f53,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f53,plain,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f70,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f32,f68])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v2_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f26,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
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

fof(f26,plain,
    ( ? [X2] :
        ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v2_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v2_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v2_tops_2(X1,X0)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X1,X0)
               => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).

fof(f66,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f33,f64])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f34,f60])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f35,f56])).

fof(f35,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f36,f52])).

fof(f36,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (28600)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (28596)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (28598)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (28609)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (28607)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (28597)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (28614)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (28602)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.50  % (28599)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (28614)Refutation not found, incomplete strategy% (28614)------------------------------
% 0.20/0.50  % (28614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28600)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f78,f87,f93,f103,f110,f128,f134,f140,f143,f146])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    ~spl4_4 | spl4_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f144,f123,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    spl4_13 <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl4_13),
% 0.20/0.50    inference(resolution,[],[f124,f80])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(superposition,[],[f46,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_subset_1)).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_subset_1)).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl4_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f123])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    spl4_16),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f141])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    $false | spl4_16),
% 0.20/0.50    inference(resolution,[],[f139,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) | spl4_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f138])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    spl4_16 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    ~spl4_16 | spl4_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f135,f132,f138])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    spl4_15 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) | spl4_15),
% 0.20/0.50    inference(resolution,[],[f133,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.50    inference(superposition,[],[f43,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | spl4_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f132])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    ~spl4_15 | spl4_14),
% 0.20/0.50    inference(avatar_split_clause,[],[f129,f126,f132])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    spl4_14 <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | spl4_14),
% 0.20/0.50    inference(resolution,[],[f127,f80])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) | spl4_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f126])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    ~spl4_13 | ~spl4_14 | spl4_6 | ~spl4_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f112,f108,f76,f126,f123])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    spl4_6 <=> v2_tops_2(k3_xboole_0(sK1,sK2),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    spl4_10 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (spl4_6 | ~spl4_10)),
% 0.20/0.50    inference(resolution,[],[f109,f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ~v2_tops_2(k3_xboole_0(sK1,sK2),sK0) | spl4_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f76])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    ( ! [X0] : (v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl4_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f108])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    ~spl4_5 | spl4_10 | ~spl4_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f106,f101,f108,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    spl4_5 <=> l1_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    spl4_9 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~r2_hidden(sK3(sK0,X0),X1) | v2_tops_2(X0,sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~l1_pre_topc(sK0)) ) | ~spl4_9),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f104])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | ~spl4_9),
% 0.20/0.50    inference(resolution,[],[f102,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | (~v4_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(rectify,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : ((v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | ~spl4_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f101])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    ~spl4_5 | spl4_9 | ~spl4_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f99,f91,f101,f68])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    spl4_8 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK3(sK0,X0),sK1) | v2_tops_2(X0,sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~l1_pre_topc(sK0)) ) | ~spl4_8),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f97])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | ~spl4_8),
% 0.20/0.50    inference(resolution,[],[f95,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1))) ) | ~spl4_8),
% 0.20/0.50    inference(resolution,[],[f92,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK3(sK0,X0),sK1) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | ~spl4_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f91])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ~spl4_4 | spl4_8 | ~spl4_2 | ~spl4_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f88,f85,f56,f91,f64])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    spl4_2 <=> v2_tops_2(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    spl4_7 <=> ! [X1,X0] : (~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~v2_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),sK1) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl4_2 | ~spl4_7)),
% 0.20/0.50    inference(resolution,[],[f86,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    v2_tops_2(sK1,sK0) | ~spl4_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f56])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_tops_2(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl4_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f85])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    ~spl4_5 | spl4_7 | ~spl4_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f82,f68,f85,f68])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK3(sK0,X0),X1) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | ~spl4_5),
% 0.20/0.50    inference(resolution,[],[f81,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v4_pre_topc(sK3(X0,X1),X0) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X0,X1)) ) | ~spl4_5),
% 0.20/0.50    inference(resolution,[],[f38,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    l1_pre_topc(sK0) | ~spl4_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f68])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v4_pre_topc(X3,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ~spl4_3 | ~spl4_6 | spl4_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f73,f52,f76,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    spl4_1 <=> v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ~v2_tops_2(k3_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl4_1),
% 0.20/0.50    inference(superposition,[],[f53,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl4_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f52])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    spl4_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f32,f68])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f26,f25,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f10])).
% 0.20/0.50  fof(f10,conjecture,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f33,f64])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    spl4_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f34,f60])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f35,f56])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    v2_tops_2(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ~spl4_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f36,f52])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (28600)------------------------------
% 0.20/0.50  % (28600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28600)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (28600)Memory used [KB]: 10746
% 0.20/0.50  % (28600)Time elapsed: 0.075 s
% 0.20/0.50  % (28600)------------------------------
% 0.20/0.50  % (28600)------------------------------
% 0.20/0.50  % (28601)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (28594)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (28614)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (28614)Memory used [KB]: 10618
% 0.20/0.50  % (28614)Time elapsed: 0.091 s
% 0.20/0.50  % (28614)------------------------------
% 0.20/0.50  % (28614)------------------------------
% 0.20/0.50  % (28593)Success in time 0.143 s
%------------------------------------------------------------------------------
