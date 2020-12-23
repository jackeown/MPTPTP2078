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
% DateTime   : Thu Dec  3 13:13:38 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 184 expanded)
%              Number of leaves         :   25 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  355 ( 771 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f143,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f55,f63,f67,f77,f84,f89,f99,f106,f124,f130,f136,f139,f142])).

fof(f142,plain,
    ( ~ spl4_4
    | spl4_13 ),
    inference(avatar_split_clause,[],[f140,f119,f61])).

fof(f61,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f119,plain,
    ( spl4_13
  <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f140,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_13 ),
    inference(resolution,[],[f120,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f44,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f120,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f139,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl4_16 ),
    inference(resolution,[],[f135,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f135,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_16
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f136,plain,
    ( ~ spl4_16
    | spl4_15 ),
    inference(avatar_split_clause,[],[f131,f128,f134])).

fof(f128,plain,
    ( spl4_15
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f131,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | spl4_15 ),
    inference(resolution,[],[f129,f69])).

fof(f69,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f41,f47])).

fof(f47,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f129,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f128])).

fof(f130,plain,
    ( ~ spl4_15
    | spl4_14 ),
    inference(avatar_split_clause,[],[f125,f122,f128])).

fof(f122,plain,
    ( spl4_14
  <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f125,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | spl4_14 ),
    inference(resolution,[],[f123,f72])).

fof(f123,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f124,plain,
    ( ~ spl4_13
    | ~ spl4_14
    | spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f108,f104,f75,f122,f119])).

fof(f75,plain,
    ( spl4_6
  <=> v2_tops_2(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f104,plain,
    ( spl4_10
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f108,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_6
    | ~ spl4_10 ),
    inference(resolution,[],[f105,f76])).

fof(f76,plain,
    ( ~ v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f105,plain,
    ( ! [X0] :
        ( v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f106,plain,
    ( ~ spl4_5
    | spl4_10
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f102,f97,f104,f65])).

fof(f65,plain,
    ( spl4_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f97,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_9 ),
    inference(resolution,[],[f98,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f14])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f99,plain,
    ( ~ spl4_5
    | spl4_9
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f95,f87,f97,f65])).

fof(f87,plain,
    ( spl4_8
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(sK0,X0),sK1)
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_8 ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_8 ),
    inference(resolution,[],[f91,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1)) )
    | ~ spl4_8 ),
    inference(resolution,[],[f88,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f88,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK0,X0),sK1)
        | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,
    ( ~ spl4_4
    | spl4_8
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f85,f82,f53,f87,f61])).

fof(f53,plain,
    ( spl4_2
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f82,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),sK1)
        | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(resolution,[],[f83,f54])).

fof(f54,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,
    ( ~ spl4_5
    | spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f79,f65,f82,f65])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_5 ),
    inference(resolution,[],[f78,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(sK3(X0,X1),X0)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_5 ),
    inference(resolution,[],[f36,f66])).

fof(f66,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v4_pre_topc(X3,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,
    ( ~ spl4_4
    | ~ spl4_6
    | spl4_1 ),
    inference(avatar_split_clause,[],[f70,f49,f75,f61])).

fof(f49,plain,
    ( spl4_1
  <=> v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f70,plain,
    ( ~ v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_1 ),
    inference(superposition,[],[f50,f45])).

fof(f50,plain,
    ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f67,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f30,f65])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v2_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v2_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v2_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
            & v2_tops_2(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
          & v2_tops_2(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v2_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v2_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v2_tops_2(X1,X0)
                 => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X1,X0)
               => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tops_2)).

fof(f63,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f33,f53])).

fof(f33,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f34,f49])).

fof(f34,plain,(
    ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n009.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 12:54:26 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.41  % (24172)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.41  % (24172)Refutation found. Thanks to Tanya!
% 0.19/0.41  % SZS status Theorem for theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f143,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(avatar_sat_refutation,[],[f51,f55,f63,f67,f77,f84,f89,f99,f106,f124,f130,f136,f139,f142])).
% 0.19/0.41  fof(f142,plain,(
% 0.19/0.41    ~spl4_4 | spl4_13),
% 0.19/0.41    inference(avatar_split_clause,[],[f140,f119,f61])).
% 0.19/0.41  fof(f61,plain,(
% 0.19/0.41    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.41  fof(f119,plain,(
% 0.19/0.41    spl4_13 <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.19/0.41  fof(f140,plain,(
% 0.19/0.41    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl4_13),
% 0.19/0.41    inference(resolution,[],[f120,f72])).
% 0.19/0.41  fof(f72,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.41    inference(duplicate_literal_removal,[],[f71])).
% 0.19/0.41  fof(f71,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.41    inference(superposition,[],[f44,f45])).
% 0.19/0.41  fof(f45,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f19])).
% 0.19/0.41  fof(f19,plain,(
% 0.19/0.41    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.19/0.41  fof(f44,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f18])).
% 0.19/0.41  fof(f18,plain,(
% 0.19/0.41    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 0.19/0.41  fof(f120,plain,(
% 0.19/0.41    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl4_13),
% 0.19/0.41    inference(avatar_component_clause,[],[f119])).
% 0.19/0.41  fof(f139,plain,(
% 0.19/0.41    spl4_16),
% 0.19/0.41    inference(avatar_contradiction_clause,[],[f137])).
% 0.19/0.41  fof(f137,plain,(
% 0.19/0.41    $false | spl4_16),
% 0.19/0.41    inference(resolution,[],[f135,f35])).
% 0.19/0.41  fof(f35,plain,(
% 0.19/0.41    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f4])).
% 0.19/0.41  fof(f4,axiom,(
% 0.19/0.41    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.19/0.41  fof(f135,plain,(
% 0.19/0.41    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) | spl4_16),
% 0.19/0.41    inference(avatar_component_clause,[],[f134])).
% 0.19/0.42  fof(f134,plain,(
% 0.19/0.42    spl4_16 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.19/0.42  fof(f136,plain,(
% 0.19/0.42    ~spl4_16 | spl4_15),
% 0.19/0.42    inference(avatar_split_clause,[],[f131,f128,f134])).
% 0.19/0.42  fof(f128,plain,(
% 0.19/0.42    spl4_15 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.19/0.42  fof(f131,plain,(
% 0.19/0.42    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) | spl4_15),
% 0.19/0.42    inference(resolution,[],[f129,f69])).
% 0.19/0.42  fof(f69,plain,(
% 0.19/0.42    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.42    inference(duplicate_literal_removal,[],[f68])).
% 0.19/0.42  fof(f68,plain,(
% 0.19/0.42    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.42    inference(superposition,[],[f41,f47])).
% 0.19/0.42  fof(f47,plain,(
% 0.19/0.42    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.42    inference(equality_resolution,[],[f43])).
% 0.19/0.42  fof(f43,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f17])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.42    inference(ennf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,axiom,(
% 0.19/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f16])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.42    inference(ennf_transformation,[],[f6])).
% 0.19/0.42  fof(f6,axiom,(
% 0.19/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.19/0.42  fof(f129,plain,(
% 0.19/0.42    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | spl4_15),
% 0.19/0.42    inference(avatar_component_clause,[],[f128])).
% 0.19/0.42  fof(f130,plain,(
% 0.19/0.42    ~spl4_15 | spl4_14),
% 0.19/0.42    inference(avatar_split_clause,[],[f125,f122,f128])).
% 0.19/0.42  fof(f122,plain,(
% 0.19/0.42    spl4_14 <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.19/0.42  fof(f125,plain,(
% 0.19/0.42    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | spl4_14),
% 0.19/0.42    inference(resolution,[],[f123,f72])).
% 0.19/0.42  fof(f123,plain,(
% 0.19/0.42    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) | spl4_14),
% 0.19/0.42    inference(avatar_component_clause,[],[f122])).
% 0.19/0.42  fof(f124,plain,(
% 0.19/0.42    ~spl4_13 | ~spl4_14 | spl4_6 | ~spl4_10),
% 0.19/0.42    inference(avatar_split_clause,[],[f108,f104,f75,f122,f119])).
% 0.19/0.42  fof(f75,plain,(
% 0.19/0.42    spl4_6 <=> v2_tops_2(k4_xboole_0(sK1,sK2),sK0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.19/0.42  fof(f104,plain,(
% 0.19/0.42    spl4_10 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.19/0.42  fof(f108,plain,(
% 0.19/0.42    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (spl4_6 | ~spl4_10)),
% 0.19/0.42    inference(resolution,[],[f105,f76])).
% 0.19/0.42  fof(f76,plain,(
% 0.19/0.42    ~v2_tops_2(k4_xboole_0(sK1,sK2),sK0) | spl4_6),
% 0.19/0.42    inference(avatar_component_clause,[],[f75])).
% 0.19/0.42  fof(f105,plain,(
% 0.19/0.42    ( ! [X0] : (v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl4_10),
% 0.19/0.42    inference(avatar_component_clause,[],[f104])).
% 0.19/0.42  fof(f106,plain,(
% 0.19/0.42    ~spl4_5 | spl4_10 | ~spl4_9),
% 0.19/0.42    inference(avatar_split_clause,[],[f102,f97,f104,f65])).
% 0.19/0.42  fof(f65,plain,(
% 0.19/0.42    spl4_5 <=> l1_pre_topc(sK0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.42  fof(f97,plain,(
% 0.19/0.42    spl4_9 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~r2_hidden(sK3(sK0,X0),X1) | v2_tops_2(X0,sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.19/0.42  fof(f102,plain,(
% 0.19/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~l1_pre_topc(sK0)) ) | ~spl4_9),
% 0.19/0.42    inference(duplicate_literal_removal,[],[f100])).
% 0.19/0.42  fof(f100,plain,(
% 0.19/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | ~spl4_9),
% 0.19/0.42    inference(resolution,[],[f98,f38])).
% 0.19/0.42  fof(f38,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f29])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | (~v4_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f27,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.19/0.42    inference(rectify,[],[f26])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.19/0.42    inference(nnf_transformation,[],[f14])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.19/0.42    inference(flattening,[],[f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : ((v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f8])).
% 0.19/0.42  fof(f8,axiom,(
% 0.19/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))))))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).
% 0.19/0.42  fof(f98,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | ~spl4_9),
% 0.19/0.42    inference(avatar_component_clause,[],[f97])).
% 0.19/0.42  fof(f99,plain,(
% 0.19/0.42    ~spl4_5 | spl4_9 | ~spl4_8),
% 0.19/0.42    inference(avatar_split_clause,[],[f95,f87,f97,f65])).
% 0.19/0.42  fof(f87,plain,(
% 0.19/0.42    spl4_8 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK3(sK0,X0),sK1) | v2_tops_2(X0,sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.19/0.42  fof(f95,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~l1_pre_topc(sK0)) ) | ~spl4_8),
% 0.19/0.42    inference(duplicate_literal_removal,[],[f93])).
% 0.19/0.42  fof(f93,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | ~spl4_8),
% 0.19/0.42    inference(resolution,[],[f91,f37])).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f29])).
% 0.19/0.42  fof(f91,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1))) ) | ~spl4_8),
% 0.19/0.42    inference(resolution,[],[f88,f40])).
% 0.19/0.42  fof(f40,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f15])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.19/0.42  fof(f88,plain,(
% 0.19/0.42    ( ! [X0] : (~r2_hidden(sK3(sK0,X0),sK1) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0)) ) | ~spl4_8),
% 0.19/0.42    inference(avatar_component_clause,[],[f87])).
% 0.19/0.42  fof(f89,plain,(
% 0.19/0.42    ~spl4_4 | spl4_8 | ~spl4_2 | ~spl4_7),
% 0.19/0.42    inference(avatar_split_clause,[],[f85,f82,f53,f87,f61])).
% 0.19/0.42  fof(f53,plain,(
% 0.19/0.42    spl4_2 <=> v2_tops_2(sK1,sK0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.42  fof(f82,plain,(
% 0.19/0.42    spl4_7 <=> ! [X1,X0] : (~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~v2_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.19/0.42  fof(f85,plain,(
% 0.19/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),sK1) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl4_2 | ~spl4_7)),
% 0.19/0.42    inference(resolution,[],[f83,f54])).
% 0.19/0.42  fof(f54,plain,(
% 0.19/0.42    v2_tops_2(sK1,sK0) | ~spl4_2),
% 0.19/0.42    inference(avatar_component_clause,[],[f53])).
% 0.19/0.42  fof(f83,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~v2_tops_2(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl4_7),
% 0.19/0.42    inference(avatar_component_clause,[],[f82])).
% 0.19/0.42  fof(f84,plain,(
% 0.19/0.42    ~spl4_5 | spl4_7 | ~spl4_5),
% 0.19/0.42    inference(avatar_split_clause,[],[f79,f65,f82,f65])).
% 0.19/0.42  fof(f79,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK3(sK0,X0),X1) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | ~spl4_5),
% 0.19/0.42    inference(resolution,[],[f78,f39])).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~v4_pre_topc(sK3(X0,X1),X0) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f29])).
% 0.19/0.42  fof(f78,plain,(
% 0.19/0.42    ( ! [X0,X1] : (v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X0,X1)) ) | ~spl4_5),
% 0.19/0.42    inference(resolution,[],[f36,f66])).
% 0.19/0.42  fof(f66,plain,(
% 0.19/0.42    l1_pre_topc(sK0) | ~spl4_5),
% 0.19/0.42    inference(avatar_component_clause,[],[f65])).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v4_pre_topc(X3,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f29])).
% 0.19/0.42  fof(f77,plain,(
% 0.19/0.42    ~spl4_4 | ~spl4_6 | spl4_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f70,f49,f75,f61])).
% 0.19/0.42  fof(f49,plain,(
% 0.19/0.42    spl4_1 <=> v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.42  fof(f70,plain,(
% 0.19/0.42    ~v2_tops_2(k4_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl4_1),
% 0.19/0.42    inference(superposition,[],[f50,f45])).
% 0.19/0.42  fof(f50,plain,(
% 0.19/0.42    ~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl4_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f49])).
% 0.19/0.42  fof(f67,plain,(
% 0.19/0.42    spl4_5),
% 0.19/0.42    inference(avatar_split_clause,[],[f30,f65])).
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    l1_pre_topc(sK0)),
% 0.19/0.42    inference(cnf_transformation,[],[f25])).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    ((~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    ? [X1] : (? [X2] : (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    ? [X2] : (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.19/0.42    inference(flattening,[],[f11])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,negated_conjecture,(
% 0.19/0.42    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.19/0.42    inference(negated_conjecture,[],[f9])).
% 0.19/0.42  fof(f9,conjecture,(
% 0.19/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tops_2)).
% 0.19/0.42  fof(f63,plain,(
% 0.19/0.42    spl4_4),
% 0.19/0.42    inference(avatar_split_clause,[],[f31,f61])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.42    inference(cnf_transformation,[],[f25])).
% 0.19/0.42  fof(f55,plain,(
% 0.19/0.42    spl4_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f33,f53])).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    v2_tops_2(sK1,sK0)),
% 0.19/0.42    inference(cnf_transformation,[],[f25])).
% 0.19/0.42  fof(f51,plain,(
% 0.19/0.42    ~spl4_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f34,f49])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    ~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.19/0.42    inference(cnf_transformation,[],[f25])).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (24172)------------------------------
% 0.19/0.42  % (24172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (24172)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (24172)Memory used [KB]: 10746
% 0.19/0.42  % (24172)Time elapsed: 0.009 s
% 0.19/0.42  % (24172)------------------------------
% 0.19/0.42  % (24172)------------------------------
% 0.19/0.42  % (24165)Success in time 0.08 s
%------------------------------------------------------------------------------
