%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 312 expanded)
%              Number of leaves         :   31 ( 146 expanded)
%              Depth                    :   13
%              Number of atoms          :  599 (2443 expanded)
%              Number of equality atoms :   32 (  56 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f472,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f74,f78,f82,f86,f90,f94,f98,f120,f136,f187,f199,f210,f446,f453,f469,f471])).

fof(f471,plain,
    ( spl4_12
    | ~ spl4_10
    | spl4_9
    | ~ spl4_8
    | spl4_5
    | ~ spl4_4
    | spl4_74 ),
    inference(avatar_split_clause,[],[f470,f467,f64,f68,f80,f84,f88,f96])).

fof(f96,plain,
    ( spl4_12
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f88,plain,
    ( spl4_10
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f84,plain,
    ( spl4_9
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f80,plain,
    ( spl4_8
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f68,plain,
    ( spl4_5
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f64,plain,
    ( spl4_4
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f467,plain,
    ( spl4_74
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f470,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_74 ),
    inference(resolution,[],[f468,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f468,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | spl4_74 ),
    inference(avatar_component_clause,[],[f467])).

fof(f469,plain,
    ( ~ spl4_74
    | ~ spl4_10
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_71 ),
    inference(avatar_split_clause,[],[f465,f450,f92,f72,f88,f467])).

fof(f72,plain,
    ( spl4_6
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f92,plain,
    ( spl4_11
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f450,plain,
    ( spl4_71
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f465,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl4_11
    | ~ spl4_71 ),
    inference(resolution,[],[f451,f93])).

fof(f93,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f451,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0) )
    | ~ spl4_71 ),
    inference(avatar_component_clause,[],[f450])).

fof(f453,plain,
    ( spl4_71
    | spl4_1
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f447,f444,f52,f450])).

fof(f52,plain,
    ( spl4_1
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f444,plain,
    ( spl4_70
  <=> r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f447,plain,
    ( ! [X0] :
        ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_70 ),
    inference(resolution,[],[f445,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f445,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f444])).

fof(f446,plain,
    ( spl4_7
    | spl4_9
    | ~ spl4_3
    | spl4_5
    | ~ spl4_2
    | spl4_70
    | ~ spl4_21
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f442,f208,f158,f444,f56,f68,f60,f84,f76])).

fof(f76,plain,
    ( spl4_7
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f60,plain,
    ( spl4_3
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f56,plain,
    ( spl4_2
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f158,plain,
    ( spl4_21
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f208,plain,
    ( spl4_28
  <=> u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f442,plain,
    ( ~ l1_pre_topc(sK2)
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ spl4_28 ),
    inference(duplicate_literal_removal,[],[f441])).

fof(f441,plain,
    ( ~ l1_pre_topc(sK2)
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl4_28 ),
    inference(resolution,[],[f304,f49])).

fof(f304,plain,
    ( ! [X7] :
        ( ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X7)
        | ~ l1_pre_topc(X7)
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X7)) )
    | ~ spl4_28 ),
    inference(superposition,[],[f102,f209])).

fof(f209,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f208])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f40,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f210,plain,
    ( spl4_28
    | spl4_9
    | ~ spl4_8
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f201,f185,f60,f80,f84,f208])).

fof(f185,plain,
    ( spl4_24
  <=> ! [X0] :
        ( u1_struct_0(k1_tsep_1(sK2,X0,sK3)) = u1_struct_0(k1_tsep_1(sK0,X0,sK3))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f201,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(resolution,[],[f186,f61])).

fof(f61,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k1_tsep_1(sK2,X0,sK3)) = u1_struct_0(k1_tsep_1(sK0,X0,sK3)) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f185])).

fof(f199,plain,
    ( ~ spl4_10
    | ~ spl4_6
    | spl4_21 ),
    inference(avatar_split_clause,[],[f198,f158,f72,f88])).

fof(f198,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_6
    | spl4_21 ),
    inference(resolution,[],[f197,f73])).

fof(f73,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | spl4_21 ),
    inference(resolution,[],[f159,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f159,plain,
    ( ~ l1_pre_topc(sK2)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f158])).

fof(f187,plain,
    ( ~ spl4_4
    | spl4_5
    | spl4_24
    | ~ spl4_2
    | ~ spl4_14
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f180,f134,f118,f56,f185,f68,f64])).

fof(f118,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f134,plain,
    ( spl4_16
  <=> ! [X3,X2] :
        ( ~ m1_pre_topc(X2,sK2)
        | ~ m1_pre_topc(X3,sK2)
        | v2_struct_0(X3)
        | k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) = u1_struct_0(k1_tsep_1(sK2,X2,X3))
        | v2_struct_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f180,plain,
    ( ! [X0] :
        ( u1_struct_0(k1_tsep_1(sK2,X0,sK3)) = u1_struct_0(k1_tsep_1(sK0,X0,sK3))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl4_2
    | ~ spl4_14
    | ~ spl4_16 ),
    inference(resolution,[],[f165,f57])).

fof(f57,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f165,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(X3,sK2)
        | u1_struct_0(k1_tsep_1(sK2,X2,X3)) = u1_struct_0(k1_tsep_1(sK0,X2,X3))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X2,sK0) )
    | ~ spl4_14
    | ~ spl4_16 ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,
    ( ! [X2,X3] :
        ( u1_struct_0(k1_tsep_1(sK2,X2,X3)) = u1_struct_0(k1_tsep_1(sK0,X2,X3))
        | ~ m1_pre_topc(X3,sK2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | v2_struct_0(X3) )
    | ~ spl4_14
    | ~ spl4_16 ),
    inference(superposition,[],[f135,f119])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f118])).

fof(f135,plain,
    ( ! [X2,X3] :
        ( k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) = u1_struct_0(k1_tsep_1(sK2,X2,X3))
        | ~ m1_pre_topc(X3,sK2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(X2) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f134])).

fof(f136,plain,
    ( spl4_7
    | spl4_16
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f124,f88,f72,f134,f76])).

fof(f124,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(X2)
        | k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) = u1_struct_0(k1_tsep_1(sK2,X2,X3))
        | v2_struct_0(sK2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK2) )
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(resolution,[],[f121,f73])).

fof(f121,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,X2)
        | v2_struct_0(X1)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(X2,X1,X0))
        | v2_struct_0(X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X2) )
    | ~ spl4_10 ),
    inference(resolution,[],[f115,f89])).

fof(f89,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f115,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ l1_pre_topc(X5)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | k2_xboole_0(u1_struct_0(X4),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X3,X4,X2))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X5)
      | ~ m1_pre_topc(X2,X3) ) ),
    inference(resolution,[],[f101,f39])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f100,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f99,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f50,f49])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f120,plain,
    ( spl4_12
    | spl4_14
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f114,f88,f118,f96])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0))
        | v2_struct_0(sK0) )
    | ~ spl4_10 ),
    inference(resolution,[],[f101,f89])).

fof(f98,plain,(
    ~ spl4_12 ),
    inference(avatar_split_clause,[],[f27,f96])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    & m1_pre_topc(sK3,sK2)
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f22,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                    & m1_pre_topc(X3,X2)
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2)
                & m1_pre_topc(X3,X2)
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2)
              & m1_pre_topc(X3,X2)
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2)
            & m1_pre_topc(X3,X2)
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2)
          & m1_pre_topc(X3,sK2)
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2)
        & m1_pre_topc(X3,sK2)
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
      & m1_pre_topc(sK3,sK2)
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( m1_pre_topc(X3,X2)
                        & m1_pre_topc(X1,X2) )
                     => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).

fof(f94,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f28,f92])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f90,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f29,f88])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f30,f84])).

fof(f30,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f82,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f31,f80])).

fof(f31,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f32,f76])).

fof(f32,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f33,f72])).

fof(f33,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f35,f64])).

fof(f35,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f36,f60])).

fof(f36,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f37,f56])).

fof(f37,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f38,f52])).

fof(f38,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:35:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (8238)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (8254)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (8245)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (8253)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (8257)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (8236)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (8242)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (8247)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (8243)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (8257)Refutation not found, incomplete strategy% (8257)------------------------------
% 0.21/0.50  % (8257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8237)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (8240)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (8257)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (8257)Memory used [KB]: 10618
% 0.21/0.50  % (8257)Time elapsed: 0.085 s
% 0.21/0.50  % (8257)------------------------------
% 0.21/0.50  % (8257)------------------------------
% 0.21/0.50  % (8239)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (8237)Refutation not found, incomplete strategy% (8237)------------------------------
% 0.21/0.50  % (8237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8237)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (8237)Memory used [KB]: 10618
% 0.21/0.50  % (8237)Time elapsed: 0.094 s
% 0.21/0.50  % (8237)------------------------------
% 0.21/0.50  % (8237)------------------------------
% 0.21/0.50  % (8252)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (8255)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (8250)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (8248)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (8246)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (8241)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (8256)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (8246)Refutation not found, incomplete strategy% (8246)------------------------------
% 0.21/0.52  % (8246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8246)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (8246)Memory used [KB]: 6396
% 0.21/0.52  % (8246)Time elapsed: 0.110 s
% 0.21/0.52  % (8246)------------------------------
% 0.21/0.52  % (8246)------------------------------
% 0.21/0.52  % (8249)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (8244)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.53  % (8242)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f472,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f74,f78,f82,f86,f90,f94,f98,f120,f136,f187,f199,f210,f446,f453,f469,f471])).
% 0.21/0.54  fof(f471,plain,(
% 0.21/0.54    spl4_12 | ~spl4_10 | spl4_9 | ~spl4_8 | spl4_5 | ~spl4_4 | spl4_74),
% 0.21/0.54    inference(avatar_split_clause,[],[f470,f467,f64,f68,f80,f84,f88,f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    spl4_12 <=> v2_struct_0(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    spl4_10 <=> l1_pre_topc(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    spl4_9 <=> v2_struct_0(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    spl4_8 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    spl4_5 <=> v2_struct_0(sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    spl4_4 <=> m1_pre_topc(sK3,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.54  fof(f467,plain,(
% 0.21/0.54    spl4_74 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 0.21/0.54  fof(f470,plain,(
% 0.21/0.54    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_74),
% 0.21/0.54    inference(resolution,[],[f468,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 0.21/0.54  fof(f468,plain,(
% 0.21/0.54    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | spl4_74),
% 0.21/0.54    inference(avatar_component_clause,[],[f467])).
% 0.21/0.54  fof(f469,plain,(
% 0.21/0.54    ~spl4_74 | ~spl4_10 | ~spl4_6 | ~spl4_11 | ~spl4_71),
% 0.21/0.54    inference(avatar_split_clause,[],[f465,f450,f92,f72,f88,f467])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    spl4_6 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    spl4_11 <=> v2_pre_topc(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.54  fof(f450,plain,(
% 0.21/0.54    spl4_71 <=> ! [X0] : (~m1_pre_topc(sK2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 0.21/0.54  fof(f465,plain,(
% 0.21/0.54    ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | (~spl4_11 | ~spl4_71)),
% 0.21/0.54    inference(resolution,[],[f451,f93])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    v2_pre_topc(sK0) | ~spl4_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f92])).
% 0.21/0.54  fof(f451,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0)) ) | ~spl4_71),
% 0.21/0.54    inference(avatar_component_clause,[],[f450])).
% 0.21/0.54  fof(f453,plain,(
% 0.21/0.54    spl4_71 | spl4_1 | ~spl4_70),
% 0.21/0.54    inference(avatar_split_clause,[],[f447,f444,f52,f450])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    spl4_1 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.54  fof(f444,plain,(
% 0.21/0.54    spl4_70 <=> r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 0.21/0.54  fof(f447,plain,(
% 0.21/0.54    ( ! [X0] : (m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl4_70),
% 0.21/0.54    inference(resolution,[],[f445,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.54  fof(f445,plain,(
% 0.21/0.54    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) | ~spl4_70),
% 0.21/0.54    inference(avatar_component_clause,[],[f444])).
% 0.21/0.54  fof(f446,plain,(
% 0.21/0.54    spl4_7 | spl4_9 | ~spl4_3 | spl4_5 | ~spl4_2 | spl4_70 | ~spl4_21 | ~spl4_28),
% 0.21/0.54    inference(avatar_split_clause,[],[f442,f208,f158,f444,f56,f68,f60,f84,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    spl4_7 <=> v2_struct_0(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    spl4_3 <=> m1_pre_topc(sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    spl4_2 <=> m1_pre_topc(sK3,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    spl4_21 <=> l1_pre_topc(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.54  fof(f208,plain,(
% 0.21/0.54    spl4_28 <=> u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.54  fof(f442,plain,(
% 0.21/0.54    ~l1_pre_topc(sK2) | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK1) | v2_struct_0(sK2) | ~spl4_28),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f441])).
% 0.21/0.54  fof(f441,plain,(
% 0.21/0.54    ~l1_pre_topc(sK2) | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~spl4_28),
% 0.21/0.54    inference(resolution,[],[f304,f49])).
% 0.21/0.54  fof(f304,plain,(
% 0.21/0.54    ( ! [X7] : (~m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),X7) | ~l1_pre_topc(X7) | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X7))) ) | ~spl4_28),
% 0.21/0.54    inference(superposition,[],[f102,f209])).
% 0.21/0.54  fof(f209,plain,(
% 0.21/0.54    u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~spl4_28),
% 0.21/0.54    inference(avatar_component_clause,[],[f208])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.21/0.54    inference(resolution,[],[f40,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.54  fof(f210,plain,(
% 0.21/0.54    spl4_28 | spl4_9 | ~spl4_8 | ~spl4_3 | ~spl4_24),
% 0.21/0.54    inference(avatar_split_clause,[],[f201,f185,f60,f80,f84,f208])).
% 0.21/0.54  fof(f185,plain,(
% 0.21/0.54    spl4_24 <=> ! [X0] : (u1_struct_0(k1_tsep_1(sK2,X0,sK3)) = u1_struct_0(k1_tsep_1(sK0,X0,sK3)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.54  fof(f201,plain,(
% 0.21/0.54    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) | (~spl4_3 | ~spl4_24)),
% 0.21/0.54    inference(resolution,[],[f186,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    m1_pre_topc(sK1,sK2) | ~spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f60])).
% 0.21/0.54  fof(f186,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | u1_struct_0(k1_tsep_1(sK2,X0,sK3)) = u1_struct_0(k1_tsep_1(sK0,X0,sK3))) ) | ~spl4_24),
% 0.21/0.54    inference(avatar_component_clause,[],[f185])).
% 0.21/0.54  fof(f199,plain,(
% 0.21/0.54    ~spl4_10 | ~spl4_6 | spl4_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f198,f158,f72,f88])).
% 0.21/0.54  fof(f198,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | (~spl4_6 | spl4_21)),
% 0.21/0.54    inference(resolution,[],[f197,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    m1_pre_topc(sK2,sK0) | ~spl4_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f72])).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | spl4_21),
% 0.21/0.54    inference(resolution,[],[f159,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    ~l1_pre_topc(sK2) | spl4_21),
% 0.21/0.54    inference(avatar_component_clause,[],[f158])).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    ~spl4_4 | spl4_5 | spl4_24 | ~spl4_2 | ~spl4_14 | ~spl4_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f180,f134,f118,f56,f185,f68,f64])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    spl4_14 <=> ! [X1,X0] : (~m1_pre_topc(X0,sK0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    spl4_16 <=> ! [X3,X2] : (~m1_pre_topc(X2,sK2) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) = u1_struct_0(k1_tsep_1(sK2,X2,X3)) | v2_struct_0(X2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    ( ! [X0] : (u1_struct_0(k1_tsep_1(sK2,X0,sK3)) = u1_struct_0(k1_tsep_1(sK0,X0,sK3)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(X0,sK0)) ) | (~spl4_2 | ~spl4_14 | ~spl4_16)),
% 0.21/0.54    inference(resolution,[],[f165,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    m1_pre_topc(sK3,sK2) | ~spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f56])).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~m1_pre_topc(X3,sK2) | u1_struct_0(k1_tsep_1(sK2,X2,X3)) = u1_struct_0(k1_tsep_1(sK0,X2,X3)) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X2,sK0)) ) | (~spl4_14 | ~spl4_16)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f162])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    ( ! [X2,X3] : (u1_struct_0(k1_tsep_1(sK2,X2,X3)) = u1_struct_0(k1_tsep_1(sK0,X2,X3)) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | v2_struct_0(X3)) ) | (~spl4_14 | ~spl4_16)),
% 0.21/0.54    inference(superposition,[],[f135,f119])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0)) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(X0)) ) | ~spl4_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f118])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) = u1_struct_0(k1_tsep_1(sK2,X2,X3)) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2)) ) | ~spl4_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f134])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    spl4_7 | spl4_16 | ~spl4_6 | ~spl4_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f124,f88,f72,f134,f76])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) = u1_struct_0(k1_tsep_1(sK2,X2,X3)) | v2_struct_0(sK2) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK2)) ) | (~spl4_6 | ~spl4_10)),
% 0.21/0.54    inference(resolution,[],[f121,f73])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(X2,X1,X0)) | v2_struct_0(X2) | v2_struct_0(X0) | ~m1_pre_topc(X0,X2)) ) | ~spl4_10),
% 0.21/0.54    inference(resolution,[],[f115,f89])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    l1_pre_topc(sK0) | ~spl4_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f88])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X4,X2,X5,X3] : (~l1_pre_topc(X5) | v2_struct_0(X2) | ~m1_pre_topc(X4,X3) | v2_struct_0(X4) | k2_xboole_0(u1_struct_0(X4),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X3,X4,X2)) | v2_struct_0(X3) | ~m1_pre_topc(X3,X5) | ~m1_pre_topc(X2,X3)) )),
% 0.21/0.54    inference(resolution,[],[f101,f39])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f100,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f99,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f50,f49])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    spl4_12 | spl4_14 | ~spl4_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f114,f88,f118,f96])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0)) | v2_struct_0(sK0)) ) | ~spl4_10),
% 0.21/0.54    inference(resolution,[],[f101,f89])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ~spl4_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f27,f96])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ~v2_struct_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f22,f21,f20,f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f7])).
% 0.21/0.54  fof(f7,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    spl4_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f28,f92])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    v2_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    spl4_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f29,f88])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    l1_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ~spl4_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f30,f84])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ~v2_struct_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    spl4_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f31,f80])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    m1_pre_topc(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ~spl4_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f32,f76])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ~v2_struct_0(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    spl4_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f33,f72])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    m1_pre_topc(sK2,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ~spl4_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f34,f68])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ~v2_struct_0(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f35,f64])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    m1_pre_topc(sK3,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f36,f60])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    m1_pre_topc(sK1,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f37,f56])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    m1_pre_topc(sK3,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ~spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f38,f52])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (8242)------------------------------
% 0.21/0.54  % (8242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8242)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (8242)Memory used [KB]: 11001
% 0.21/0.54  % (8242)Time elapsed: 0.124 s
% 0.21/0.54  % (8242)------------------------------
% 0.21/0.54  % (8242)------------------------------
% 0.21/0.54  % (8230)Success in time 0.181 s
%------------------------------------------------------------------------------
