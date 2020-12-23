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
% DateTime   : Thu Dec  3 13:23:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 180 expanded)
%              Number of leaves         :   23 (  91 expanded)
%              Depth                    :    7
%              Number of atoms          :  292 (1026 expanded)
%              Number of equality atoms :   36 ( 225 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f38,f42,f46,f50,f54,f58,f62,f67,f72,f78,f84,f92,f97,f104,f115])).

fof(f115,plain,
    ( ~ spl4_7
    | spl4_15 ),
    inference(avatar_split_clause,[],[f112,f102,f56])).

fof(f56,plain,
    ( spl4_7
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f102,plain,
    ( spl4_15
  <=> m1_pre_topc(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f112,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_15 ),
    inference(resolution,[],[f103,f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f103,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f104,plain,
    ( ~ spl4_15
    | ~ spl4_7
    | ~ spl4_11
    | spl4_14 ),
    inference(avatar_split_clause,[],[f98,f95,f76,f56,f102])).

fof(f76,plain,
    ( spl4_11
  <=> ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f95,plain,
    ( spl4_14
  <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f98,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ spl4_11
    | spl4_14 ),
    inference(resolution,[],[f96,f77])).

fof(f77,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X0,sK1) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f96,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f95])).

fof(f97,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | ~ spl4_14
    | spl4_13 ),
    inference(avatar_split_clause,[],[f93,f88,f95,f60,f56])).

fof(f60,plain,
    ( spl4_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f88,plain,
    ( spl4_13
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f93,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | spl4_13 ),
    inference(resolution,[],[f89,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f89,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f88])).

fof(f92,plain,
    ( ~ spl4_13
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f85,f81,f52,f60,f36,f88])).

fof(f36,plain,
    ( spl4_2
  <=> v1_tops_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f52,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f81,plain,
    ( spl4_12
  <=> ! [X0] :
        ( ~ v1_tops_2(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_pre_topc(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f85,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_tops_2(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(resolution,[],[f82,f53])).

fof(f53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f82,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ v1_tops_2(sK2,X0)
        | ~ m1_pre_topc(sK1,X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f84,plain,
    ( spl4_12
    | ~ spl4_10
    | spl4_9 ),
    inference(avatar_split_clause,[],[f79,f65,f70,f81])).

fof(f70,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f65,plain,
    ( spl4_9
  <=> v1_tops_2(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | ~ v1_tops_2(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | spl4_9 ),
    inference(resolution,[],[f30,f66])).

fof(f66,plain,
    ( ~ v1_tops_2(sK2,sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f30,plain,(
    ! [X2,X0,X3] :
      ( v1_tops_2(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v1_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

fof(f78,plain,
    ( ~ spl4_7
    | spl4_11
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f73,f44,f76,f56])).

fof(f44,plain,
    ( spl4_4
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f73,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_4 ),
    inference(superposition,[],[f27,f45])).

fof(f45,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,
    ( spl4_10
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f68,f48,f40,f70])).

fof(f40,plain,
    ( spl4_3
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f48,plain,
    ( spl4_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f68,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(superposition,[],[f49,f41])).

fof(f41,plain,
    ( sK2 = sK3
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f49,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f67,plain,
    ( ~ spl4_9
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f63,f40,f32,f65])).

fof(f32,plain,
    ( spl4_1
  <=> v1_tops_2(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f63,plain,
    ( ~ v1_tops_2(sK2,sK1)
    | spl4_1
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f33,f41])).

fof(f33,plain,
    ( ~ v1_tops_2(sK3,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f62,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f18,f60])).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ v1_tops_2(sK3,sK1)
    & v1_tops_2(sK2,sK0)
    & sK2 = sK3
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v1_tops_2(X3,X1)
                    & v1_tops_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X1)
                  & v1_tops_2(X2,sK0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v1_tops_2(X3,X1)
                & v1_tops_2(X2,sK0)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v1_tops_2(X3,sK1)
              & v1_tops_2(X2,sK0)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v1_tops_2(X3,sK1)
            & v1_tops_2(X2,sK0)
            & X2 = X3
            & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X3] :
          ( ~ v1_tops_2(X3,sK1)
          & v1_tops_2(sK2,sK0)
          & sK2 = X3
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3] :
        ( ~ v1_tops_2(X3,sK1)
        & v1_tops_2(sK2,sK0)
        & sK2 = X3
        & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
   => ( ~ v1_tops_2(sK3,sK1)
      & v1_tops_2(sK2,sK0)
      & sK2 = sK3
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X1)
                  & v1_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X1)
                  & v1_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( v1_tops_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
                     => v1_tops_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( v1_tops_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
                   => v1_tops_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_waybel_9)).

fof(f58,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f19,f56])).

fof(f19,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f21,f48])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f23,f40])).

fof(f23,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f24,f36])).

fof(f24,plain,(
    v1_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f25,f32])).

fof(f25,plain,(
    ~ v1_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:36:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (29046)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.42  % (29046)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.43  % (29054)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f34,f38,f42,f46,f50,f54,f58,f62,f67,f72,f78,f84,f92,f97,f104,f115])).
% 0.20/0.43  fof(f115,plain,(
% 0.20/0.43    ~spl4_7 | spl4_15),
% 0.20/0.43    inference(avatar_split_clause,[],[f112,f102,f56])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    spl4_7 <=> l1_pre_topc(sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.43  fof(f102,plain,(
% 0.20/0.43    spl4_15 <=> m1_pre_topc(sK1,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.43  fof(f112,plain,(
% 0.20/0.43    ~l1_pre_topc(sK1) | spl4_15),
% 0.20/0.43    inference(resolution,[],[f103,f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.43  fof(f103,plain,(
% 0.20/0.43    ~m1_pre_topc(sK1,sK1) | spl4_15),
% 0.20/0.43    inference(avatar_component_clause,[],[f102])).
% 0.20/0.43  fof(f104,plain,(
% 0.20/0.43    ~spl4_15 | ~spl4_7 | ~spl4_11 | spl4_14),
% 0.20/0.43    inference(avatar_split_clause,[],[f98,f95,f76,f56,f102])).
% 0.20/0.43  fof(f76,plain,(
% 0.20/0.43    spl4_11 <=> ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.43  fof(f95,plain,(
% 0.20/0.43    spl4_14 <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.43  fof(f98,plain,(
% 0.20/0.43    ~l1_pre_topc(sK1) | ~m1_pre_topc(sK1,sK1) | (~spl4_11 | spl4_14)),
% 0.20/0.43    inference(resolution,[],[f96,f77])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,sK1)) ) | ~spl4_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f76])).
% 0.20/0.43  fof(f96,plain,(
% 0.20/0.43    ~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl4_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f95])).
% 0.20/0.43  fof(f97,plain,(
% 0.20/0.43    ~spl4_7 | ~spl4_8 | ~spl4_14 | spl4_13),
% 0.20/0.43    inference(avatar_split_clause,[],[f93,f88,f95,f60,f56])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    spl4_8 <=> l1_pre_topc(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    spl4_13 <=> m1_pre_topc(sK1,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.43  fof(f93,plain,(
% 0.20/0.43    ~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | spl4_13),
% 0.20/0.43    inference(resolution,[],[f89,f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(nnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    ~m1_pre_topc(sK1,sK0) | spl4_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f88])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    ~spl4_13 | ~spl4_2 | ~spl4_8 | ~spl4_6 | ~spl4_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f85,f81,f52,f60,f36,f88])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    spl4_2 <=> v1_tops_2(sK2,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    spl4_12 <=> ! [X0] : (~v1_tops_2(sK2,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(sK1,X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    ~l1_pre_topc(sK0) | ~v1_tops_2(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | (~spl4_6 | ~spl4_12)),
% 0.20/0.43    inference(resolution,[],[f82,f53])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl4_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f52])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tops_2(sK2,X0) | ~m1_pre_topc(sK1,X0)) ) | ~spl4_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f81])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    spl4_12 | ~spl4_10 | spl4_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f79,f65,f70,f81])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    spl4_9 <=> v1_tops_2(sK2,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~v1_tops_2(sK2,X0) | ~m1_pre_topc(sK1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | spl4_9),
% 0.20/0.43    inference(resolution,[],[f30,f66])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    ~v1_tops_2(sK2,sK1) | spl4_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f65])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X2,X0,X3] : (v1_tops_2(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.43    inference(equality_resolution,[],[f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(flattening,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    ~spl4_7 | spl4_11 | ~spl4_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f73,f44,f76,f56])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    spl4_4 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X0)) ) | ~spl4_4),
% 0.20/0.43    inference(superposition,[],[f27,f45])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~spl4_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f44])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    spl4_10 | ~spl4_3 | ~spl4_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f68,f48,f40,f70])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    spl4_3 <=> sK2 = sK3),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    spl4_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (~spl4_3 | ~spl4_5)),
% 0.20/0.43    inference(superposition,[],[f49,f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    sK2 = sK3 | ~spl4_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f40])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl4_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f48])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    ~spl4_9 | spl4_1 | ~spl4_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f63,f40,f32,f65])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    spl4_1 <=> v1_tops_2(sK3,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    ~v1_tops_2(sK2,sK1) | (spl4_1 | ~spl4_3)),
% 0.20/0.43    inference(forward_demodulation,[],[f33,f41])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ~v1_tops_2(sK3,sK1) | spl4_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f32])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    spl4_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f18,f60])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    l1_pre_topc(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    (((~v1_tops_2(sK3,sK1) & v1_tops_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14,f13,f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X1) & v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X1) & v1_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X1) & v1_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v1_tops_2(X3,sK1) & v1_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ? [X2] : (? [X3] : (~v1_tops_2(X3,sK1) & v1_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X3] : (~v1_tops_2(X3,sK1) & v1_tops_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ? [X3] : (~v1_tops_2(X3,sK1) & v1_tops_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) => (~v1_tops_2(sK3,sK1) & v1_tops_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X1) & v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.20/0.43    inference(flattening,[],[f6])).
% 0.20/0.43  fof(f6,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v1_tops_2(X3,X1) & (v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,negated_conjecture,(
% 0.20/0.43    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => v1_tops_2(X3,X1))))))),
% 0.20/0.43    inference(negated_conjecture,[],[f4])).
% 0.20/0.43  fof(f4,conjecture,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => v1_tops_2(X3,X1))))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_waybel_9)).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    spl4_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f19,f56])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    l1_pre_topc(sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    spl4_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f20,f52])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    spl4_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f21,f48])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    spl4_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f22,f44])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    spl4_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f23,f40])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    sK2 = sK3),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f36])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    v1_tops_2(sK2,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ~spl4_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f32])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ~v1_tops_2(sK3,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (29046)------------------------------
% 0.20/0.43  % (29046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (29046)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (29046)Memory used [KB]: 10618
% 0.20/0.43  % (29046)Time elapsed: 0.029 s
% 0.20/0.43  % (29046)------------------------------
% 0.20/0.43  % (29046)------------------------------
% 0.20/0.43  % (29039)Success in time 0.073 s
%------------------------------------------------------------------------------
