%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1317+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:44 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 233 expanded)
%              Number of leaves         :   27 ( 113 expanded)
%              Depth                    :   10
%              Number of atoms          :  410 (1166 expanded)
%              Number of equality atoms :   20 ( 103 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f46,f50,f54,f58,f62,f66,f71,f76,f86,f90,f104,f108,f120,f125,f127,f132,f135])).

fof(f135,plain,
    ( ~ spl5_10
    | ~ spl5_9
    | spl5_8
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f133,f130,f69,f74,f80])).

fof(f80,plain,
    ( spl5_10
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f74,plain,
    ( spl5_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f69,plain,
    ( spl5_8
  <=> v2_tops_2(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f130,plain,
    ( spl5_18
  <=> v4_pre_topc(sK4(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f133,plain,
    ( v2_tops_2(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2)
    | ~ spl5_18 ),
    inference(resolution,[],[f131,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(sK4(X0,X1),X0)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK4(X0,X1),X0)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f131,plain,
    ( v4_pre_topc(sK4(sK2,sK1),sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( spl5_18
    | ~ spl5_13
    | ~ spl5_5
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f128,f118,f56,f100,f130])).

fof(f100,plain,
    ( spl5_13
  <=> m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f56,plain,
    ( spl5_5
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f118,plain,
    ( spl5_16
  <=> ! [X0] :
        ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | v4_pre_topc(sK4(sK2,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f128,plain,
    ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(sK4(sK2,sK1),sK2)
    | ~ spl5_5
    | ~ spl5_16 ),
    inference(resolution,[],[f119,f57])).

fof(f57,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(sK4(sK2,sK1),X0) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f118])).

fof(f127,plain,
    ( ~ spl5_13
    | ~ spl5_5
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f126,f123,f56,f100])).

fof(f123,plain,
    ( spl5_17
  <=> ! [X0] :
        ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f126,plain,
    ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl5_5
    | ~ spl5_17 ),
    inference(resolution,[],[f124,f57])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,
    ( ~ spl5_7
    | spl5_17
    | spl5_15 ),
    inference(avatar_split_clause,[],[f121,f115,f123,f64])).

fof(f64,plain,
    ( spl5_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f115,plain,
    ( spl5_15
  <=> m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | spl5_15 ),
    inference(resolution,[],[f116,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f116,plain,
    ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f115])).

fof(f120,plain,
    ( ~ spl5_7
    | ~ spl5_15
    | spl5_16
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f113,f97,f118,f115,f64])).

fof(f97,plain,
    ( spl5_12
  <=> v4_pre_topc(sK4(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(sK4(sK2,sK1),X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_12 ),
    inference(resolution,[],[f98,f38])).

fof(f38,plain,(
    ! [X2,X0,X3] :
      ( ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v4_pre_topc(X3,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

fof(f98,plain,
    ( v4_pre_topc(sK4(sK2,sK1),sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f108,plain,
    ( ~ spl5_10
    | ~ spl5_9
    | spl5_8
    | spl5_13 ),
    inference(avatar_split_clause,[],[f105,f100,f69,f74,f80])).

fof(f105,plain,
    ( v2_tops_2(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2)
    | spl5_13 ),
    inference(resolution,[],[f101,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f101,plain,
    ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f100])).

fof(f104,plain,
    ( spl5_12
    | ~ spl5_13
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f95,f84,f56,f64,f60,f52,f100,f97])).

fof(f52,plain,
    ( spl5_4
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f60,plain,
    ( spl5_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f84,plain,
    ( spl5_11
  <=> ! [X0] :
        ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(sK4(sK2,sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v2_tops_2(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f95,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_tops_2(sK1,sK0)
    | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(sK4(sK2,sK1),sK0)
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(resolution,[],[f93,f57])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v2_tops_2(sK1,X0)
        | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X1)))
        | v4_pre_topc(sK4(sK2,sK1),X0) )
    | ~ spl5_11 ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(sK4(sK2,sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v2_tops_2(sK1,X0)
        | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_11 ),
    inference(resolution,[],[f85,f32])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(sK4(sK2,sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v2_tops_2(sK1,X0) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f84])).

fof(f90,plain,
    ( ~ spl5_7
    | ~ spl5_5
    | spl5_10 ),
    inference(avatar_split_clause,[],[f88,f80,f56,f64])).

fof(f88,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_5
    | spl5_10 ),
    inference(resolution,[],[f87,f57])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | spl5_10 ),
    inference(resolution,[],[f81,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f81,plain,
    ( ~ l1_pre_topc(sK2)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f86,plain,
    ( ~ spl5_10
    | ~ spl5_9
    | spl5_11
    | spl5_8 ),
    inference(avatar_split_clause,[],[f78,f69,f84,f74,f80])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_tops_2(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | v4_pre_topc(sK4(sK2,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ l1_pre_topc(sK2) )
    | spl5_8 ),
    inference(resolution,[],[f77,f70])).

fof(f70,plain,
    ( ~ v2_tops_2(sK1,sK2)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v2_tops_2(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ l1_pre_topc(X2)
      | v4_pre_topc(sK4(X0,X1),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f34,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,
    ( spl5_9
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f72,f48,f44,f74])).

fof(f44,plain,
    ( spl5_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f48,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f72,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(superposition,[],[f49,f45])).

fof(f45,plain,
    ( sK1 = sK3
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f49,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f71,plain,
    ( ~ spl5_8
    | spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f67,f44,f40,f69])).

fof(f40,plain,
    ( spl5_1
  <=> v2_tops_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f67,plain,
    ( ~ v2_tops_2(sK1,sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f41,f45])).

fof(f41,plain,
    ( ~ v2_tops_2(sK3,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f66,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f24,f64])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v2_tops_2(sK3,sK2)
    & sK1 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & v2_tops_2(sK1,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f18,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tops_2(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
                & v2_tops_2(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,sK0)
              & m1_pre_topc(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tops_2(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
            & v2_tops_2(X1,sK0)
            & m1_pre_topc(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tops_2(X3,X2)
              & sK1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
          & v2_tops_2(sK1,sK0)
          & m1_pre_topc(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v2_tops_2(X3,X2)
            & sK1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
        & v2_tops_2(sK1,sK0)
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ~ v2_tops_2(X3,sK2)
          & sK1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & v2_tops_2(sK1,sK0)
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( ~ v2_tops_2(X3,sK2)
        & sK1 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ~ v2_tops_2(sK3,sK2)
      & sK1 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v2_tops_2(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                     => ( X1 = X3
                       => v2_tops_2(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v2_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v2_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tops_2)).

fof(f62,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f26,f56])).

fof(f26,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f27,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f28,f48])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f29,f44])).

fof(f29,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f30,f40])).

fof(f30,plain,(
    ~ v2_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
