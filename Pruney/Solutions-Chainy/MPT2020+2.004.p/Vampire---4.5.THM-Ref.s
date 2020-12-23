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
% DateTime   : Thu Dec  3 13:23:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 288 expanded)
%              Number of leaves         :   33 ( 139 expanded)
%              Depth                    :   10
%              Number of atoms          :  508 (1590 expanded)
%              Number of equality atoms :   36 ( 225 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f74,f78,f82,f87,f92,f98,f105,f116,f127,f134,f142,f155,f165,f171,f229,f232,f243])).

fof(f243,plain,
    ( ~ spl5_7
    | ~ spl5_10
    | spl5_9
    | ~ spl5_15
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f241,f169,f125,f85,f90,f76])).

fof(f76,plain,
    ( spl5_7
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f90,plain,
    ( spl5_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f85,plain,
    ( spl5_9
  <=> v1_tops_2(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f125,plain,
    ( spl5_15
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f169,plain,
    ( spl5_22
  <=> ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f241,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v1_tops_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ spl5_22 ),
    inference(resolution,[],[f170,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK4(X0,X1),X0)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(f170,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f169])).

fof(f232,plain,
    ( ~ spl5_7
    | ~ spl5_10
    | spl5_9
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f230,f227,f85,f90,f76])).

fof(f227,plain,
    ( spl5_29
  <=> v3_pre_topc(sK4(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f230,plain,
    ( v1_tops_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ spl5_29 ),
    inference(resolution,[],[f228,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK4(X0,X1),X0)
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f228,plain,
    ( v3_pre_topc(sK4(sK1,sK2),sK1)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f227])).

fof(f229,plain,
    ( ~ spl5_7
    | ~ spl5_10
    | spl5_9
    | spl5_29
    | ~ spl5_15
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f224,f163,f125,f227,f85,f90,f76])).

fof(f163,plain,
    ( spl5_21
  <=> ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | v3_pre_topc(sK4(sK1,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f224,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v3_pre_topc(sK4(sK1,sK2),sK1)
    | v1_tops_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ spl5_21 ),
    inference(resolution,[],[f164,f46])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | v3_pre_topc(sK4(sK1,sK2),X0) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f163])).

fof(f171,plain,
    ( ~ spl5_8
    | spl5_22
    | spl5_20 ),
    inference(avatar_split_clause,[],[f167,f160,f169,f80])).

fof(f80,plain,
    ( spl5_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f160,plain,
    ( spl5_20
  <=> m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | spl5_20 ),
    inference(resolution,[],[f161,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f161,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f160])).

fof(f165,plain,
    ( ~ spl5_8
    | ~ spl5_20
    | spl5_21
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f158,f122,f163,f160,f80])).

fof(f122,plain,
    ( spl5_14
  <=> v3_pre_topc(sK4(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(sK4(sK1,sK2),X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_14 ),
    inference(resolution,[],[f123,f50])).

fof(f50,plain,(
    ! [X2,X0,X3] :
      ( ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f123,plain,
    ( v3_pre_topc(sK4(sK1,sK2),sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f155,plain,
    ( ~ spl5_7
    | spl5_17 ),
    inference(avatar_split_clause,[],[f151,f140,f76])).

fof(f140,plain,
    ( spl5_17
  <=> m1_pre_topc(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f151,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_17 ),
    inference(resolution,[],[f141,f39])).

fof(f39,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f141,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f140])).

fof(f142,plain,
    ( ~ spl5_17
    | ~ spl5_7
    | ~ spl5_11
    | spl5_16 ),
    inference(avatar_split_clause,[],[f135,f131,f96,f76,f140])).

fof(f96,plain,
    ( spl5_11
  <=> ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f131,plain,
    ( spl5_16
  <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f135,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ spl5_11
    | spl5_16 ),
    inference(resolution,[],[f132,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X0,sK1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f96])).

fof(f132,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f131])).

fof(f134,plain,
    ( ~ spl5_8
    | ~ spl5_16
    | spl5_15 ),
    inference(avatar_split_clause,[],[f129,f125,f131,f80])).

fof(f129,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_15 ),
    inference(resolution,[],[f126,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f126,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f125])).

fof(f127,plain,
    ( ~ spl5_8
    | ~ spl5_2
    | spl5_14
    | ~ spl5_15
    | ~ spl5_6
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f117,f114,f72,f125,f122,f56,f80])).

fof(f56,plain,
    ( spl5_2
  <=> v1_tops_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f72,plain,
    ( spl5_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f114,plain,
    ( spl5_13
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | v3_pre_topc(sK4(sK1,sK2),X0)
        | ~ v1_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f117,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v3_pre_topc(sK4(sK1,sK2),sK0)
    | ~ v1_tops_2(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_6
    | ~ spl5_13 ),
    inference(resolution,[],[f115,f73])).

fof(f73,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_pre_topc(sK1,X0)
        | v3_pre_topc(sK4(sK1,sK2),X0)
        | ~ v1_tops_2(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( ~ spl5_7
    | ~ spl5_10
    | spl5_9
    | spl5_13
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f110,f103,f114,f85,f90,f76])).

fof(f103,plain,
    ( spl5_12
  <=> ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(sK4(sK1,sK2),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v1_tops_2(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v1_tops_2(sK2,X0)
        | v3_pre_topc(sK4(sK1,sK2),X0)
        | ~ m1_pre_topc(sK1,X0)
        | v1_tops_2(sK2,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | ~ l1_pre_topc(sK1) )
    | ~ spl5_12 ),
    inference(resolution,[],[f108,f46])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v1_tops_2(sK2,X0)
        | v3_pre_topc(sK4(sK1,sK2),X0)
        | ~ m1_pre_topc(X1,X0) )
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(sK4(sK1,sK2),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v1_tops_2(sK2,X0)
        | ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_12 ),
    inference(resolution,[],[f104,f43])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(sK4(sK1,sK2),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v1_tops_2(sK2,X0) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f103])).

fof(f105,plain,
    ( ~ spl5_7
    | ~ spl5_10
    | spl5_12
    | spl5_9 ),
    inference(avatar_split_clause,[],[f100,f85,f103,f90,f76])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | v3_pre_topc(sK4(sK1,sK2),X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | ~ l1_pre_topc(sK1) )
    | spl5_9 ),
    inference(resolution,[],[f99,f86])).

fof(f86,plain,
    ( ~ v1_tops_2(sK2,sK1)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v1_tops_2(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ l1_pre_topc(X2)
      | v3_pre_topc(sK4(X0,X1),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f45,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f98,plain,
    ( ~ spl5_7
    | spl5_11
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f93,f64,f96,f76])).

fof(f64,plain,
    ( spl5_4
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f93,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_4 ),
    inference(superposition,[],[f40,f65])).

fof(f65,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f92,plain,
    ( spl5_10
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f88,f68,f60,f90])).

fof(f60,plain,
    ( spl5_3
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f68,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f88,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(superposition,[],[f69,f61])).

fof(f61,plain,
    ( sK2 = sK3
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f69,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f87,plain,
    ( ~ spl5_9
    | spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f83,f60,f52,f85])).

fof(f52,plain,
    ( spl5_1
  <=> v1_tops_2(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

% (19231)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f83,plain,
    ( ~ v1_tops_2(sK2,sK1)
    | spl5_1
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f53,f61])).

fof(f53,plain,
    ( ~ v1_tops_2(sK3,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f82,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f31,f80])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ v1_tops_2(sK3,sK1)
    & v1_tops_2(sK2,sK0)
    & sK2 = sK3
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f24,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v1_tops_2(X3,X1)
                    & v1_tops_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
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

fof(f22,plain,
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

fof(f23,plain,
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

fof(f24,plain,
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

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X1)
                  & v1_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X1)
                  & v1_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v1_tops_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v1_tops_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_waybel_9)).

fof(f78,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f32,f76])).

fof(f32,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f33,f72])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f35,f64])).

fof(f35,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f36,f60])).

fof(f36,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f37,f56])).

fof(f37,plain,(
    v1_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f38,f52])).

fof(f38,plain,(
    ~ v1_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:30:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (19224)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (19232)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (19225)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (19221)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (19224)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f244,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f74,f78,f82,f87,f92,f98,f105,f116,f127,f134,f142,f155,f165,f171,f229,f232,f243])).
% 0.21/0.47  fof(f243,plain,(
% 0.21/0.47    ~spl5_7 | ~spl5_10 | spl5_9 | ~spl5_15 | ~spl5_22),
% 0.21/0.47    inference(avatar_split_clause,[],[f241,f169,f125,f85,f90,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl5_7 <=> l1_pre_topc(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl5_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    spl5_9 <=> v1_tops_2(sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    spl5_15 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.47  fof(f169,plain,(
% 0.21/0.47    spl5_22 <=> ! [X0] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.47  fof(f241,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK0) | v1_tops_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~spl5_22),
% 0.21/0.47    inference(resolution,[],[f170,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(rectify,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).
% 0.21/0.47  fof(f170,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f169])).
% 0.21/0.47  fof(f232,plain,(
% 0.21/0.47    ~spl5_7 | ~spl5_10 | spl5_9 | ~spl5_29),
% 0.21/0.47    inference(avatar_split_clause,[],[f230,f227,f85,f90,f76])).
% 0.21/0.47  fof(f227,plain,(
% 0.21/0.47    spl5_29 <=> v3_pre_topc(sK4(sK1,sK2),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.47  fof(f230,plain,(
% 0.21/0.47    v1_tops_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~spl5_29),
% 0.21/0.47    inference(resolution,[],[f228,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v3_pre_topc(sK4(X0,X1),X0) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f228,plain,(
% 0.21/0.47    v3_pre_topc(sK4(sK1,sK2),sK1) | ~spl5_29),
% 0.21/0.47    inference(avatar_component_clause,[],[f227])).
% 0.21/0.47  fof(f229,plain,(
% 0.21/0.47    ~spl5_7 | ~spl5_10 | spl5_9 | spl5_29 | ~spl5_15 | ~spl5_21),
% 0.21/0.47    inference(avatar_split_clause,[],[f224,f163,f125,f227,f85,f90,f76])).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    spl5_21 <=> ! [X0] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | v3_pre_topc(sK4(sK1,sK2),X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.47  fof(f224,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK0) | v3_pre_topc(sK4(sK1,sK2),sK1) | v1_tops_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~spl5_21),
% 0.21/0.47    inference(resolution,[],[f164,f46])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | v3_pre_topc(sK4(sK1,sK2),X0)) ) | ~spl5_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f163])).
% 0.21/0.47  fof(f171,plain,(
% 0.21/0.47    ~spl5_8 | spl5_22 | spl5_20),
% 0.21/0.47    inference(avatar_split_clause,[],[f167,f160,f169,f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl5_8 <=> l1_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    spl5_20 <=> m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | spl5_20),
% 0.21/0.47    inference(resolution,[],[f161,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f160])).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    ~spl5_8 | ~spl5_20 | spl5_21 | ~spl5_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f158,f122,f163,f160,f80])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    spl5_14 <=> v3_pre_topc(sK4(sK1,sK2),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK4(sK1,sK2),X0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl5_14),
% 0.21/0.47    inference(resolution,[],[f123,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X2,X0,X3] : (~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    v3_pre_topc(sK4(sK1,sK2),sK0) | ~spl5_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f122])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    ~spl5_7 | spl5_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f151,f140,f76])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    spl5_17 <=> m1_pre_topc(sK1,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    ~l1_pre_topc(sK1) | spl5_17),
% 0.21/0.47    inference(resolution,[],[f141,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK1) | spl5_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f140])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    ~spl5_17 | ~spl5_7 | ~spl5_11 | spl5_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f135,f131,f96,f76,f140])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl5_11 <=> ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    spl5_16 <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    ~l1_pre_topc(sK1) | ~m1_pre_topc(sK1,sK1) | (~spl5_11 | spl5_16)),
% 0.21/0.47    inference(resolution,[],[f132,f97])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,sK1)) ) | ~spl5_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f96])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl5_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f131])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ~spl5_8 | ~spl5_16 | spl5_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f129,f125,f131,f80])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | spl5_15),
% 0.21/0.47    inference(resolution,[],[f126,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK0) | spl5_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f125])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    ~spl5_8 | ~spl5_2 | spl5_14 | ~spl5_15 | ~spl5_6 | ~spl5_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f117,f114,f72,f125,f122,f56,f80])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl5_2 <=> v1_tops_2(sK2,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl5_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl5_13 <=> ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | v3_pre_topc(sK4(sK1,sK2),X0) | ~v1_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK0) | v3_pre_topc(sK4(sK1,sK2),sK0) | ~v1_tops_2(sK2,sK0) | ~l1_pre_topc(sK0) | (~spl5_6 | ~spl5_13)),
% 0.21/0.47    inference(resolution,[],[f115,f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl5_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f72])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(sK1,X0) | v3_pre_topc(sK4(sK1,sK2),X0) | ~v1_tops_2(sK2,X0) | ~l1_pre_topc(X0)) ) | ~spl5_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f114])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    ~spl5_7 | ~spl5_10 | spl5_9 | spl5_13 | ~spl5_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f110,f103,f114,f85,f90,f76])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl5_12 <=> ! [X0] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK4(sK1,sK2),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(sK2,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(sK2,X0) | v3_pre_topc(sK4(sK1,sK2),X0) | ~m1_pre_topc(sK1,X0) | v1_tops_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1)) ) | ~spl5_12),
% 0.21/0.47    inference(resolution,[],[f108,f46])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(sK2,X0) | v3_pre_topc(sK4(sK1,sK2),X0) | ~m1_pre_topc(X1,X0)) ) | ~spl5_12),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f107])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v3_pre_topc(sK4(sK1,sK2),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(sK2,X0) | ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl5_12),
% 0.21/0.47    inference(resolution,[],[f104,f43])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK4(sK1,sK2),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(sK2,X0)) ) | ~spl5_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f103])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ~spl5_7 | ~spl5_10 | spl5_12 | spl5_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f100,f85,f103,f90,f76])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v3_pre_topc(sK4(sK1,sK2),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1)) ) | spl5_9),
% 0.21/0.47    inference(resolution,[],[f99,f86])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ~v1_tops_2(sK2,sK1) | spl5_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f85])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_tops_2(X1,X0) | ~m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X2))) | ~v1_tops_2(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~l1_pre_topc(X2) | v3_pre_topc(sK4(X0,X1),X2) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(resolution,[],[f45,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ~spl5_7 | spl5_11 | ~spl5_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f93,f64,f96,f76])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl5_4 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X0)) ) | ~spl5_4),
% 0.21/0.47    inference(superposition,[],[f40,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~spl5_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f64])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl5_10 | ~spl5_3 | ~spl5_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f88,f68,f60,f90])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl5_3 <=> sK2 = sK3),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (~spl5_3 | ~spl5_5)),
% 0.21/0.47    inference(superposition,[],[f69,f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    sK2 = sK3 | ~spl5_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f60])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl5_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f68])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ~spl5_9 | spl5_1 | ~spl5_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f83,f60,f52,f85])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl5_1 <=> v1_tops_2(sK3,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  % (19231)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ~v1_tops_2(sK2,sK1) | (spl5_1 | ~spl5_3)),
% 0.21/0.47    inference(forward_demodulation,[],[f53,f61])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ~v1_tops_2(sK3,sK1) | spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f52])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl5_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f80])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    (((~v1_tops_2(sK3,sK1) & v1_tops_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f24,f23,f22,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X1) & v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X1) & v1_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X1) & v1_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v1_tops_2(X3,sK1) & v1_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ? [X2] : (? [X3] : (~v1_tops_2(X3,sK1) & v1_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X3] : (~v1_tops_2(X3,sK1) & v1_tops_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ? [X3] : (~v1_tops_2(X3,sK1) & v1_tops_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) => (~v1_tops_2(sK3,sK1) & v1_tops_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X1) & v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v1_tops_2(X3,X1) & (v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tops_2(X3,X1))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f8])).
% 0.21/0.47  fof(f8,conjecture,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tops_2(X3,X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_waybel_9)).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    spl5_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f76])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    l1_pre_topc(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    spl5_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f72])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    spl5_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f34,f68])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl5_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f35,f64])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    spl5_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f36,f60])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    sK2 = sK3),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f56])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    v1_tops_2(sK2,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ~spl5_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f52])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ~v1_tops_2(sK3,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (19224)------------------------------
% 0.21/0.47  % (19224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19224)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (19224)Memory used [KB]: 10746
% 0.21/0.47  % (19224)Time elapsed: 0.058 s
% 0.21/0.47  % (19224)------------------------------
% 0.21/0.47  % (19224)------------------------------
% 0.21/0.48  % (19217)Success in time 0.117 s
%------------------------------------------------------------------------------
